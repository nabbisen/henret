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
USE_RE = re.compile(r"^\s*-?\s*uses:\s*([^@\s]+)@([^\s#]+)", re.MULTILINE)
INSTALL_RE = re.compile(
    r"^\s*python3\s+scripts/install_ci_tool\.py\s+([a-z0-9_-]+)\s+--destination\b",
    re.MULTILINE)
DIRECT_DOWNLOAD_RE = re.compile(
    r"\b(?:curl|wget)\b|urllib\.request|urlopen\s*\(|requests\.(?:get|request)\s*\("
    r"|Invoke-WebRequest",
    re.IGNORECASE)


def validate_policy_shape(policy: object) -> list[str]:
    errors: list[str] = []
    if type(policy) is not dict or type(policy.get("schema")) is not int or \
            policy.get("schema") != 1:
        return ["policy root/schema must be object/schema 1"]
    if set(policy) != {"schema", "actions", "tools", "workflow_tools"}:
        errors.append("policy keys must be exactly schema/actions/tools/workflow_tools")
    actions = policy.get("actions")
    tools = policy.get("tools")
    workflow_tools = policy.get("workflow_tools")
    if type(actions) is not dict or type(tools) is not dict or type(workflow_tools) is not dict:
        return errors + ["policy actions, tools, and workflow_tools must be objects"]
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
    return errors


def validate(policy: object, workflow_texts: dict[str, str], metadata_text: str,
             toolchain_text: str) -> list[str]:
    errors = validate_policy_shape(policy)
    if errors:
        return errors
    actions = policy["actions"]
    tools = policy["tools"]
    workflow_tools = policy["workflow_tools"]

    observed_actions: set[str] = set()
    for filename, text in workflow_texts.items():
        if re.search(r"releases/latest|/latest/|releases/download/\$", text, re.I):
            errors.append(f"{filename} contains a movable latest/download reference")
        if DIRECT_DOWNLOAD_RE.search(text):
            errors.append(f"{filename} contains a direct download mechanism")
        for action, ref in USE_RE.findall(text):
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


def load_workflows() -> dict[str, str]:
    paths = sorted({*WORKFLOWS.glob("*.yml"), *WORKFLOWS.glob("*.yaml")})
    return {path.name: path.read_text() for path in paths}


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
    cases: list[tuple[object, dict[str, str], str, str]] = []

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
    movable_workflow[first] = movable_workflow[first].replace(
        policy["actions"]["actions/checkout"]["commit"], "v6")
    cases.append((policy, movable_workflow, metadata, toolchain))
    yaml_bypass = dict(workflows)
    yaml_bypass["bypass.yaml"] = "steps:\n  - uses: actions/checkout@v6\n"
    cases.append((policy, yaml_bypass, metadata, toolchain))
    direct_download = dict(workflows)
    direct_download["docs.yml"] += "\n      - run: curl https://example.com/tool-v1 | sh\n"
    cases.append((policy, direct_download, metadata, toolchain))
    cases.append((policy, workflows, metadata.replace(
        "https://github.com/nabbisen/henret", "https://example.com/placeholder"),
                  toolchain))
    cases.append((policy, workflows, metadata, "leanprover/lean4:v0.0.0\n"))
    failures += sum(not validate(p, w, m, t) for p, w, m, t in cases)

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

    print(f"ci-supply-chain-selftest: valid + {len(cases)} invalid policy/workflow "
          f"fixtures + checksum accept/reject; {failures} error(s)")
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
