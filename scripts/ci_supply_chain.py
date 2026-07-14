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
from pathlib import Path

from install_ci_tool import verify_digest

ROOT = Path(__file__).resolve().parent.parent
POLICY_PATH = ROOT / "ci" / "supply-chain.json"
WORKFLOWS = ROOT / ".github" / "workflows"
FULL_SHA_RE = re.compile(r"[0-9a-f]{40}\Z")
FULL_SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")
USE_RE = re.compile(r"^\s*-?\s*uses:\s*([^@\s]+)@([^\s#]+)", re.MULTILINE)


def validate(policy: object, workflow_texts: dict[str, str]) -> list[str]:
    errors: list[str] = []
    if type(policy) is not dict or policy.get("schema") != 1:
        return ["policy root/schema must be object/schema 1"]
    actions = policy.get("actions")
    tools = policy.get("tools")
    if type(actions) is not dict or type(tools) is not dict:
        return ["policy actions and tools must be objects"]
    for name, pin in actions.items():
        if type(pin) is not dict or FULL_SHA_RE.fullmatch(str(pin.get("commit", ""))) is None:
            errors.append(f"action {name} lacks a full lowercase commit SHA")
        if not isinstance(pin.get("version"), str) or not pin["version"].startswith("v"):
            errors.append(f"action {name} lacks a human-readable version")
    for name, pin in tools.items():
        if type(pin) is not dict:
            errors.append(f"tool {name} policy must be an object")
            continue
        version, url = pin.get("version"), pin.get("url")
        if not isinstance(version, str) or not isinstance(url, str) or version not in url:
            errors.append(f"tool {name} URL is not bound to its exact version")
        if "latest" in str(url).lower():
            errors.append(f"tool {name} URL uses latest")
        if FULL_SHA256_RE.fullmatch(str(pin.get("sha256", ""))) is None:
            errors.append(f"tool {name} lacks a full lowercase SHA-256")
        if not isinstance(pin.get("binary"), str) or "/" in pin.get("binary", ""):
            errors.append(f"tool {name} binary must be a simple filename")

    observed_actions: set[str] = set()
    joined = "\n".join(workflow_texts.values())
    for filename, text in workflow_texts.items():
        if re.search(r"releases/latest|/latest/|releases/download/\$", text, re.I):
            errors.append(f"{filename} contains a movable latest/download reference")
        for action, ref in USE_RE.findall(text):
            observed_actions.add(action)
            expected = actions.get(action)
            if expected is None:
                errors.append(f"{filename} uses unregistered action {action}")
            elif ref != expected.get("commit"):
                errors.append(f"{filename} action {action} is not pinned to policy commit")
    if observed_actions != set(actions):
        errors.append("policy/workflow action set mismatch: "
                      f"policy={sorted(actions)}, observed={sorted(observed_actions)}")
    for tool in tools:
        invocation = f"scripts/install_ci_tool.py {tool} "
        if invocation not in joined:
            errors.append(f"no workflow installs pinned tool {tool}")
    return errors


def load_workflows() -> dict[str, str]:
    return {path.name: path.read_text() for path in sorted(WORKFLOWS.glob("*.yml"))}


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
    tool_repositories = {"elan": "leanprover/elan", "mdbook": "rust-lang/mdBook"}
    for tool, repository in tool_repositories.items():
        latest = github_json(f"https://api.github.com/repos/{repository}/releases/latest")
        observed = latest["tag_name"]
        pinned = policy["tools"][tool]["version"]
        state = "current" if observed == pinned else "UPDATE"
        updates += observed != pinned
        print(f"{state}: {tool} {pinned} -> {observed}")
    if updates:
        print(f"ci-supply-chain-refresh: {updates} reviewed source update(s) required")
        return 1
    print("ci-supply-chain-refresh: all pins current")
    return 0


def self_test() -> int:
    policy = json.loads(POLICY_PATH.read_text())
    workflows = load_workflows()
    failures = int(bool(validate(policy, workflows)))
    cases: list[tuple[object, dict[str, str]]] = []

    bad_action = copy.deepcopy(policy)
    bad_action["actions"]["actions/checkout"]["commit"] = "v6"
    cases.append((bad_action, workflows))
    bad_tool_hash = copy.deepcopy(policy)
    bad_tool_hash["tools"]["elan"]["sha256"] = "0" * 63
    cases.append((bad_tool_hash, workflows))
    latest_tool = copy.deepcopy(policy)
    mdbook_version = latest_tool["tools"]["mdbook"]["version"]
    latest_tool["tools"]["mdbook"]["url"] = latest_tool["tools"]["mdbook"]["url"].replace(
        mdbook_version, "latest", 1)
    cases.append((latest_tool, workflows))
    movable_workflow = dict(workflows)
    first = next(iter(movable_workflow))
    movable_workflow[first] = movable_workflow[first].replace(
        policy["actions"]["actions/checkout"]["commit"], "v6")
    cases.append((policy, movable_workflow))
    failures += sum(not validate(p, w) for p, w in cases)

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
    errors = validate(policy, load_workflows())
    lakefile = (ROOT / "lakefile.lean").read_text()
    if "https://github.com/nabbisen/henret" not in lakefile or \
            re.search(r"placeholder|example\.com", lakefile, re.I):
        errors.append("lakefile repository metadata is missing or placeholder")
    for error in errors:
        print(f"ci-supply-chain: FAIL — {error}")
    if errors:
        return 1
    print("ci-supply-chain: action commits and downloaded-tool pins match policy")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
