#!/usr/bin/env python3
"""RFC 095 — verify a published release against its release-verification.json.

Two uses:

  * **Post-upload (release procedure, RFC 095 §3.1):** after publishing, a
    maintainer re-downloads the tarball + manifest from the release page and runs
    this to confirm the *published* bytes match the manifest — catching the
    "CI built the right file but the wrong one was uploaded" gap.

  * **Consumer (RFC 095 §D4):** a downstream consumer (iotakt / jemmet) fetches
    the tarball + manifest and runs this to anchor henret provenance at fetch
    time, without trusting an out-of-band CI log.

    verify_release_manifest.py [--require-current|--require-v2]
        <manifest.json> <tarball> [GATE-RUN.md]

Checks: tarball SHA-256 matches both `tarball_sha256` and `source_archive.sha256`;
`source_archive.size_bytes` matches the file; every gate record is `pass`; and,
when GATE-RUN.md is supplied and `human_summary` is present, its hash binds.

This is hash-only verification: it trusts the channel the manifest was fetched
over (RFC 095 §D5). Exit 0 on success, non-zero on any mismatch.
"""
from __future__ import annotations

import hashlib
import io
import json
import re
import copy
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

from gate_registry import (ACTIVE_PROFILE, PROFILES, V2_PROFILE, V2_REGISTRY,
                           V3_EXPLORER_PARAMETERS, V3_EXPLORER_RESULT, V3_PROFILE,
                           V4_PROFILE)
from explorer_result import strict_json_loads, validate_manifest_evidence
from ci_supply_chain import validate_policy_shape

FULL_SHA1_RE = re.compile(r"[0-9a-f]{40}\Z")
FULL_SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")
KNOWN_LEGACY_PROFILES = {"ci-core-v1", "full"}
RFC104_POLICY_HASH_KEY = "ci_supply_chain_json_sha256"
RFC104_SCRIPT_HASH_KEYS = {
    "ci_supply_chain_py_sha256", "install_ci_tool_py_sha256",
}
RFC104_ARCHIVE_FILES = {
    "ci/supply-chain.json": RFC104_POLICY_HASH_KEY,
    "scripts/ci_supply_chain.py": "ci_supply_chain_py_sha256",
    "scripts/install_ci_tool.py": "install_ci_tool_py_sha256",
}
HOSTED_CI_KEYS = {
    "repository", "run_id", "run_attempt", "ref", "sha", "workflow_ref",
    "workflow_sha", "runner_environment", "runner_name", "runner_os",
    "runner_arch", "image_os", "image_version",
}


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()


def gate_contract_errors(manifest: dict) -> list[str]:
    profile = manifest.get("release_profile")
    contract = PROFILES.get(profile)
    if contract is None:
        if profile in KNOWN_LEGACY_PROFILES:
            return []
        return [f"unknown release_profile {profile!r}"]
    errors = []
    registry = contract["registry"]
    expected_gates = contract["gates"]
    expected_ids = set(expected_gates)
    if manifest.get("gate_registry") != registry:
        errors.append(f"{profile} requires gate_registry {registry}")
    if manifest.get("required_gates_passed") is not True:
        errors.append(f"{profile} requires required_gates_passed=true")
    if manifest.get("git_dirty") is not False:
        errors.append(f"{profile} is not authoritative when git_dirty is not false")
    if manifest.get("local_precheck") is not False:
        errors.append(f"{profile} is not authoritative when local_precheck is not false")
    git_commit = manifest.get("git_commit")
    # This repository currently uses Git's SHA-1 object format. Do not accept
    # abbreviations or arbitrary provenance labels as an exact candidate commit.
    if not isinstance(git_commit, str) or FULL_SHA1_RE.fullmatch(git_commit) is None:
        errors.append(f"{profile} git_commit must be exactly 40 lowercase "
                      "hexadecimal characters")
    gates = manifest.get("gates", [])
    ids = [g.get("id") for g in gates]
    if any(type(gate_id) is not int for gate_id in ids):
        errors.append(f"{profile} gate IDs must be integers")
    integer_ids = {gate_id for gate_id in ids if type(gate_id) is int}
    if len(ids) != len(set(ids)):
        errors.append(f"{profile} contains duplicate gate IDs")
    missing, extra = sorted(expected_ids - integer_ids), sorted(integer_ids - expected_ids)
    if missing:
        errors.append(f"{profile} missing required gate IDs: {missing}")
    if extra:
        errors.append(f"{profile} has unexpected gate IDs: {extra}")
    for gate in gates:
        gate_id = gate.get("id")
        if gate_id in expected_ids:
            if gate.get("criticality") != "required":
                errors.append(f"{profile} gate {gate_id} is not required")
            if gate.get("status") != "pass":
                errors.append(f"{profile} gate {gate_id} did not pass")
            if profile in (V3_PROFILE, V4_PROFILE) and gate.get("evidence_id") != expected_gates[gate_id]:
                errors.append(f"{profile} gate {gate_id} evidence_id does not match registry")
    if profile in (V3_PROFILE, V4_PROFILE):
        explorer = next((g for g in gates if g.get("id") == 11), None)
        if explorer is not None:
            params = explorer.get("parameters")
            result = explorer.get("result")
            try:
                validate_manifest_evidence(params, result)
            except ValueError as exc:
                errors.append(f"{profile} explorer evidence invalid: {exc}")
            if type(explorer.get("duration_ms")) is not int or explorer["duration_ms"] < 0:
                errors.append(f"{profile} explorer duration_ms is missing or invalid")
            if FULL_SHA256_RE.fullmatch(str(explorer.get("stdout_sha256", ""))) is None:
                errors.append(f"{profile} explorer stdout_sha256 is missing or invalid")
    if profile == V4_PROFILE:
        supply_chain = manifest.get("supply_chain")
        if type(supply_chain) is not dict or "policy_sha256" not in supply_chain:
            errors.append(f"{profile} requires supply_chain evidence")
        else:
            policy = {key: value for key, value in supply_chain.items()
                      if key != "policy_sha256"}
            errors.extend(f"{profile} supply_chain invalid: {error}"
                          for error in validate_policy_shape(policy))
            policy_hash = supply_chain.get("policy_sha256")
            if FULL_SHA256_RE.fullmatch(str(policy_hash or "")) is None:
                errors.append(f"{profile} supply_chain policy_sha256 is invalid")
            gate_policy = manifest.get("gate_policy")
            if type(gate_policy) is not dict:
                errors.append(f"{profile} requires gate_policy evidence")
            else:
                if gate_policy.get(RFC104_POLICY_HASH_KEY) != policy_hash:
                    errors.append(f"{profile} supply-chain policy hashes disagree")
                for key in RFC104_SCRIPT_HASH_KEYS:
                    if FULL_SHA256_RE.fullmatch(str(gate_policy.get(key, ""))) is None:
                        errors.append(f"{profile} gate_policy missing or invalid {key}")
        hosted = manifest.get("hosted_ci")
        if type(hosted) is not dict or set(hosted) != HOSTED_CI_KEYS:
            errors.append(f"{profile} requires exact hosted_ci provenance")
        else:
            if any(not isinstance(hosted[key], str) or not hosted[key]
                   for key in HOSTED_CI_KEYS):
                errors.append(f"{profile} hosted_ci fields must be non-empty strings")
            if hosted.get("repository") != "nabbisen/henret":
                errors.append(f"{profile} hosted_ci repository is not nabbisen/henret")
            if not str(hosted.get("run_id", "")).isdigit() or \
                    not str(hosted.get("run_attempt", "")).isdigit():
                errors.append(f"{profile} hosted_ci run identity is invalid")
            if hosted.get("sha") != manifest.get("git_commit") or \
                    hosted.get("workflow_sha") != manifest.get("git_commit"):
                errors.append(f"{profile} hosted_ci commit identity disagrees")
            if ".github/workflows/ci.yml@" not in str(hosted.get("workflow_ref", "")):
                errors.append(f"{profile} hosted_ci workflow is not ci.yml")
            if hosted.get("runner_environment") != "github-hosted":
                errors.append(f"{profile} runner is not GitHub-hosted")
        if manifest.get("runner") != "github-actions":
            errors.append(f"{profile} requires runner=github-actions")
    return errors


def source_policy_errors(manifest: dict, tarball: Path) -> list[str]:
    """Bind RFC 104 policy and checker hashes to source-archive bytes."""
    if manifest.get("release_profile") != V4_PROFILE:
        return []
    errors: list[str] = []
    try:
        with tarfile.open(tarball, "r:gz") as archive:
            archived_bytes: dict[str, bytes] = {}
            for path in RFC104_ARCHIVE_FILES:
                members = [member for member in archive.getmembers()
                           if member.isfile() and
                           (member.name == path or member.name.endswith(f"/{path}"))]
                if len(members) != 1:
                    errors.append(f"source archive must contain exactly one {path}; "
                                  f"observed {len(members)}")
                    continue
                stream = archive.extractfile(members[0])
                if stream is None:
                    errors.append(f"source archive file is unreadable: {path}")
                    continue
                archived_bytes[path] = stream.read()
    except (OSError, tarfile.TarError) as exc:
        return [f"cannot inspect source archive supply-chain policy: {exc}"]
    if errors:
        return errors
    policy_bytes = archived_bytes["ci/supply-chain.json"]
    try:
        archived_policy = strict_json_loads(policy_bytes.decode())
    except (UnicodeDecodeError, ValueError) as exc:
        return [f"source archive supply-chain policy is invalid: {exc}"]
    supply_chain = manifest.get("supply_chain")
    if type(supply_chain) is not dict:
        return ["manifest supply_chain evidence is missing"]
    embedded_policy = {key: value for key, value in supply_chain.items()
                       if key != "policy_sha256"}
    if archived_policy != embedded_policy:
        errors.append("embedded supply-chain policy disagrees with source archive")
    archived_hash = hashlib.sha256(policy_bytes).hexdigest()
    if supply_chain.get("policy_sha256") != archived_hash:
        errors.append("supply_chain.policy_sha256 disagrees with source archive")
    gate_policy = manifest.get("gate_policy")
    if type(gate_policy) is not dict:
        errors.append("manifest gate_policy evidence is missing")
    else:
        for path, key in RFC104_ARCHIVE_FILES.items():
            observed = hashlib.sha256(archived_bytes[path]).hexdigest()
            if gate_policy.get(key) != observed:
                errors.append(f"gate_policy {key} disagrees with source archive {path}")
    return errors


def self_test() -> int:
    base = {"release_profile": V2_PROFILE, "gate_registry": V2_REGISTRY,
            "required_gates_passed": True, "git_dirty": False,
            "local_precheck": False, "git_commit": "a" * 40,
            "gates": [{"id": i, "criticality": "required", "status": "pass"}
                      for i in range(11)]}
    failures = int(bool(gate_contract_errors(base)))
    cases: list[dict] = []

    def changed(**fields) -> dict:
        return {**base, **fields}

    cases.append(changed(gates=[dict(g) for g in base["gates"][:-1]]))
    advisory = changed(gates=[dict(g) for g in base["gates"]])
    advisory["gates"][2]["criticality"] = "advisory"
    cases.append(advisory)
    timeout = changed(gates=[dict(g) for g in base["gates"]])
    timeout["gates"][4]["status"] = "timeout"
    cases.append(timeout)
    cases.append(changed(gate_registry="legacy"))
    cases.append(changed(gates=[dict(g) for g in base["gates"]] +
                         [dict(base["gates"][0])]))
    unexpected = [dict(g) for g in base["gates"]]
    unexpected[-1]["id"] = 11
    cases.append(changed(gates=unexpected))
    cases.append(changed(required_gates_passed=False))
    cases.append(changed(git_dirty=True))
    cases.append(changed(local_precheck=True))
    invalid_commits = ["", "abc123", "a" * 41, "g" * 40]
    cases.extend(changed(git_commit=value) for value in invalid_commits)
    failures += sum(not gate_contract_errors(case) for case in cases)

    legacy = {
        "release_profile": "ci-core-v1",
        "gate_registry": "rfc097-ci-core-v1",
        "required_gates_passed": True,
        "gates": [
            {"id": 0, "criticality": "required", "status": "pass"},
            {"id": 2, "criticality": "advisory",
             "status": "not_run_in_release_core"},
        ],
    }
    failures += int(bool(gate_contract_errors(legacy)))
    failures += int(not gate_contract_errors({"release_profile": "invented-profile"}))

    v3 = {
        **base,
        "release_profile": V3_PROFILE,
        "gate_registry": PROFILES[V3_PROFILE]["registry"],
        "gates": [
            {"id": i, "evidence_id": evidence_id, "criticality": "required",
             "status": "pass", "duration_ms": 1, "stdout_sha256": "b" * 64}
            for i, evidence_id in PROFILES[V3_PROFILE]["gates"].items()
        ],
    }
    v3["gates"][11]["parameters"] = copy.deepcopy(V3_EXPLORER_PARAMETERS)
    v3["gates"][11]["result"] = copy.deepcopy(V3_EXPLORER_RESULT)
    failures += int(bool(gate_contract_errors(v3)))
    v3_cases = []
    bad_evidence = {**v3, "gates": [dict(g) for g in v3["gates"]]}
    bad_evidence["gates"][11]["evidence_id"] = "test.renamed"
    v3_cases.append(bad_evidence)
    missing_parameters = {**v3, "gates": [dict(g) for g in v3["gates"]]}
    missing_parameters["gates"][11].pop("parameters")
    v3_cases.append(missing_parameters)
    shallow_parameters = {**v3, "gates": [dict(g) for g in v3["gates"]]}
    shallow_parameters["gates"][11]["parameters"] = {
        **V3_EXPLORER_PARAMETERS, "depth": 1,
    }
    v3_cases.append(shallow_parameters)
    missing_result = copy.deepcopy(v3)
    missing_result["gates"][11].pop("result")
    v3_cases.append(missing_result)
    false_result = copy.deepcopy(v3)
    false_result["gates"][11]["result"]["counterexample_found"] = False
    v3_cases.append(false_result)
    drift_result = copy.deepcopy(v3)
    drift_result["gates"][11]["result"]["depth"] = 1
    v3_cases.append(drift_result)
    numeric_boolean = copy.deepcopy(v3)
    numeric_boolean["gates"][11]["result"]["well_formed"] = 1
    v3_cases.append(numeric_boolean)
    boolean_integer = copy.deepcopy(v3)
    boolean_integer["gates"][11]["result"]["depth"] = True
    v3_cases.append(boolean_integer)
    boolean_gate_id = copy.deepcopy(v3)
    boolean_gate_id["gates"][1]["id"] = True
    v3_cases.append(boolean_gate_id)
    bad_hash = {**v3, "gates": [dict(g) for g in v3["gates"]]}
    bad_hash["gates"][11]["stdout_sha256"] = "not-a-hash"
    v3_cases.append(bad_hash)
    failures += sum(not gate_contract_errors(case) for case in v3_cases)

    policy_bytes = (Path(__file__).resolve().parent.parent / "ci" /
                    "supply-chain.json").read_bytes()
    script_bytes = {
        "scripts/ci_supply_chain.py": (Path(__file__).resolve().parent /
                                        "ci_supply_chain.py").read_bytes(),
        "scripts/install_ci_tool.py": (Path(__file__).resolve().parent /
                                        "install_ci_tool.py").read_bytes(),
    }
    policy = strict_json_loads(policy_bytes.decode())
    policy_hash = hashlib.sha256(policy_bytes).hexdigest()
    v4 = copy.deepcopy(v3)
    v4.update({
        "release_profile": V4_PROFILE,
        "gate_registry": PROFILES[V4_PROFILE]["registry"],
        "runner": "github-actions",
        "supply_chain": {"policy_sha256": policy_hash, **policy},
        "gate_policy": {
            RFC104_POLICY_HASH_KEY: policy_hash,
            "ci_supply_chain_py_sha256": hashlib.sha256(
                script_bytes["scripts/ci_supply_chain.py"]).hexdigest(),
            "install_ci_tool_py_sha256": hashlib.sha256(
                script_bytes["scripts/install_ci_tool.py"]).hexdigest(),
        },
        "hosted_ci": {
            "repository": "nabbisen/henret", "run_id": "123",
            "run_attempt": "1", "ref": "refs/heads/main", "sha": "a" * 40,
            "workflow_ref": "nabbisen/henret/.github/workflows/ci.yml@refs/heads/main",
            "workflow_sha": "a" * 40, "runner_environment": "github-hosted",
            "runner_name": "GitHub Actions 1", "runner_os": "Linux",
            "runner_arch": "X64", "image_os": "ubuntu24",
            "image_version": "20260701.1",
        },
    })
    failures += int(bool(gate_contract_errors(v4)))
    v4_cases: list[dict] = []
    missing_supply = copy.deepcopy(v4)
    missing_supply.pop("supply_chain")
    v4_cases.append(missing_supply)
    mismatch_hash = copy.deepcopy(v4)
    mismatch_hash["supply_chain"]["policy_sha256"] = "d" * 64
    v4_cases.append(mismatch_hash)
    mutated_action = copy.deepcopy(v4)
    mutated_action["supply_chain"]["actions"]["actions/checkout"]["commit"] = "d" * 40
    v4_cases.append(mutated_action)
    missing_script_hash = copy.deepcopy(v4)
    missing_script_hash["gate_policy"].pop("install_ci_tool_py_sha256")
    v4_cases.append(missing_script_hash)
    local_runner = copy.deepcopy(v4)
    local_runner["runner"] = "local"
    local_runner["local_precheck"] = True
    local_runner["hosted_ci"] = None
    v4_cases.append(local_runner)
    hosted_sha_drift = copy.deepcopy(v4)
    hosted_sha_drift["hosted_ci"]["sha"] = "d" * 40
    v4_cases.append(hosted_sha_drift)
    # A syntactically valid but changed action commit is rejected by the source
    # archive binding at the CLI boundary below, not by shape validation alone.
    failures += sum(not gate_contract_errors(case) for case in v4_cases
                    if case is not mutated_action)

    # Exercise the command-line boundary for exact-commit rejection and legacy
    # compatibility, not only the pure contract function.
    with tempfile.TemporaryDirectory(prefix="henret-release-verifier-") as td:
        root = Path(td)
        tarball = root / "henret-test.tar.gz"
        with tarfile.open(tarball, "w:gz") as archive:
            archive_files = {"ci/supply-chain.json": policy_bytes, **script_bytes}
            for path, data in archive_files.items():
                info = tarfile.TarInfo(f"henret-test/{path}")
                info.size = len(data)
                archive.addfile(info, io.BytesIO(data))
        archive_hash = sha256_file(tarball)

        def cli_manifest(m: dict) -> dict:
            return {
                **m,
                "package": "henret",
                "version": "0.0.0-test",
                "tarball_sha256": archive_hash,
                "source_archive": {
                    "name": tarball.name,
                    "sha256": archive_hash,
                    "size_bytes": tarball.stat().st_size,
                },
            }

        manifest_path = root / "manifest.json"

        def cli_returncode(m: dict, requirement: str | None = None) -> int:
            manifest_path.write_text(json.dumps(cli_manifest(m)))
            flag = [requirement] if requirement else []
            proc = subprocess.run(
                [sys.executable, str(Path(__file__).resolve()), *flag,
                 str(manifest_path), str(tarball)],
                capture_output=True, text=True, timeout=10,
            )
            return proc.returncode

        def raw_cli_returncode(raw: str) -> int:
            manifest_path.write_text(raw)
            proc = subprocess.run(
                [sys.executable, str(Path(__file__).resolve()),
                 str(manifest_path), str(tarball)],
                capture_output=True, text=True, timeout=10,
            )
            return proc.returncode

        failures += int(cli_returncode(base) != 0)
        failures += sum(cli_returncode(changed(git_commit=value)) == 0
                        for value in invalid_commits)
        failures += int(cli_returncode(legacy) != 0)
        failures += int(cli_returncode(legacy, "--require-v2") == 0)
        failures += int(cli_returncode(v3, "--require-current") == 0)
        failures += int(cli_returncode(v4, "--require-current") != 0)
        failures += int(cli_returncode(legacy, "--require-current") == 0)
        cli_v4_cases = [missing_supply, mismatch_hash, mutated_action,
                        missing_script_hash, local_runner]
        failures += sum(cli_returncode(case, "--require-current") == 0
                        for case in cli_v4_cases)
        raw_v3 = json.dumps(cli_manifest(v3), separators=(",", ":"))
        duplicate_result = raw_v3.replace(
            '"counterexample_found":true',
            '"counterexample_found":false,"counterexample_found":true')
        duplicate_manifest = raw_v3.replace(
            '"release_profile":"release-core-v3"',
            '"release_profile":"legacy","release_profile":"release-core-v3"')
        failures += int(raw_cli_returncode(duplicate_result) == 0)
        failures += int(raw_cli_returncode(duplicate_manifest) == 0)

    print(f"release-verifier-selftest: valid v2/v3/v4/legacy + "
          f"{len(cases)} invalid v2 + {len(v3_cases)} invalid v3 + "
          f"{len(v4_cases)} invalid v4 fixtures; 5 invalid v4 CLI cases; "
          f"4 malformed commit + 2 duplicate-key CLI cases; "
          f"{failures} error(s)")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    args = sys.argv[1:]
    require_v2 = "--require-v2" in args
    require_current = "--require-current" in args
    args = [arg for arg in args if arg not in ("--require-v2", "--require-current")]
    if not 2 <= len(args) <= 3:
        print(__doc__)
        return 2
    manifest_path = Path(args[0])
    tarball = Path(args[1])
    gate_run = Path(args[2]) if len(args) > 2 else None

    for p in (manifest_path, tarball):
        if not p.exists():
            print(f"verify: missing file: {p}", file=sys.stderr)
            return 2

    try:
        m = strict_json_loads(manifest_path.read_text())
    except (OSError, ValueError) as exc:
        print(f"verify: FAIL — invalid manifest JSON: {exc}", file=sys.stderr)
        return 1
    if type(m) is not dict:
        print("verify: FAIL — manifest root must be a JSON object", file=sys.stderr)
        return 1
    errors: list[str] = gate_contract_errors(m)
    if require_v2 and m.get("release_profile") != V2_PROFILE:
        errors.append(f"expected release_profile {V2_PROFILE}, observed "
                      f"{m.get('release_profile')!r}")
    if require_current and m.get("release_profile") != ACTIVE_PROFILE:
        errors.append(f"expected release_profile {ACTIVE_PROFILE}, observed "
                      f"{m.get('release_profile')!r}")

    actual = sha256_file(tarball)
    errors.extend(source_policy_errors(m, tarball))
    if actual != m.get("tarball_sha256"):
        errors.append(f"tarball_sha256 mismatch: file {actual} != manifest "
                      f"{m.get('tarball_sha256')}")
    sa = m.get("source_archive")
    if sa:
        if actual != sa.get("sha256"):
            errors.append("source_archive.sha256 mismatch")
        size = tarball.stat().st_size
        if sa.get("size_bytes") not in (None, size):
            errors.append(f"source_archive.size_bytes mismatch: file {size} != "
                          f"manifest {sa.get('size_bytes')}")

    gates = m.get("gates", [])
    if not gates:
        errors.append("manifest lists no gate records")
    # Legacy manifests retain criticality semantics; versioned release-core
    # profiles additionally require their exact registries above.
    required = [g for g in gates if g.get("criticality", "required") == "required"]
    for g in required:
        if g.get("status") != "pass":
            errors.append(f"required gate {g.get('id')} ({g.get('name')}) status="
                          f"{g.get('status')!r}")
    if m.get("required_gates_passed") is False:
        errors.append("manifest required_gates_passed is false")

    if gate_run is not None:
        hs = m.get("human_summary")
        if not gate_run.exists():
            errors.append(f"GATE-RUN file missing: {gate_run}")
        elif hs:
            if sha256_file(gate_run) != hs.get("sha256"):
                errors.append("human_summary.sha256 mismatch (GATE-RUN.md drifted)")

    if errors:
        for e in errors:
            print(f"verify: FAIL — {e}", file=sys.stderr)
        return 1

    print(f"verify: OK — {m.get('package')} v{m.get('version')} "
          f"[{m.get('release_profile','full')}]; tarball sha256 {actual[:16]}…; "
          f"{len(required)} required gates pass")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
