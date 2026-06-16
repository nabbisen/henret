#!/usr/bin/env python3
"""RFC 080 — assemble release-verification.json from gate records + environment.

Invoked by `scripts/check.sh --release`:
    release_manifest.py <records.jsonl> <version> <tarball>

Produces the non-manual, hashed manifest (080-B) with gate-policy script
hashes (080-2). `git_dirty` ignores paths under release/ (080-4 exception:
generated release artifacts must not dirty the tree they certify). When not
in a git work tree the run is marked a local pre-check (authoritative
evidence comes from CI, 080-D).
"""
import datetime
import hashlib
import json
import os
import platform
import subprocess
import sys
from pathlib import Path

records_path, version, tarball = sys.argv[1], sys.argv[2], sys.argv[3]


def sha256_file(p):
    p = Path(p)
    if not p.exists():
        return None
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()


def git(*args):
    try:
        return subprocess.run(["git", *args], capture_output=True,
                              text=True, timeout=10)
    except Exception:
        return None


inside = git("rev-parse", "--is-inside-work-tree")
if inside and inside.returncode == 0 and inside.stdout.strip() == "true":
    commit = git("rev-parse", "HEAD").stdout.strip()
    st = git("status", "--porcelain").stdout.splitlines()
    # 080-4: generated release/ artifacts do not count as a dirty source tree.
    dirty = any(line.strip() and not line[3:].startswith("release/") for line in st)
    local_precheck = False
else:
    commit, dirty, local_precheck = None, False, True

gates = [json.loads(l) for l in Path(records_path).read_text().splitlines() if l.strip()]

POLICY = ["check.sh", "check_selftest.py", "axiom_audit.py", "doc_symbol_check.py",
          "doc_count_check.py", "rfc_metadata_check.py", "warning_budget.py"]
gate_policy = {
    s.replace(".", "_").replace("-", "_") + "_sha256": sha256_file("scripts/" + s)
    for s in POLICY
}

runner = "github-actions" if os.environ.get("GITHUB_ACTIONS") \
    else os.environ.get("RUNNER_NAME", "local")

manifest = {
    "manifest_schema": 1,
    "generated_by": "scripts/check.sh --release",
    "package": "henret",
    "version": version,
    "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "git_commit": commit,
    "git_dirty": dirty,
    "local_precheck": local_precheck,
    "tarball_sha256": sha256_file(tarball),
    "lake_manifest_sha256": sha256_file("lake-manifest.json"),
    "lean_toolchain_sha256": sha256_file("lean-toolchain"),
    "os": platform.platform(),
    "runner": runner,
    "gate_policy": gate_policy,
    "gates": gates,
    "runtime_package": {
        "included": False,
        "version_or_commit": None,
        "evidence": "out-of-tree; populated by RFC 081 evidence ledger",
    },
}
print(json.dumps(manifest, indent=2))
