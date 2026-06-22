#!/usr/bin/env python3
"""RFC 080 — assemble release-verification.json from gate records + environment.

Invoked by `scripts/check.sh --release`:
    release_manifest.py <records.jsonl> <version> <tarball> [gate_run_md_path]

Produces the non-manual, hashed manifest (080-B) with gate-policy script
hashes (080-2). `git_dirty` ignores paths under release/ (080-4 exception:
generated release artifacts must not dirty the tree they certify). When not
in a git work tree the run is marked a local pre-check (authoritative
evidence comes from CI, 080-D).

RFC 095 additions (published, consumer-fetchable manifest):
- `source_archive` block (name, sha256, size_bytes) beside the legacy
  `tarball_sha256` (kept for compatibility; not removed at manifest_schema 1).
- When a GATE-RUN.md output path is given, this script *renders and writes* it
  from the core manifest, then binds it by hash in `human_summary`. GATE-RUN.md
  renders only the core fields, so adding `human_summary` afterwards cannot make
  it drift (no circular hash).
- Signing is intentionally absent; it will be an additive optional field in a
  future manifest_schema, so hash-only verification trusts the publication
  channel today (RFC 095 §D5).
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
gate_run_path = sys.argv[4] if len(sys.argv) > 4 else None


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
          "doc_count_check.py", "rfc_metadata_check.py", "forbidden_claim_check.py",
          "warning_budget.py", "helper_usage_check.py", "extract_model_docs.py",
          "extract_theorem_docs.py", "extract_rfc_index.py"]
gate_policy = {
    s.replace(".", "_").replace("-", "_") + "_sha256": sha256_file("scripts/" + s)
    for s in POLICY
}

runner = "github-actions" if os.environ.get("GITHUB_ACTIONS") \
    else os.environ.get("RUNNER_NAME", "local")

tarball_sha = sha256_file(tarball)
tarball_size = Path(tarball).stat().st_size if Path(tarball).exists() else None

manifest = {
    "manifest_schema": 1,
    "generated_by": "scripts/check.sh --release",
    "package": "henret",
    "version": version,
    "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "git_commit": commit,
    "git_dirty": dirty,
    "local_precheck": local_precheck,
    # RFC 095 §D2: named, sized source archive (consumer-friendly), beside the
    # legacy hash field which is retained for compatibility (RFC 095 §3.2).
    "tarball_sha256": tarball_sha,
    "source_archive": {
        "name": Path(tarball).name,
        "sha256": tarball_sha,
        "size_bytes": tarball_size,
    },
    "lake_manifest_sha256": sha256_file("lake-manifest.json"),
    "lean_toolchain_sha256": sha256_file("lean-toolchain"),
    "os": platform.platform(),
    "runner": runner,
    "gate_policy": gate_policy,
    "gates": gates,
    "runtime_package": {
        "included": False,
        "version_or_commit": None,
        "verified_by_this_tarball": False,
        "evidence_ledger": "docs/evidence-ledger.yaml",
        "evidence": "Out-of-tree sibling package; runtime claims carry "
                    "verified_by_this_tarball=false in the evidence ledger (RFC 081).",
    },
}


def render_gate_run(m):
    out = []
    out.append(f"# Henret release gate run - v{m['version']}\n")
    out.append(f"- generated_by: `{m['generated_by']}`")
    out.append(f"- timestamp_utc: {m['timestamp_utc']}")
    out.append(f"- git_commit: {m['git_commit']}  (dirty: {m['git_dirty']})")
    out.append(f"- tarball: `{m['source_archive']['name']}` "
               f"({m['source_archive']['size_bytes']} bytes)")
    out.append(f"- tarball_sha256: `{m['tarball_sha256']}`")
    out.append(f"- os: {m['os']}  runner: {m['runner']}\n")
    out.append("| id | gate | status | ms |")
    out.append("|----|------|--------|----|")
    for g in m["gates"]:
        out.append(f"| {g['id']} | {g['name']} | {g['status']} | {g['duration_ms']} |")
    return "\n".join(out) + "\n"


# RFC 095 §3.3: render GATE-RUN.md from the *core* manifest, then bind it by
# hash. human_summary is added AFTER rendering, so it never appears in the
# rendered file — the bound hash cannot become stale.
if gate_run_path:
    gr = Path(gate_run_path)
    gr.write_text(render_gate_run(manifest))
    manifest["human_summary"] = {"name": gr.name, "sha256": sha256_file(gr)}

print(json.dumps(manifest, indent=2))
