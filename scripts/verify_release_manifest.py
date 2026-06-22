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

    verify_release_manifest.py <manifest.json> <tarball> [GATE-RUN.md]

Checks: tarball SHA-256 matches both `tarball_sha256` and `source_archive.sha256`;
`source_archive.size_bytes` matches the file; every gate record is `pass`; and,
when GATE-RUN.md is supplied and `human_summary` is present, its hash binds.

This is hash-only verification: it trusts the channel the manifest was fetched
over (RFC 095 §D5). Exit 0 on success, non-zero on any mismatch.
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()


def main() -> int:
    if not 3 <= len(sys.argv) <= 4:
        print(__doc__)
        return 2
    manifest_path = Path(sys.argv[1])
    tarball = Path(sys.argv[2])
    gate_run = Path(sys.argv[3]) if len(sys.argv) > 3 else None

    for p in (manifest_path, tarball):
        if not p.exists():
            print(f"verify: missing file: {p}", file=sys.stderr)
            return 2

    m = json.loads(manifest_path.read_text())
    errors: list[str] = []

    actual = sha256_file(tarball)
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
    # RFC 097: only required-criticality gates are release-blocking; advisory
    # gates (demo, exhaustive conformance) may be not-run in the ci-core profile.
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
