#!/usr/bin/env python3
"""RFC 097 — release-validation report (advisory executable evidence).

    validation_report.py <records.jsonl> <version> [gate_run_md_path]

Emitted by `check.sh --release-validation`. The demo (gate 2) and exhaustive
conformance (gate 4) executables are advisory regression evidence that cannot run
inside the CI-authoritative release-core budget; this report records their result
and per-gate timing separately, so the release manifest can reference it without
blocking sidecar publication on it. Hash-bound `GATE-RUN`-style summary when a
path is given (same non-circular pattern as the release manifest).
"""
import datetime
import hashlib
import json
import sys
from pathlib import Path

records_path, version = sys.argv[1], sys.argv[2]
gate_run_path = sys.argv[3] if len(sys.argv) > 3 else None


def sha256_file(p):
    p = Path(p)
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None


gates = [json.loads(l) for l in Path(records_path).read_text().splitlines() if l.strip()]
# Advisory executable gates this report is about (others, e.g. build, are setup).
ADVISORY = {2, 4}
advisory = [g for g in gates if g.get("id") in ADVISORY]
all_pass = all(g.get("status") == "pass" for g in advisory) if advisory else False

report = {
    "report_schema": 1,
    "kind": "release-validation",
    "package": "henret",
    "version": version,
    "generated_by": "scripts/check.sh --release-validation",
    "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "advisory_gates_passed": all_pass,
    "gates": gates,
}


def render(r):
    out = [f"# Henret release-validation report - v{r['version']}\n",
           f"- generated_by: `{r['generated_by']}`",
           f"- timestamp_utc: {r['timestamp_utc']}",
           f"- advisory_gates_passed: {r['advisory_gates_passed']}\n",
           "| id | gate | status | ms |", "|----|------|--------|----|"]
    for g in r["gates"]:
        out.append(f"| {g['id']} | {g['name']} | {g['status']} | {g['duration_ms']} |")
    out.append("\nThese are advisory executable-regression results (RFC 097); they "
               "are not release-blocking and do not by themselves constitute the "
               "RFC 095 sidecar.")
    return "\n".join(out) + "\n"


if gate_run_path:
    gr = Path(gate_run_path)
    gr.write_text(render(report))
    report["human_summary"] = {"name": gr.name, "sha256": sha256_file(gr)}

print(json.dumps(report, indent=2))
