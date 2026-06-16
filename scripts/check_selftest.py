#!/usr/bin/env python3
"""RFC 080 — gate-suite self-test (gate stage 0).

Validates the gate suite's own internal consistency *before* the expensive
semantic gates run, so the suite cannot silently rot the way it did before
the v0.17.0 audit (a non-existent theorem in the audit input, an allowlist
~26 entries out of sync with the heredoc, examples broken for several RFCs).

Checks (080-C):
  1. every gate id appears exactly once and has a non-empty name
  2. the axiom-audit allowlist matches the `#print axioms` inputs exactly
  3. the doc-symbol check has a non-empty target/symbol set
  4. the stale-phrase / generated-doc consistency check has non-empty targets
  5. the warning-budget gate is wired
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
errors = []


def err(msg):
    errors.append(msg)


CHECK_SH = (ROOT / "scripts" / "check.sh").read_text()
AUDIT_PY = (ROOT / "scripts" / "axiom_audit.py").read_text()

# 1. gate ids unique + named -------------------------------------------------
gates = re.findall(r'run_gate\s+(\d+)\s+"([^"]+)"', CHECK_SH)
ids = [int(i) for i, _ in gates]
if not gates:
    err("no `run_gate <id> \"<name>\"` declarations found in check.sh")
dupes = sorted({i for i in ids if ids.count(i) > 1})
if dupes:
    err(f"duplicate gate id(s): {dupes}")
for i, n in gates:
    if not n.strip():
        err(f"gate {i} has an empty name")

# 2. axiom-audit allowlist == #print axioms inputs ---------------------------
# heredoc inputs: short/partial names -> last dotted component
printed = {m.split(".")[-1]
           for m in re.findall(r"#print axioms\s+([A-Za-z_][\w.]*)", CHECK_SH)}
# allowlist keys are dict entries `"Henret...":` (a trailing colon distinguishes
# them from NATIVE_SIX set members `"Henret...",`); skip commented lines.
allow = set()
for line in AUDIT_PY.splitlines():
    if line.lstrip().startswith("#"):
        continue
    m = re.search(r'"(Henret[^"]+)"\s*:', line)
    if m:
        allow.add(m.group(1).split(".")[-1])
if printed != allow:
    miss = sorted(allow - printed)
    extra = sorted(printed - allow)
    err(f"axiom-audit drift: allowlisted-but-not-printed={miss}; "
        f"printed-but-not-allowlisted={extra}")

# 3. doc-symbol check has a non-empty symbol set -----------------------------
r = subprocess.run([sys.executable, "scripts/doc_symbol_check.py"],
                   capture_output=True, text=True, cwd=ROOT)
if r.returncode != 0:
    err(f"doc_symbol_check.py failed to run: {r.stderr.strip()[:120]}")
elif (r.stdout.count("#check") + r.stdout.count("#print")) == 0:
    err("doc_symbol_check.py emitted no symbol checks (empty target set)")

# 4. stale-phrase / generated-doc consistency has non-empty targets ----------
for tgt in ("README.md", "docs", "Henret"):
    if not (ROOT / tgt).exists():
        err(f"doc-consistency target does not exist: {tgt}")
r = subprocess.run([sys.executable, "scripts/doc_count_check.py"],
                   capture_output=True, text=True, cwd=ROOT)
if "ground truth" not in r.stdout:
    err("doc_count_check.py did not compute a ground-truth count set")

# 5. warning-budget gate is wired --------------------------------------------
if not re.search(r'run_gate\s+\d+\s+"[^"]*warning', CHECK_SH, re.I):
    err("warning-budget gate is not wired in check.sh")

for e in errors:
    print("SELFTEST FAIL:", e)
print(f"check_selftest: {len(gates)} gates, {len(allow)} allowlisted theorems, "
      f"{len(printed)} printed; {len(errors)} error(s)")
sys.exit(1 if errors else 0)
