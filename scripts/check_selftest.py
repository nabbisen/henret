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
  6. RFC 103 active release-core selects validation, packaging, docs, explorer
  7. numeric and semantic gate IDs match the active versioned registry
"""
import re
import subprocess
import sys
from pathlib import Path

from gate_registry import ACTIVE_PROFILE, EVIDENCE_CAPABILITIES, PROFILES

ROOT = Path(__file__).resolve().parent.parent
errors = []


def err(msg):
    errors.append(msg)


CHECK_SH = (ROOT / "scripts" / "check.sh").read_text()
AUDIT_PY = (ROOT / "scripts" / "axiom_audit.py").read_text()

# 1. gate ids unique + semantic ids + names ---------------------------------
gates = re.findall(r'run_gate\s+(\d+)\s+"([^"]+)"\s+"([^"]+)"', CHECK_SH)
ids = [int(i) for i, _, _ in gates]
if not gates:
    err("no `run_gate <id> \"<evidence-id>\" \"<name>\"` declarations found")
dupes = sorted({i for i in ids if ids.count(i) > 1})
if dupes:
    err(f"duplicate gate id(s): {dupes}")
for i, evidence_id, n in gates:
    if not evidence_id.strip():
        err(f"gate {i} has an empty evidence id")
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
if not re.search(r'run_gate\s+\d+\s+"[^"]+"\s+"[^"]*warning', CHECK_SH, re.I):
    err("warning-budget gate is not wired in check.sh")

# 6. RFC 103 release-core composition ---------------------------------------
if not re.search(r'--release-core\)\s+CORE=1;\s+VALID=1;\s+PACKAGE=1', CHECK_SH):
    err("release-core does not select required executable validation + packaging")
if not re.search(r'run_gate\s+10\s+"docs\.mdbook"\s+"mdBook documentation integrity"', CHECK_SH):
    err("release-core exact-commit mdBook gate is not wired")
if not re.search(r'run_gate\s+11\s+"test\.explorer"\s+"bounded model explorer"', CHECK_SH):
    err("release-core bounded explorer gate is not wired")
if "HENRET_RELEASE_PROFILE=release-core-v3" not in CHECK_SH:
    err("release-core does not select the RFC 103 v3 profile")
if 'if [ "$status" != pass ] && [ "$advisory" = 0 ]' not in CHECK_SH:
    err("required timeout/failure is not fail-closed")

# 7. active registry matches executable declarations ------------------------
declared = {int(i): evidence_id for i, evidence_id, _ in gates}
registered = PROFILES[ACTIVE_PROFILE]["gates"]
if declared != registered:
    err(f"active gate-registry drift: declared={declared}; registered={registered}")
if set(registered.values()) != set(EVIDENCE_CAPABILITIES):
    err("active gate registry and evidence-capability map disagree")

for e in errors:
    print("SELFTEST FAIL:", e)
print(f"check_selftest: {len(gates)} gates, {len(allow)} allowlisted theorems, "
      f"{len(printed)} printed; {len(errors)} error(s)")
sys.exit(1 if errors else 0)
