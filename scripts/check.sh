#!/usr/bin/env bash
# Henret release gate (RFC 017).
# All five gates must pass before an archive is cut.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== gate 1/7: lake build (Lean-only core + demo) =="
lake build

echo "== gate 2/7: lake build HenretNative (optional native layer) =="
lake build HenretNative

echo "== gate 3/7: demo regression scenarios =="
lake exe henret-demo

echo "== gate 4/7: all examples compile =="
for f in examples/[0-9][0-9]_*.lean; do
  echo "  - $f"
  lake env lean "$f" > /dev/null
done

echo "== gate 5/7: strict axiom audit (RFC 020) =="
AUDIT=$(mktemp /tmp/henret-audit-XXXX.lean)
cat > "$AUDIT" << 'LEAN'
import Henret
import Henret.Native.DequeModel
import Henret.Native.Assumptions
open Henret Henret.Native
#print axioms step_preserves_terminal
#print axioms step_invalid_unchanged
#print axioms run_preserves_owner
#print axioms reachable_wf
#print axioms reachable_spawned_has_owner
#print axioms reachable_owner_has_mailbox
#print axioms step_clock_monotone
#print axioms receive_only_own
#print axioms reachable_runnable_is_queued
#print axioms reachable_queue_exact
#print axioms step_blocked_unchanged
#print axioms qRun_tracks
#print axioms driveStackB_complete
#print axioms nativeDequeModel_qRun_tracks
LEAN
lake env lean "$AUDIT" | python3 scripts/axiom_audit.py
rm -f "$AUDIT"

echo "== gate 6/7: documentation consistency (RFC 021) =="
if grep -rn "five scenarios\|rfcs/proposed/010\|RFC 010 (proposed)\|remains in proposed\|send_preserves_tasks\|receive_preserves_tasks\|\\\`send a m\\\`\|\\\`receive a\\\`\|five .#eval" \
     README.md docs/ examples/ CHANGELOG.md Henret/ Main.lean 2>/dev/null \
     | grep -v "\.lake" | grep -v "docs/reviews/" | grep -v "rfcs/done/" | grep -v "docs/handoff-"; then
  echo "FAIL: stale documentation phrase found"; exit 1
fi
echo "docs consistency ok"

echo "== gate 7/7: doc-symbol checker (RFC 026) =="
DOCSYM=$(mktemp /tmp/henret-docsym-XXXX.lean)
python3 scripts/doc_symbol_check.py > "$DOCSYM"
if ! lake env lean "$DOCSYM" > /dev/null 2>&1; then
  echo "FAIL: a backticked theorem name in docs does not resolve:"
  lake env lean "$DOCSYM" 2>&1 | grep "unknown" | head -10
  exit 1
fi
rm -f "$DOCSYM"
echo "doc symbols ok"

echo "== all gates green =="
