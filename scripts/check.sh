#!/usr/bin/env bash
# Henret release gate (RFC 017).
# All five gates must pass before an archive is cut.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== gate 1/5: lake build (Lean-only core + demo) =="
lake build

echo "== gate 2/5: lake build HenretNative (optional native layer) =="
lake build HenretNative

echo "== gate 3/5: demo regression scenarios =="
lake exe henret-demo

echo "== gate 4/5: all examples compile =="
for f in examples/[0-9][0-9]_*.lean; do
  echo "  - $f"
  lake env lean "$f" > /dev/null
done

echo "== gate 5/5: axiom audit =="
CORE_AUDIT=$(mktemp /tmp/henret-audit-core-XXXX.lean)
cat > "$CORE_AUDIT" << 'LEAN'
import Henret
open Henret
#print axioms step_preserves_terminal
#print axioms step_invalid_unchanged
#print axioms run_preserves_owner
#print axioms reachable_wf
#print axioms step_clock_monotone
LEAN
CORE_OUT=$(lake env lean "$CORE_AUDIT")
echo "$CORE_OUT"
if echo "$CORE_OUT" | grep -qE "NativeDeque|sorryAx"; then
  echo "FAIL: core theorem depends on a project axiom or sorry"; exit 1
fi

NATIVE_AUDIT=$(mktemp /tmp/henret-audit-native-XXXX.lean)
cat > "$NATIVE_AUDIT" << 'LEAN'
import Henret.Native.DequeModel
import Henret.Native.Assumptions
open Henret.Native
#print axioms qRun_tracks
#print axioms drivePopB_complete
LEAN
NATIVE_OUT=$(lake env lean "$NATIVE_AUDIT")
echo "$NATIVE_OUT"
if echo "$NATIVE_OUT" | grep -qE "NativeDeque|sorryAx"; then
  echo "FAIL: pure native-layer theorem depends on a project axiom or sorry"; exit 1
fi

ASSUMED_AUDIT=$(mktemp /tmp/henret-audit-assumed-XXXX.lean)
cat > "$ASSUMED_AUDIT" << 'LEAN'
import Henret.Native.Assumptions
open Henret.Native
#print axioms nativeDequeModel_qRun_tracks
LEAN
ASSUMED_OUT=$(lake env lean "$ASSUMED_AUDIT")
echo "$ASSUMED_OUT"
for ax in toList_empty toList_push steal_val steal_rest pop_val pop_rest; do
  if ! echo "$ASSUMED_OUT" | grep -q "NativeDeque.$ax"; then
    echo "FAIL: native theorem missing expected axiom NativeDeque.$ax"; exit 1
  fi
done
if echo "$ASSUMED_OUT" | grep -q "sorryAx"; then
  echo "FAIL: sorry detected"; exit 1
fi
rm -f "$CORE_AUDIT" "$NATIVE_AUDIT" "$ASSUMED_AUDIT"

echo "== all gates green =="
