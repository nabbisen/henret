#!/usr/bin/env bash
# Henret release gate (RFC 017, extended through RFC 051).
# All gates must pass before an archive is cut.  This is the single
# command referenced by docs/release-checklist.md.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== gate 1/10: lake build (Lean-only core + demo) =="
lake build

echo "== gate 2/10: lake build HenretNative (optional native layer) =="
lake build HenretNative

echo "== gate 3/10: lake build HenretExplore (optional model checker) =="
lake build HenretExplore

echo "== gate 4/10: demo regression scenarios =="
lake exe henret-demo

echo "== gate 5/10: all examples compile =="
for f in examples/[0-9][0-9]_*.lean; do
  echo "  - $f"
  lake env lean "$f" > /dev/null
done

echo "== gate 6/10: golden-trace conformance (RFC 047) =="
lake exe henret-conformance

echo "== gate 7/10: strict axiom audit (RFC 020) =="
AUDIT=$(mktemp /tmp/henret-audit-XXXX.lean)
cat > "$AUDIT" << 'LEAN'
import Henret
import Henret.Native.DequeModel
import Henret.Native.Assumptions
open Henret Henret.Native Henret.Bridge
#print axioms step_preserves_terminal
#print axioms step_invalid_unchanged
#print axioms run_preserves_wf
#print axioms reachable_wf
#print axioms reachable_spawned_has_owner
#print axioms reachable_owner_has_mailbox
#print axioms step_clock_monotone
#print axioms receive_only_own
#print axioms reachable_runnable_is_queued
#print axioms reachable_queue_exact
#print axioms receive_empty_parks
#print axioms receive_blocked_parks
#print axioms reachable_waiters_exact
#print axioms reachable_waiter_actor_unique
#check @spawnChild_sets_parent
#check @spawnChild_queues_child
#check @step_preserves_parent
#check @reachable_parent_lt
#check @parent_chain_terminates
#print axioms reachable_parent_lt
#print axioms parent_chain_terminates
#print axioms qRun_tracks
#print axioms driveStackB_complete
#print axioms nativeDequeModel_qRun_tracks
-- RFC 036 bridge theorems (single-worker queue projection)
#print axioms bridge_step_single_worker
#print axioms bridge_run_tracks_single_worker
#print axioms bridge_run_general
#check @bridge_spawn
#check @bridge_spawnChild
#check @bridge_schedule
#check @bridge_cancel
#check @bridge_send
#check @bridge_inject
#check @bridge_tick
-- RFC 038 owner/parent exactness theorems
#print axioms reachable_owner_spawned
#print axioms reachable_parent_child_spawned
#check @spawnChild_child_spawned
#check @WellFormed.owner_spawned
#check @WellFormed.parent_child_spawned
-- RFC 039 cascade cancel theorems
#print axioms preserves_wf_cancelTree
#print axioms cancelTree_cancels_task
#print axioms cancelTree_preserves_task_state
#print axioms bridge_cancelTree
#check @cancelTree_cancels_root
#check @cancelTree_removes_from_readyQ
#check @descendantsOf_nodup
-- RFC 049 supervision restart policies
#print axioms reachable_restart_fresh
#print axioms reachable_restart_old_failed
#print axioms reachable_restart_parent_consistent
#print axioms restart_preserves_parent_acyclicity
#print axioms restarted_task_has_owner
#check @preserves_wf_fail
#check @preserves_wf_restartOne
#check @bridge_fail
#check @bridge_restartOne
-- RFC 054 semantic profile inclusion chain
#print axioms core_le_actor
#print axioms actor_le_full
#print axioms core_le_full
-- RFC 055 structured cancellation / shutdown
#print axioms closeActor_sets_closed
#print axioms closed_actor_rejects_send
#print axioms closed_actor_rejects_inject
#print axioms shutdown_rejects_spawn
#print axioms shutdown_sets_status
#print axioms stopWhenIdle_requires_quiescent
#print axioms stopWhenIdle_sets_stopped
#check @preserves_wf_closeActor
#check @preserves_wf_shutdown
#check @preserves_wf_stopWhenIdle
#check @bridge_closeActor
#check @bridge_shutdown
#check @bridge_stopWhenIdle
#check @closeActor_preserves_mailboxes
-- Coverage for the remaining allowlisted headline theorems
#print axioms reachable_occurrence_unique
#print axioms send_stamps_source
#print axioms inject_stamps_none
#print axioms Bridge.reachable_multi_bridge
#print axioms Bridge.single_bridge_implies_multi_bridge
#print axioms Conformance.conformance_suite_passes
#print axioms Progress.ready_eventually_scheduled_under_bounded_fairness
#print axioms Progress.schedule_schedules_head
#print axioms Progress.head_scheduled_within_one
#print axioms Progress.unfairOps_not_bounded_fair_0
#print axioms Trace.stepTrace_state_eq_step
#print axioms Trace.stepTrace_result_eq_step
#print axioms Trace.runTraceLedger_state_eq_run
#print axioms Trace.event_received_sound
#print axioms Trace.event_parked_sound
#print axioms Trace.event_timerWoke_sound
#print axioms Trace.event_spawnChild_sound
LEAN
lake env lean "$AUDIT" | python3 scripts/axiom_audit.py
rm -f "$AUDIT"

echo "== gate 8/10: documentation consistency (RFC 021 + RFC 037) =="
if grep -rn "five scenarios\|rfcs/proposed/010\|RFC 010 (proposed)\|remains in proposed\|send_preserves_tasks\|receive_preserves_tasks\|10-operation\|six-field reachability\|nine-field reachability\|\`send a m\`\|\`receive a\`\|five .#eval" \
     README.md docs/ examples/ CHANGELOG.md Henret/ Main.lean 2>/dev/null \
     | grep -v "\.lake" | grep -v "docs/reviews/" | grep -v "rfcs/done/" | grep -v "docs/handoff-"; then
  echo "FAIL: stale documentation phrase found (v0.2.x/v0.3.x era)"; exit 1
fi
# v0.8.0 review stale phrases (RFC 037)
if grep -rn "six scenarios\|field 15 of 16\|all 16 fields\|carries no source actor\|requires an envelope or occurrence identity\|neither touches task state\|RFC 035.*Connecting" \
     README.md docs/ examples/ CHANGELOG.md Henret/ Main.lean 2>/dev/null \
     | grep -v "\.lake" | grep -v "docs/reviews/" | grep -v "rfcs/done/" | grep -v "docs/handoff-"; then
  echo "FAIL: stale v0.8.0 phrase found (RFC 037 gates)"; exit 1
fi
# Bridge claim rule + grammar-count drift (RFC 052 governance)
if grep -rn "complete bridge preservation\|all 12 RuntimeOps\|12-operation\|the bridge is complete\|18 RuntimeOps\|18-operation" \
     README.md docs/ examples/ CHANGELOG.md Henret/ Main.lean 2>/dev/null \
     | grep -v "\.lake" | grep -v "docs/reviews/" | grep -v "rfcs/done/" | grep -v "docs/handoff-"; then
  echo "FAIL: bridge-claim-rule / stale grammar-count phrase found (RFC 052 gates)"; exit 1
fi
echo "docs consistency ok"
echo "== gate 9/10: doc-symbol checker (RFC 026) =="
DOCSYM=$(mktemp /tmp/henret-docsym-XXXX.lean)
python3 scripts/doc_symbol_check.py > "$DOCSYM"
if ! lake env lean "$DOCSYM" > /dev/null 2>&1; then
  echo "FAIL: a backticked theorem name in docs does not resolve:"
  lake env lean "$DOCSYM" 2>&1 | grep "unknown" | head -10
  exit 1
fi
rm -f "$DOCSYM"
echo "doc symbols ok"

echo "== gate 10/10: RFC metadata schema (RFC 085) =="
if ! python3 scripts/rfc_metadata_check.py; then
  echo "FAIL: RFC front-matter metadata check failed (RFC 085)"
  exit 1
fi

echo "== all gates green =="
