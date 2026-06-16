#!/usr/bin/env python3
"""Strict axiom audit (RFC 020).

Reads `#print axioms` output on stdin, parses every
  'Name' depends on axioms: [a, b, ...]
block (which may wrap across lines), and checks each theorem's axiom set
EXACTLY against the allowlist below.  Any unexpected axiom — including a
project axiom with a novel name — fails the audit.  Theorems printed but
missing from the allowlist also fail (audit must be intentional).
"""
import re
import sys

STD = {"propext", "Quot.sound"}
STD_C = STD | {"Classical.choice"}  # reachability theorems use Classical.choice via by_cases/obtain
NATIVE_SIX = {
    "Henret.Native.NativeDeque.toList_empty",
    "Henret.Native.NativeDeque.toList_push",
    "Henret.Native.NativeDeque.steal_val",
    "Henret.Native.NativeDeque.steal_rest",
    "Henret.Native.NativeDeque.pop_val",
    "Henret.Native.NativeDeque.pop_rest",
}

# theorem -> (required ⊆ axioms, axioms ⊆ allowed)
ALLOWLIST = {
    # Lean-only core: standard kernel axioms only.
    "Henret.step_preserves_terminal":        (set(), STD),
    "Henret.step_invalid_unchanged":         (set(), STD),
    "Henret.run_preserves_wf":               (set(), STD_C),
    "Henret.reachable_wf":                   (set(), STD_C),
    "Henret.reachable_spawned_has_owner":    (set(), STD_C),
    "Henret.reachable_owner_has_mailbox":    (set(), STD_C),
    "Henret.step_clock_monotone":            (set(), STD),
    "Henret.receive_only_own":               (set(), STD),
    "Henret.reachable_runnable_is_queued":   (set(), STD_C),
    "Henret.reachable_queue_exact":          (set(), STD_C),
    "Henret.receive_empty_parks":            (set(), STD),
    "Henret.receive_blocked_parks":          (set(), STD),
    "Henret.reachable_waiters_exact":        (set(), STD_C),
    "Henret.reachable_waiter_actor_unique":  (set(), STD_C),
    "Henret.reachable_parent_lt":              (set(), STD_C),
    "Henret.reachable_occurrence_unique":       (set(), STD_C),
    "Henret.send_stamps_source":                (set(), STD),
    "Henret.inject_stamps_none":                (set(), STD),
    "Henret.parent_chain_terminates":           (set(), STD_C),
    # RFC 043 multi-worker bridge
    "Henret.Bridge.reachable_multi_bridge":            (set(), STD_C),
    "Henret.Bridge.single_bridge_implies_multi_bridge": (set(), STD),
    # RFC 045 execution trace ledger
    "Henret.Trace.stepTrace_state_eq_step":   (set(), STD),
    "Henret.Trace.stepTrace_result_eq_step":  (set(), STD),
    "Henret.Trace.runTraceLedger_state_eq_run": (set(), STD),
    "Henret.Trace.event_received_sound":      (set(), STD),
    "Henret.Trace.event_parked_sound":        (set(), STD),
    "Henret.Trace.event_timerWoke_sound":     (set(), STD),
    "Henret.Trace.event_spawnChild_sound":    (set(), STD),
    # RFC 047 golden trace conformance
    "Henret.Conformance.conformance_suite_passes": (set(), STD),
    # RFC 049 supervision restart policies
    "Henret.reachable_restart_fresh":              (set(), STD_C),
    "Henret.reachable_restart_old_failed":         (set(), STD_C),
    "Henret.reachable_restart_parent_consistent":  (set(), STD_C),
    "Henret.restart_preserves_parent_acyclicity":  (set(), STD_C),
    "Henret.restarted_task_has_owner":             (set(), STD_C),
    # RFC 054 semantic profile inclusion chain (kernel decide, propext only)
    "Henret.core_le_actor":                        (set(), STD),
    "Henret.actor_le_full":                        (set(), STD),
    "Henret.core_le_full":                         (set(), STD),
    # RFC 046 fairness / conditional liveness
    "Henret.Progress.ready_eventually_scheduled_under_bounded_fairness": (set(), STD),
    "Henret.Progress.schedule_schedules_head":  (set(), STD),
    "Henret.Progress.head_scheduled_within_one": (set(), STD),
    "Henret.Progress.unfairOps_not_bounded_fair_0": (set(), STD),
    # Pure native layer: still standard only.
    # "Henret.Native.qRun_tracks":             (set(), STD),
    # "Henret.Native.driveStackB_complete":    (set(), STD),
    # Assumed native layer: exactly the six declared axioms
    # (+ standard + Classical.choice from the opaque NonemptyType).
    # "Henret.Native.nativeDequeModel_qRun_tracks":
    #     (NATIVE_SIX, NATIVE_SIX | STD | {"Classical.choice"}),
}

text = sys.stdin.read()
# join wrapped lines: a block starts at 'Name' and runs to the closing ]
blocks = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",
                    text.replace("\n", " "))
if not blocks:
    print("AUDIT FAIL: no '#print axioms' output found")
    sys.exit(1)

seen = set()
fail = False
for name, axlist in blocks:
    seen.add(name)
    axioms = {a.strip() for a in axlist.split(",") if a.strip()}
    if name not in ALLOWLIST:
        print(f"AUDIT FAIL: {name} printed but not in allowlist")
        fail = True
        continue
    required, allowed = ALLOWLIST[name]
    extra = axioms - allowed
    missing = required - axioms
    if extra:
        print(f"AUDIT FAIL: {name} depends on unexpected axiom(s): {sorted(extra)}")
        fail = True
    if missing:
        print(f"AUDIT FAIL: {name} missing expected axiom(s): {sorted(missing)}")
        fail = True
    if not extra and not missing:
        print(f"audit ok: {name} ⊆ {sorted(allowed)}")

unprinted = set(ALLOWLIST) - seen
if unprinted:
    print(f"AUDIT FAIL: allowlisted theorem(s) not printed: {sorted(unprinted)}")
    fail = True

sys.exit(1 if fail else 0)
