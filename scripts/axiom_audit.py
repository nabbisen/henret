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
    # RFC 039 cascade cancel
    "Henret.cancelTree_cancels_task":              (set(), STD),
    "Henret.cancelTree_preserves_task_state":      (set(), STD),
    "Henret.Bridge.bridge_cancelTree":             (set(), STD),
    "Henret.preserves_wf_cancelTree":              (set(), STD),
    # RFC 038 owner / parent exactness (reachable)
    "Henret.reachable_owner_spawned":              (set(), STD_C),
    "Henret.reachable_parent_child_spawned":       (set(), STD_C),
    # RFC 036 single-worker bridge headline theorems
    "Henret.Bridge.bridge_step_single_worker":         (set(), STD),
    "Henret.Bridge.bridge_run_tracks_single_worker":   (set(), STD),
    "Henret.Bridge.bridge_run_general":                (set(), STD),
    # Pure native layer (model only): standard axioms.
    "Henret.Native.qRun_tracks":                   (set(), STD),
    "Henret.Native.driveStackB_complete":          (set(), STD),
    # Assumed native FFI layer: exactly the six declared axioms
    # (+ standard + Classical.choice from the opaque NonemptyType).
    "Henret.Native.nativeDequeModel_qRun_tracks":
        (NATIVE_SIX, NATIVE_SIX | STD | {"Classical.choice"}),
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
    "Henret.Conformance.branch_suite_passes": (set(), STD),
    "Henret.Conformance.coverage_complete": (set(), STD),
    # RFC 056 — bounded mailboxes / backpressure
    "Henret.reachable_mailbox_within_capacity": (set(), STD_C),
    "Henret.step_backpressured_unchanged":      (set(), STD),
    "Henret.send_full_backpressured":           (set(), STD),
    "Henret.inject_full_backpressured":         (set(), STD),
    "Henret.send_unbounded_not_backpressured":  (set(), STD),
    "Henret.inject_unbounded_not_backpressured": (set(), STD),
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
    # RFC 055 structured cancellation / shutdown safety (pure step lemmas)
    "Henret.closeActor_sets_closed":               (set(), STD),
    "Henret.closed_actor_rejects_send":            (set(), STD),
    "Henret.closed_actor_rejects_inject":          (set(), STD),
    "Henret.shutdown_rejects_spawn":               (set(), STD),
    "Henret.shutdown_sets_status":                 (set(), STD),
    "Henret.stopWhenIdle_requires_quiescent":      (set(), STD),
    "Henret.stopWhenIdle_sets_stopped":            (set(), STD),
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
    # RFC 057: resource lifetime & finalization ledger
    "Henret.preserves_wf_acquire":   (set(), STD),
    "Henret.preserves_wf_release":   (set(), STD),
    "Henret.preserves_wf_finalize":  (set(), STD),
    "Henret.reachable_resource_fresh":              (set(), STD_C),
    "Henret.reachable_resource_owner_spawned":      (set(), STD_C),
    "Henret.reachable_allocated_owner_nonterminal": (set(), STD_C),
    "Henret.reachable_closing_owner_terminal":      (set(), STD_C),
    "Henret.nextResourceId_monotone_step": (set(), STD),
    "Henret.nextResourceId_monotone_run":  (set(), STD),
    "Henret.complete_marks_owned_resource_closing": (set(), STD),
    "Henret.cancel_marks_owned_resource_closing":   (set(), STD),
    "Henret.fail_marks_owned_resource_closing":     (set(), STD),
    "Henret.cancelTree_marks_descendant_resource_closing": (set(), STD),
    "Henret.full_has_resourceLifetime": (set(), STD),
    "Henret.full_has_schedulingPolicy": (set(), STD),
    # RFC 057: per-branch behavioural theorems
    "Henret.acquire_running_allocates":          (set(), STD),
    "Henret.acquire_not_running_invalid":        (set(), STD),
    "Henret.acquire_non_running_state_invalid":  (set(), STD),
    "Henret.release_owner_allocated_ok":         (set(), STD),
    "Henret.release_non_owner_invalid":          (set(), STD),
    "Henret.release_released_invalid":           (set(), STD),
    "Henret.release_closing_invalid":            (set(), STD),
    "Henret.finalize_closing_ok":                (set(), STD),
    "Henret.finalize_allocated_invalid":         (set(), STD),
    "Henret.finalize_released_invalid":          (set(), STD),
    # RFC 057: released is a terminal ledger state
    "Henret.released_resource_never_live_step": (set(), STD),
    "Henret.released_resource_never_live_run":  (set(), STD_C),
    "Henret.reachable_released_resource_never_live": (set(), STD_C),
    # RFC 064: fault & outcome taxonomy (zero-axiom classification)
    "Henret.blocked_not_invalid_class":        (set(), STD),
    "Henret.backpressured_not_invalid_class":  (set(), STD),
    "Henret.timedOut_not_invalid_class":       (set(), STD),
    "Henret.invalid_is_fault":                 (set(), STD),
    "Henret.blocked_not_fault":                (set(), STD),
    "Henret.backpressured_not_fault":          (set(), STD),
    "Henret.timedOut_not_fault":               (set(), STD),
    "Henret.ok_not_fault":                     (set(), STD),
    # RFC 058: scheduling policy layer
    "Henret.reorder_preserves_wf":      (set(), STD_C),
    "Henret.policyStep_preserves_wf":   (set(), STD_C),
    "Henret.policy_does_not_create_task": (set(), STD),
    "Henret.fifo_policy_equiv_schedule": (set(), STD),
    "Henret.schedule_preserves_nextId":  (set(), STD),
    # RFC 059: deadline & priority semantics
    "Henret.wf_taskMeta_only":          (set(), STD),
    "Henret.preserves_wf_setPriority":  (set(), STD),
    "Henret.preserves_wf_setDeadline":  (set(), STD),
    "Henret.setPriority_meta_of_spawned": (set(), STD),
    "Henret.setDeadline_meta_of_spawned": (set(), STD),
    "Henret.pickBy_mem":                (set(), STD),
    "Henret.foldl_best_mem":            (set(), STD),
    "Henret.foldl_best_ge":             (set(), STD),
    "Henret.priority_policy_selects_max": (set(), STD),
    "Henret.foldl_winner":              (set(), STD),
    "Henret.deadlineLt_irrefl":         (set(), STD),
    "Henret.deadline_policy_selects_min_deadline": (set(), STD),
    "Henret.closing_finalize_releases": (set(), STD),
    "Henret.resourceDrained_drained":  (set(), STD),
    "Henret.stopWhenDrained_stops_drained": (set(), STD),
    "Henret.stopWhenDrained_stops":    (set(), STD),
    "Henret.stopWhenDrained_noop":     (set(), STD),
    "Henret.preserves_wf_stopWhenDrained": (set(), STD),
    "Henret.Bridge.bridge_stopWhenDrained": (set(), STD),
    # RFC 088 — drained-state persistence (RFC 057 Tier 2)
    "Henret.step_resources_none_run_none": (set(), STD),
    "Henret.drained_step_drained":     (set(), STD),
    "Henret.stopWhenDrained_then_step_drained": (set(), STD),
    # RFC 089 — sleeping-timer coherence (RFC 057 Tier 2 groundwork)
    "Henret.sleepingHasTimer_init":    (set(), STD),
    "Henret.step_preserves_sleepingHasTimer": (set(), STD),
    "Henret.run_preserves_sleepingHasTimer":  (set(), STD),
    "Henret.reachable_sleepingHasTimer": (set(), STD),
    "Henret.quiescent_no_sleeping":    (set(), STD),
    # RFC 090 — Frozen bundle / multi-step drained permanence (RFC 057 Tier 2 payoff)
    "Henret.step_preserves_frozen":    (set(), STD),
    "Henret.stopWhenDrained_enters_frozen": (set(), STD),
    "Henret.frozen_run_drained":       (set(), STD_C),
    "Henret.reachable_stopWhenDrained_stays_drained":   (set(), STD_C),
    "Henret.reachable_stopWhenDrained_stays_quiescent": (set(), STD_C),
}

text = sys.stdin.read()
# join wrapped lines: a block starts at 'Name' and runs to the closing ]
blocks = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",
                    text.replace("\n", " "))
# A theorem proved without any axiom prints "... does not depend on any axioms"
# rather than "depends on axioms: []"; record those as an empty axiom set.
blocks += [(name, "")
           for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
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
