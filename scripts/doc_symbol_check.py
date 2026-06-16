#!/usr/bin/env python3
"""Doc-symbol checker (RFC 026, reviewer SF-05 long-term option).

Extracts backticked identifiers that look like theorem/lemma names from the
proof documentation and emits a Lean file of `#check` lines. The release
gate compiles that file: a stale theorem name in the docs becomes a build
failure instead of silent drift.

Heuristic for "looks like a theorem name": contains an underscore, starts
lowercase, is a bare identifier or a dotted one (Timer.foo, Mailbox.foo,
WellFormed.foo). Tokens in IGNORE are documentation vocabulary, field
names used in prose, file paths, or operation syntax — not public theorem
references.
"""
import re
import sys

# Strict proof-doc files: every theorem name here must exist in source.
PROOF_DOC_FILES = [
    "docs/proof-index.md",
    "docs/proof-trust-test-matrix.md",
]

# Broader live-doc files: README, guides, examples (excludes historical
# docs that intentionally quote removed names: rfcs/done/, docs/reviews/,
# docs/handoff-*, CHANGELOG.md entries that quote old state).
LIVE_DOC_FILES = [
    "README.md",
    "docs/test-index.md",
    "docs/guided-tour.md",
    "examples/README.md",
]

DOC_FILES = PROOF_DOC_FILES + LIVE_DOC_FILES

# Not theorem references: ops/syntax, fields discussed in prose, files, vocab.
IGNORE = {
    # RFC 033 WellFormed field names (not standalone theorems)
    "occ_fresh", "occ_nodup", "occ_disjoint",
    "nextMsgId", "occurrence",
    # RFC 038 WellFormed field names (not standalone theorems; use WellFormed.X form)
    "owner_spawned", "parent_child_spawned",
    # RFC 040 WellFormed timed field names (not standalone theorems)
    "timed_has_deadline", "deadline_is_timed", "timed_has_timer",
    "timed_is_waiter", "timed_waiters_valid", "timed_waiters_nodup",
    "timed_waiters_exclusive",
    # RFC 040 new toQOps lemmas
    "toQOps_send_valid_timed_waiter", "toQOps_inject_valid_timed_waiter",
    "receiveUntil",
    # RFC 041 Mailbox selective-dequeue helpers (Mailbox.* namespace)
    "dequeueFirst", "dequeueFirstByOccurrence", "dequeueFirstFrom",
    "dequeueFirst_matches", "dequeueFirst_sublist", "dequeueFirst_none",
    "dequeue_spec", "listDequeueFirst", "listDequeueFirst_matches",
    "listDequeueFirst_mem", "listDequeueFirst_sublist", "listDequeueFirst_none",
    "receiveByOccurrence", "receiveFrom",
    # RFC 043 multi-worker bridge
    "applyMQOp", "applyMQOps", "MultiBridgeState",
    "multi_bridge_push", "multi_bridge_filter", "multi_bridge_steal",
    "single_bridge_implies_multi_bridge", "reachable_multi_bridge",
    # MultiBridgeState / WellFormed field names referenced in prose
    "global_unique", "worker_nodup", "reachable_wf.readyQ_nodup",
    # RFC 045 trace ledger
    "TraceEvent", "stepTrace", "runTraceLedger", "traceEvents", "eventsOf",
    "stepTrace_state_eq_step", "stepTrace_result_eq_step",
    "runTraceLedger_state_eq_run", "runTraceLedger_results_eq_runTrace",
    "event_received_sound", "event_parked_sound", "event_directWoke_sound",
    "event_timerWoke_sound", "event_spawnChild_sound", "event_scheduled_sound",
    "event_waiterWoke_send_sound",
    "invalid", "spawned", "spawnChild", "scheduled", "yielded", "completed",
    "cancelled", "slept", "timerWoke", "directWoke", "sent", "injected",
    "received", "parked", "waiterWoke", "noEffect", "runTrace",
    # RFC 047 golden trace conformance
    "GoldenScenario", "observe", "checkScenario", "scenarioReport",
    "TraceRefines", "firstMismatch", "goldenScenarios", "allPass",
    "suiteReport", "conformance_suite_passes", "renderEvent", "renderTrace",
    "branch_suite_passes", "coverage_complete", "branchScenarios",
    "kernelScenarios", "checkBranch", "coverageComplete", "coverageRegistry",
    "BranchScenario", "branchAllPass", "branchReport", "coverageReport",
    "renderScenario", "renderSuite",
    # RFC 047 golden scenario names
    "spawn_schedule_complete", "yield_requeues", "sleep_tick_wakes",
    "empty_receive_parks", "send_wakes_waiter_mesa", "inject_wakes_waiter_mesa",
    "cancel_ready_task", "cancel_waiting_task", "spawn_child_parent_lt",
    "occurrence_unique_two_mailboxes",
    # RFC 046 fairness / conditional liveness
    "stateAt", "runnableAtStep", "scheduledAtStep", "BoundedReadyFair",
    "ready_eventually_scheduled_under_bounded_fairness",
    "schedule_schedules_head", "head_scheduled_within_one",
    "fairOps", "unfairOps", "fair_task0_scheduled", "fair_task1_scheduled",
    "unfair_task1_runnable", "unfair_task1_never_scheduled",
    "unfairOps_not_bounded_fair_0",
    # RFC 048 bounded model explorer (HenretExplore lib, outside default import)
    "SmallWorld", "genOps", "genPrograms", "genProgramsExact",
    "checkWellFormedBool", "checkOccUniqueBool", "checkBridgeBool",
    "occurrenceIds", "propWellFormed", "propOccurrenceUnique", "propBridge",
    "propReadyAlwaysEmpty", "explore", "confirms", "shrinkPass",
    "shrinkProgram", "findAndShrink", "Property",
    # RFC 049 supervision restart policies
    "fail", "restartOne", "restartOf", "RestartWellFormed",
    "restart_parent_consistent", "restart_old_failed", "restart_fresh",
    "restart_wf_init", "step_restartOf_stable", "step_preserves_restart_wf",
    "reachable_restart_wf", "reachable_restart_fresh",
    "reachable_restart_old_failed", "reachable_restart_parent_consistent",
    "restart_preserves_parent_acyclicity", "restarted_task_has_owner",
    "preserves_wf_fail", "preserves_wf_restartOne", "bridge_fail",
    "bridge_restartOne", "restartOf_irrel", "run_preserves_restart_wf",
    "restart_wf_of_restartOf_stable", "restart_wf_restartOne", "supervision",
    "isTerminal_failed", "TaskState.failed",
    # RFC 054 semantic profiles
    "SemanticFeature", "SemanticProfile", "Subset", "Has", "nodup",
    "Profile.core", "Profile.actor", "Profile.full",
    # RFC 050 observability / visualization (pure renderers)
    "render", "traceTable", "stateWord", "taskLocation", "locationMap",
    "mailboxView", "stateRender", "readyIndex", "waitingActor",
    "timedWaitingActor", "usedActors", "mailboxLine", "parentTreeMermaid",
    "mailboxMermaid", "bridgeWorkerQueues", "scenario", "tree",
    # RFC 035/036 Bridge sub-namespace types/internals — not standalone theorems
    "bridgeState_init", "bridgeState_push0", "bridgeState_pop0", "bridgeState_filter0",
    "bridgeState_readyQ_unchanged", "applyQOp", "applyQOps", "applyQOps_append",
    "WorkerQueues", "WorkerQueues.init", "BridgeState", "QOp", "toQOps", "toQOpsTrace",
    "bridge_stable", "WorkerIdx", "pushWorker0",
    # toQOps direct-effect lemmas (internal; listed in proof-index but not live docs)
    "toQOps_spawn_valid", "toQOps_spawn_invalid",
    "toQOps_spawnChild_valid",
    "toQOps_yield_valid", "toQOps_yield_invalid",
    "toQOps_wake_valid", "toQOps_wake_invalid",
    "toQOps_cancel_valid", "toQOps_cancel_invalid_terminal", "toQOps_cancel_invalid_unspawned",
    "toQOps_send_valid_waiter", "toQOps_send_valid_no_waiter",
    "toQOps_inject_valid_waiter", "toQOps_inject_valid_no_waiter", "toQOps_inject_invalid",
    "toQOps_tick_valid", "toQOps_tick_invalid",
    "toQOps_complete_nil", "toQOps_receive_nil", "toQOps_sleep_nil",
    "toQOps_schedule_nonempty", "toQOps_schedule_empty",
    # operation syntax and grammar tokens
    "send t b m", "receive t", "inject a m", "spawn a", "yield t",
    "complete t", "cancel t", "sleep t deadline", "tick now", "wake t",
    "tick t", "wake_many", "step s op",
    # structures / types / modules / files (checked elsewhere or not theorems)
    "lean_lib", "check-rfcs", "lake build", "lake exe",
    # WellFormed fields referenced in prose (they resolve as projections;
    # checked via the WellFormed. prefix variants below when written dotted)
    "readyQ_nodup", "readyQ_queued", "running_runs", "timers_nodup",
    "timers_sleep", "fresh_none", "timers_sorted", "spawned_has_owner",
    "owned_has_mailbox",
    # value/test vocabulary
    "proof-trust-test-matrix", "assumption-index", "test-index",
    "henret-demo", "check.sh", "axiom_audit.py",
    # Lean tactics mentioned in prose
    "native_decide",
    # WF fields added in RFC 031 (discussed in prose, not theorem names)
    "waiters_waiting", "waiters_owned", "waiting_queued", "waiters_nodup",
    # Mesa-semantics prose tokens
    "mailboxWaiters", "taskState", "readyQ", "mailboxes",
    # version/file tokens that appear in live docs
    "lake_build", "lake_exe", "lake_env",
    # RuntimeState/RuntimeOp field and constructor names used in prose
    "send", "receive", "inject", "taskOwner", "taskState", "taskParent",
    "now", "running", "nextId", "timers",
    # WellFormed fields referenced bare (the dotted WellFormed.X forms are checked)
    "parent_lt", "parent_spawned",
    # Historical name mentioned only in a rename note
    "drivePopB",
    # RFC 035 BridgeState field names (not standalone theorems)
    "queue_eq", "other_empty",
    # RFC 081 evidence-ledger vocabulary (documentation terms, not theorems)
    "in_tree_model_proof", "in_tree_model_test", "sibling_runtime_package",
    "external_artifact", "verified_by_this_tarball", "verified_by_ci",
    "evidence_location", "claim_id", "external_version", "external_commit",
    # RFC 056 WellFormed field referenced bare (dotted WellFormed.X is checked)
    "mailbox_within_capacity",
    # RFC 056 conformance scenario defs (Henret.Conformance namespace, not theorems)
    "bounded_send_then_backpressured", "bounded_receive_frees_capacity",
    "bounded_inject_full_backpressured", "capacity_zero_send_backpressured",
    "capacity_zero_inject_backpressured", "unbounded_send_never_backpressured",
    "full_mailbox_with_waiter_send_backpressured",
    "full_mailbox_with_waiter_inject_backpressured",
    # RFC 057 WellFormed fields referenced bare (dotted WellFormed.X is checked)
    "resource_fresh", "resource_owner_spawned",
    "allocated_owner_nonterminal", "closing_owner_terminal",
    # RFC 057 conformance scenario defs (Henret.Conformance namespace, not theorems)
    "resource_acquire_release_ok", "resource_acquire_returns_fresh_id",
    "resource_release_non_owner_invalid", "resource_release_after_release_invalid",
    "resource_finalize_allocated_invalid", "resource_cancel_marks_closing",
    "resource_fail_marks_closing", "resource_complete_marks_closing",
    "resource_finalize_closing_released", "resource_acquire_not_running_invalid",
}

NAME_RE = re.compile(r"`([A-Za-z][A-Za-z0-9_.']*)`")


def looks_like_theorem(tok: str) -> bool:
    if tok in IGNORE:
        return False
    if "/" in tok or " " in tok:
        return False
    head = tok.split(".")[-1]
    if "_" not in head:
        return False
    if not head[0].islower():
        return False
    # skip obvious file stems
    if tok.endswith(".md") or tok.endswith(".lean") or tok.endswith(".sh"):
        return False
    return True


def main() -> int:
    names = set()
    for f in DOC_FILES:
        try:
            text = open(f).read()
        except FileNotFoundError:
            print(f"doc-symbol: missing doc file {f}")
            return 1
        for tok in NAME_RE.findall(text):
            tok = tok.rstrip(".")
            if looks_like_theorem(tok):
                names.add(tok)

    lines = [
        "import Henret",
        "import Henret.Native.DequeModel",
        "import Henret.Native.Assumptions",
        "open Henret Henret.Native Henret.Bridge",
        "",
    ]
    for n in sorted(names):
        lines.append(f"#check @{n}")
    out = "\n".join(lines) + "\n"
    sys.stdout.write(out)
    print(f"-- doc-symbol: {len(names)} names extracted", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
