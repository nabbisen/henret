import Henret.Conformance.Branch
import Henret.Conformance.Golden
/-!
  # Henret.Conformance.Coverage  (RFC 083)

  The coverage source of truth (083-D): a Lean registry, not hand-maintained
  markdown. Every executable `RuntimeOp` semantic branch is tied to a named
  golden scenario — a trace `GoldenScenario` (RFC 047) for the pre-RFC-033
  operations, or a `BranchScenario` (RFC 083) for everything added since and
  the negative/security cases. Closed-actor and shutdown rejections are
  explicit branches here (083-5), not merely scenario names.

  `coverage_complete` kernel-checks two things:
  (1) every registry branch names a scenario that actually exists, and
  (2) every `BranchScenario.covers` id is a real registry branch
  (so a scenario cannot claim coverage that the registry does not record).
-/
namespace Henret.Conformance

open Henret

/-- One executable branch and the golden scenario that covers it. -/
structure CoverageEntry where
  /-- The `RuntimeOp` this branch belongs to. -/
  op       : String
  /-- Stable, namespaced branch id (083-2). -/
  branchId : BranchId
  /-- Name of the covering scenario (trace or branch), or "" if `outscope`. -/
  scenario : String
  /-- Explicitly not covered by a golden scenario. -/
  outscope : Bool := false
  /-- Reason, required when `outscope`. -/
  reason   : String := ""

/-- Every executable `RuntimeOp` branch. Pre-RFC-033 operations are covered by
    the RFC 047 trace suite; post-RFC-033 operations and the negative/security
    cases by the RFC 083 branch suite. -/
def coverageRegistry : List CoverageEntry :=
  [ -- pre-RFC-033 operations (RFC 047 trace scenarios)
    { op := "spawn",      branchId := "spawn.creates-task",        scenario := "spawn_schedule_complete" },
    { op := "schedule",   branchId := "schedule.runs-head",        scenario := "spawn_schedule_complete" },
    { op := "complete",   branchId := "complete.terminal",         scenario := "spawn_schedule_complete" },
    { op := "yield",      branchId := "yield.requeues",            scenario := "yield_requeues" },
    { op := "sleep",      branchId := "sleep.sets-timer",          scenario := "sleep_tick_wakes" },
    { op := "tick",       branchId := "tick.wakes-sleeping",       scenario := "sleep_tick_wakes" },
    { op := "receive",    branchId := "receive.empty-parks",       scenario := "empty_receive_parks" },
    { op := "send",       branchId := "send.wakes-waiter",         scenario := "send_wakes_waiter_mesa" },
    { op := "inject",     branchId := "inject.wakes-waiter",       scenario := "inject_wakes_waiter_mesa" },
    { op := "cancel",     branchId := "cancel.ready-task",         scenario := "cancel_ready_task" },
    { op := "cancel",     branchId := "cancel.waiting-task",       scenario := "cancel_waiting_task" },
    { op := "spawnChild", branchId := "spawnChild.records-parent", scenario := "spawn_child_parent_lt" },
    { op := "send",       branchId := "send.fresh-occurrence",     scenario := "occurrence_unique_two_mailboxes" },
    -- receiveUntil (RFC 040)
    { op := "receiveUntil", branchId := "receiveUntil.timeout-fast-path",     scenario := "receiveUntil_timeout_fast_path" },
    { op := "receiveUntil", branchId := "receiveUntil.park-future-deadline",  scenario := "receiveUntil_park_future_deadline" },
    { op := "receiveUntil", branchId := "receiveUntil.park-then-tick-wakes",  scenario := "receiveUntil_park_then_tick_wakes" },
    { op := "receiveUntil", branchId := "receiveUntil.message-before-deadline", scenario := "receiveUntil_message_before_deadline" },
    { op := "receiveUntil", branchId := "receiveUntil.non-running-invalid",   scenario := "waiting_task_cannot_receive" },
    { op := "tick",         branchId := "tick.wakes-waitingTimed",            scenario := "receiveUntil_park_then_tick_wakes" },
    -- selective receive (RFC 041)
    { op := "receiveByOccurrence", branchId := "receiveByOccurrence.hit",        scenario := "receiveByOccurrence_hit" },
    { op := "receiveByOccurrence", branchId := "receiveByOccurrence.miss-parks", scenario := "receiveByOccurrence_miss_parks" },
    { op := "receiveFrom",         branchId := "receiveFrom.source-hit",         scenario := "receiveFrom_source_hit" },
    { op := "receiveFrom",         branchId := "receiveFrom.source-miss-parks",  scenario := "receiveFrom_source_miss_parks" },
    -- supervision (RFC 049)
    { op := "fail",       branchId := "fail.marks-failed",          scenario := "fail_marks_failed" },
    { op := "restartOne", branchId := "restartOne.spawns-replacement", scenario := "restartOne_spawns_replacement" },
    -- structured cancellation / shutdown (RFC 055) — closed/shutdown are branches (083-5)
    { op := "closeActor",   branchId := "closeActor.preserves-mailbox",      scenario := "closeActor_preserves_mailbox" },
    { op := "shutdown",     branchId := "shutdown.sets-status",              scenario := "shutdown_sets_status" },
    { op := "shutdown",     branchId := "shutdown.idempotent",               scenario := "shutdown_sets_status" },
    { op := "stopWhenIdle", branchId := "stopWhenIdle.quiescent",            scenario := "stopWhenIdle_quiescent" },
    { op := "stopWhenIdle", branchId := "stopWhenIdle.nonquiescent-invalid", scenario := "stopWhenIdle_nonquiescent" },
    -- direct wake (RFC 005) and cascade cancel (RFC 039)
    { op := "wake",       branchId := "wake.moves-sleeper-to-ready", scenario := "wake_moves_sleeper_to_ready" },
    { op := "cancelTree", branchId := "cancelTree.cancels-subtree",  scenario := "cancelTree_cancels_subtree" },
    -- Mesa re-park (083-4)
    { op := "receive",    branchId := "receive.mesa-repark",         scenario := "mesa_woken_task_can_repark" },
    -- negative / security branches (083 §Negative)
    { op := "send",       branchId := "send.non-running-invalid",    scenario := "non_running_send_invalid" },
    { op := "receive",    branchId := "receive.unowned-invalid",     scenario := "unowned_receive_invalid" },
    { op := "send",       branchId := "send.waiting-task-invalid",   scenario := "waiting_task_cannot_send" },
    { op := "schedule",   branchId := "schedule.skips-cancelled",    scenario := "cancelled_task_not_schedulable" },
    { op := "cancel",     branchId := "cancel.removes-from-readyQ",  scenario := "cancelled_task_not_schedulable" },
    { op := "send",       branchId := "send.closed-actor-invalid",   scenario := "closed_actor_rejects_send" },
    { op := "inject",     branchId := "inject.closed-actor-invalid", scenario := "closed_actor_rejects_inject" },
    { op := "spawn",      branchId := "spawn.shutdown-invalid",      scenario := "shutdown_rejects_spawn" },
    { op := "inject",     branchId := "inject.shutdown-invalid",     scenario := "shutdown_rejects_inject" },
    { op := "tick",       branchId := "tick.never-wakes-cancelled",  scenario := "stale_timer_cannot_wake_cancelled" },
    { op := "cancel",     branchId := "cancel.removes-timer",        scenario := "stale_timer_cannot_wake_cancelled" },
    -- bounded mailboxes / backpressure (RFC 056)
    { op := "send",   branchId := "send.capacity-ok",                  scenario := "bounded_send_then_backpressured" },
    { op := "send",   branchId := "send.capacity-full-backpressured",  scenario := "bounded_send_then_backpressured" },
    { op := "send",   branchId := "send.capacity-frees-after-receive", scenario := "bounded_receive_frees_capacity" },
    { op := "inject", branchId := "inject.capacity-full-backpressured", scenario := "bounded_inject_full_backpressured" },
    { op := "send",   branchId := "send.capacity-zero-reject-all",     scenario := "capacity_zero_send_backpressured" },
    { op := "inject", branchId := "inject.capacity-zero-reject-all",   scenario := "capacity_zero_inject_backpressured" },
    { op := "send",   branchId := "send.unbounded-never-backpressured", scenario := "unbounded_send_never_backpressured" },
    { op := "inject", branchId := "inject.full-with-waiter-backpressured", scenario := "full_mailbox_with_waiter_inject_backpressured" },
    { op := "send",   branchId := "send.full-with-waiter-backpressured",   scenario := "full_mailbox_with_waiter_send_backpressured" },
    -- resource lifetime & finalization ledger (RFC 057)
    { op := "acquire",  branchId := "acquire.running-allocates",    scenario := "resource_acquire_release_ok" },
    { op := "acquire",  branchId := "acquire.fresh-id",             scenario := "resource_acquire_returns_fresh_id" },
    { op := "acquire",  branchId := "acquire.not-running-invalid",  scenario := "resource_acquire_not_running_invalid" },
    { op := "release",  branchId := "release.owner-allocated-ok",   scenario := "resource_acquire_release_ok" },
    { op := "release",  branchId := "release.non-owner-invalid",    scenario := "resource_release_non_owner_invalid" },
    { op := "release",  branchId := "release.released-invalid",     scenario := "resource_release_after_release_invalid" },
    { op := "finalize", branchId := "finalize.closing-ok",          scenario := "resource_finalize_closing_released" },
    { op := "finalize", branchId := "finalize.allocated-invalid",   scenario := "resource_finalize_allocated_invalid" },
    { op := "complete", branchId := "complete.marks-owned-closing", scenario := "resource_complete_marks_closing" },
    { op := "cancel",   branchId := "cancel.marks-owned-closing",   scenario := "resource_cancel_marks_closing" },
    { op := "fail",     branchId := "fail.marks-owned-closing",     scenario := "resource_fail_marks_closing" },
    { op := "stopWhenDrained", branchId := "stopWhenDrained.drained-stops",          scenario := "stopWhenDrained_drained_stops" },
    { op := "stopWhenDrained", branchId := "stopWhenDrained.live-resource-invalid",  scenario := "stopWhenDrained_live_resource_invalid" },
    { op := "stopWhenDrained", branchId := "stopWhenDrained.persists-drained",        scenario := "stopWhenDrained_then_acquire_stays_drained" },
    { op := "acquireActor", branchId := "acquireActor.ok",                       scenario := "acquireActor_ok" },
    { op := "acquireActor", branchId := "acquireActor.invalid-closed-actor",     scenario := "acquireActor_invalid_closed_actor" },
    { op := "acquireActor", branchId := "acquireActor.invalid-missing-mailbox",  scenario := "acquireActor_invalid_missing_mailbox" },
    { op := "acquireActor", branchId := "acquireActor.survives-task-complete",   scenario := "task_complete_does_not_close_actor_resource" },
    { op := "acquireActor", branchId := "acquireActor.survives-task-cancel",     scenario := "task_cancel_does_not_close_actor_resource" },
    { op := "acquireActor", branchId := "acquireActor.survives-task-fail",       scenario := "task_fail_does_not_close_actor_resource" },
    { op := "closeActor",   branchId := "closeActor.marks-actor-resource-closing", scenario := "closeActor_marks_actor_resource_closing" },
    { op := "finalize",     branchId := "finalize.actor-resource-released",      scenario := "finalize_actor_resource_released" },
    { op := "release",      branchId := "release.actor-owned-invalid",           scenario := "release_task_on_actor_resource_invalid" },
    { op := "stopWhenDrained", branchId := "stopWhenDrained.blocked-by-actor-allocated", scenario := "stopWhenDrained_blocked_by_actor_allocated_resource" },
    { op := "stopWhenDrained", branchId := "stopWhenDrained.blocked-by-actor-closing",   scenario := "stopWhenDrained_blocked_by_actor_closing_resource" },
    { op := "stopWhenDrained", branchId := "stopWhenDrained.succeeds-after-actor-finalize", scenario := "stopWhenDrained_succeeds_after_actor_resource_finalized" },
    { op := "stopWhenIdle", branchId := "stopWhenIdle.stops-with-live-resource", scenario := "stopWhenIdle_stops_with_live_resource" } ]

/-- The names of every available golden scenario (trace + branch). -/
def allScenarioNames : List String :=
  goldenScenarios.map (·.name) ++ branchScenarios.map (·.name)

/-- Coverage is complete when (1) every registry branch names an existing
    scenario or is `outscope` with a reason, and (2) every `BranchScenario`'s
    claimed `covers` id is a real registry branch. -/
def coverageComplete : Bool :=
  coverageRegistry.all (fun e =>
    (e.outscope && e.reason != "") || allScenarioNames.contains e.scenario)
  && branchScenarios.all (fun sc =>
       sc.covers.all (fun id => coverageRegistry.any (·.branchId == id)))

/-- **Coverage gate** (RFC 080 stage 6) — kernel-checked completeness of the
    branch-to-scenario registry. Adding a `RuntimeOp` branch without a covering
    scenario, or a scenario claiming an unregistered branch, breaks this. -/
theorem coverage_complete : coverageComplete = true := by decide

/-- A human-readable coverage report. -/
def coverageReport : String :=
  s!"branches: {coverageRegistry.length}; scenarios: {allScenarioNames.length} "
    ++ s!"(trace {goldenScenarios.length} + branch {branchScenarios.length}); "
    ++ (if coverageComplete then "coverage COMPLETE" else "coverage INCOMPLETE")

end Henret.Conformance
