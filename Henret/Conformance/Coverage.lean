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
    { op := "cancel",     branchId := "cancel.removes-timer",        scenario := "stale_timer_cannot_wake_cancelled" } ]

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
