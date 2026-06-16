import Henret.Conformance.Scenario
/-!
  # Henret.Conformance.Branch  (RFC 083)

  The branch-coverage conformance suite. Where RFC 047's `GoldenScenario`
  pins an observable `TraceEvent` trace, a `BranchScenario` pins the exact
  `StepResult` sequence *and* an executable final-state predicate, and
  declares which semantic `RuntimeOp` branches it covers (083-2/083-3).

  Every executable branch added since RFC 033 (receiveUntil, selective
  receive, fail/restartOne, closeActor/shutdown/stopWhenIdle) plus the
  negative/security cases get a scenario here; `Coverage.lean` ties each
  branch to its scenario. Expected results are the model's own output.
-/
namespace Henret.Conformance

open Henret

/-- A stable, namespaced semantic-branch identifier (083-2),
    e.g. `"receiveUntil.timeout-fast-path"`. -/
abbrev BranchId := String

/-- An executable branch-coverage scenario (083-3). -/
structure BranchScenario where
  /-- Stable scenario identifier. -/
  name        : String
  /-- One-line purpose. -/
  description : String
  /-- The operation sequence. -/
  ops         : List RuntimeOp
  /-- The exact `StepResult` sequence the model produces. -/
  expected    : List StepResult
  /-- Executable final-state predicate. -/
  finalCheck  : RuntimeState → Bool
  /-- Semantic branches this scenario covers. -/
  covers      : List BranchId
  /-- A negative/security scenario (proves the model rejects / no-ops). -/
  negative    : Bool := false
  /-- Starting state. -/
  initial     : RuntimeState := RuntimeState.init

/-- Run a scenario, returning `(finalState, results)`. -/
def runBranch (sc : BranchScenario) : RuntimeState × List StepResult :=
  runTrace sc.initial sc.ops

/-- A scenario passes when the observed `StepResult` sequence equals the
    expected one and the final-state predicate holds. -/
def checkBranch (sc : BranchScenario) : Bool :=
  let (s', rs) := runBranch sc
  (rs == sc.expected) && sc.finalCheck s'

/-- Small helpers for final-state predicates. -/
def mailboxLen (s : RuntimeState) (a : ActorId) : Nat :=
  match s.mailboxes a with | some mb => mb.messages.length | none => 0

/-! ## Positive scenarios -/

def receiveUntil_timeout_fast_path : BranchScenario where
  name := "receiveUntil_timeout_fast_path"
  description := "receiveUntil with deadline ≤ now on an empty mailbox returns immediately"
  ops := [.spawn 7, .schedule, .receiveUntil 0 0]
  expected := [.spawned 0, .scheduled 0, .timedOut]
  finalCheck := fun s =>
    s.taskState 0 == some .running && s.running == some 0 &&
    s.timers.isEmpty && (s.timedMailboxWaiters 7).isEmpty
  covers := ["receiveUntil.timeout-fast-path"]

def receiveUntil_park_future_deadline : BranchScenario where
  name := "receiveUntil_park_future_deadline"
  description := "receiveUntil with deadline > now on an empty mailbox parks with a timer"
  ops := [.spawn 7, .schedule, .receiveUntil 0 5]
  expected := [.spawned 0, .scheduled 0, .blocked]
  finalCheck := fun s =>
    s.taskState 0 == some .waitingTimed && s.running == none &&
    (s.timedMailboxWaiters 7).contains 0 && s.waitDeadline 0 == some 5 &&
    s.timers.any (fun e => e.task == 0)
  covers := ["receiveUntil.park-future-deadline"]

def receiveUntil_park_then_tick_wakes : BranchScenario where
  name := "receiveUntil_park_then_tick_wakes"
  description := "a parked receiveUntil is woken by a tick at/after its deadline"
  ops := [.spawn 7, .schedule, .receiveUntil 0 5, .tick 5]
  expected := [.spawned 0, .scheduled 0, .blocked, .woke [0]]
  finalCheck := fun s =>
    s.taskState 0 == some .ready && s.readyQ.contains 0 &&
    !(s.timedMailboxWaiters 7).contains 0 && s.waitDeadline 0 == none &&
    !s.timers.any (fun e => e.task == 0)
  covers := ["receiveUntil.park-then-tick-wakes", "tick.wakes-waitingTimed"]

def receiveUntil_message_before_deadline : BranchScenario where
  name := "receiveUntil_message_before_deadline"
  description := "receiveUntil with a message present returns it before the deadline"
  ops := [.spawn 7, .schedule, .inject 7 ⟨1, 100⟩, .receiveUntil 0 5]
  expected := [.spawned 0, .scheduled 0, .ok, .received ⟨0, none, ⟨1, 100⟩⟩]
  finalCheck := fun s =>
    s.taskState 0 == some .running && mailboxLen s 7 == 0
  covers := ["receiveUntil.message-before-deadline"]

def receiveByOccurrence_hit : BranchScenario where
  name := "receiveByOccurrence_hit"
  description := "receiveByOccurrence returns the envelope with the matching occurrence"
  ops := [.spawn 7, .schedule, .inject 7 ⟨1, 100⟩, .inject 7 ⟨2, 200⟩,
          .receiveByOccurrence 0 1]
  expected := [.spawned 0, .scheduled 0, .ok, .ok, .received ⟨1, none, ⟨2, 200⟩⟩]
  finalCheck := fun s => mailboxLen s 7 == 1 && s.taskState 0 == some .running
  covers := ["receiveByOccurrence.hit"]

def receiveByOccurrence_miss_parks : BranchScenario where
  name := "receiveByOccurrence_miss_parks"
  description := "receiveByOccurrence with no match parks the task in mailboxWaiters"
  ops := [.spawn 7, .schedule, .inject 7 ⟨1, 100⟩, .receiveByOccurrence 0 99]
  expected := [.spawned 0, .scheduled 0, .ok, .blocked]
  finalCheck := fun s =>
    s.taskState 0 == some .waiting && s.running == none &&
    (s.mailboxWaiters 7).contains 0
  covers := ["receiveByOccurrence.miss-parks"]

def receiveFrom_source_hit : BranchScenario where
  name := "receiveFrom_source_hit"
  description := "receiveFrom returns an envelope whose source matches"
  ops := [.spawn 7, .spawn 9, .schedule, .send 0 9 ⟨1, 100⟩, .complete 0,
          .schedule, .receiveFrom 1 7]
  expected := [.spawned 0, .spawned 1, .scheduled 0, .ok, .ok, .scheduled 1, .received ⟨0, (some 7), ⟨1, 100⟩⟩]
  finalCheck := fun s => mailboxLen s 9 == 0 && s.taskState 1 == some .running
  covers := ["receiveFrom.source-hit"]

def receiveFrom_source_miss_parks : BranchScenario where
  name := "receiveFrom_source_miss_parks"
  description := "receiveFrom with no matching source parks the task"
  ops := [.spawn 7, .spawn 9, .schedule, .send 0 9 ⟨1, 100⟩, .complete 0,
          .schedule, .receiveFrom 1 5]
  expected := [.spawned 0, .spawned 1, .scheduled 0, .ok, .ok, .scheduled 1, .blocked]
  finalCheck := fun s =>
    s.taskState 1 == some .waiting && (s.mailboxWaiters 9).contains 1
  covers := ["receiveFrom.source-miss-parks"]

def fail_marks_failed : BranchScenario where
  name := "fail_marks_failed"
  description := "fail moves a non-terminal task to .failed and removes it everywhere"
  ops := [.spawn 7, .schedule, .fail 0]
  expected := [.spawned 0, .scheduled 0, .ok]
  finalCheck := fun s =>
    s.taskState 0 == some .failed && !s.readyQ.contains 0 &&
    s.running == none && s.waitDeadline 0 == none
  covers := ["fail.marks-failed"]

def restartOne_spawns_replacement : BranchScenario where
  name := "restartOne_spawns_replacement"
  description := "restartOne spawns a FRESH replacement; the failed task is not revived"
  ops := [.spawn 7, .schedule, .spawnChild 0 9, .fail 1, .restartOne 0 1 9]
  expected := [.spawned 0, .scheduled 0, .spawned 1, .ok, .spawned 2]
  finalCheck := fun s =>
    s.taskState 2 == some .new && s.taskOwner 2 == some 9 &&
    s.taskParent 2 == some 0 && s.restartOf 2 == some 1 &&
    s.readyQ.contains 2 && s.taskState 1 == some .failed
  covers := ["restartOne.spawns-replacement"]

def closeActor_preserves_mailbox : BranchScenario where
  name := "closeActor_preserves_mailbox"
  description := "closeActor marks the actor closed and PRESERVES its mailbox contents"
  ops := [.spawn 7, .schedule, .inject 7 ⟨1, 100⟩, .closeActor 7]
  expected := [.spawned 0, .scheduled 0, .ok, .ok]
  finalCheck := fun s => s.actorStatus 7 == .closed && mailboxLen s 7 == 1
  covers := ["closeActor.preserves-mailbox"]

def shutdown_sets_status : BranchScenario where
  name := "shutdown_sets_status"
  description := "shutdown sets shuttingDown and is idempotent"
  ops := [.shutdown, .shutdown]
  expected := [.ok, .ok]
  finalCheck := fun s => s.runtimeStatus == .shuttingDown
  covers := ["shutdown.sets-status", "shutdown.idempotent"]

def stopWhenIdle_quiescent : BranchScenario where
  name := "stopWhenIdle_quiescent"
  description := "stopWhenIdle stops the runtime when quiescent"
  ops := [.stopWhenIdle]
  expected := [.ok]
  finalCheck := fun s => s.runtimeStatus == .stopped
  covers := ["stopWhenIdle.quiescent"]

def stopWhenIdle_nonquiescent : BranchScenario where
  name := "stopWhenIdle_nonquiescent"
  description := "stopWhenIdle is invalid (no-op) when work remains"
  ops := [.spawn 7, .stopWhenIdle]
  expected := [.spawned 0, .invalid]
  finalCheck := fun s => s.runtimeStatus == .running && s.readyQ.contains 0
  covers := ["stopWhenIdle.nonquiescent-invalid"]

def mesa_woken_task_can_repark : BranchScenario where
  name := "mesa_woken_task_can_repark"
  description := "a waiter woken by a delivery finds the message already consumed and re-parks (Mesa)"
  ops := [.spawn 7, .schedule, .spawnChild 0 7, .receive 0, .schedule,
          .inject 7 ⟨1, 100⟩, .receive 1, .complete 1, .schedule, .receive 0]
  expected := [.spawned 0, .scheduled 0, .spawned 1, .blocked, .scheduled 1, .ok, .received ⟨0, none, ⟨1, 100⟩⟩, .ok, .scheduled 0, .blocked]
  finalCheck := fun s =>
    s.taskState 0 == some .waiting && (s.mailboxWaiters 7).contains 0 &&
    s.running == none
  covers := ["receive.mesa-repark"]

/-! ## Negative / security scenarios (083 §Negative) -/

def non_running_send_invalid : BranchScenario where
  name := "non_running_send_invalid"
  description := "send by a task that is not running is invalid; the mailbox is unchanged"
  ops := [.spawn 7, .send 0 7 ⟨1, 100⟩]
  expected := [.spawned 0, .invalid]
  finalCheck := fun s => mailboxLen s 7 == 0
  covers := ["send.non-running-invalid"]
  negative := true

def unowned_receive_invalid : BranchScenario where
  name := "unowned_receive_invalid"
  description := "receive by an unspawned/unowned task is invalid"
  ops := [.receive 0]
  expected := [.invalid]
  finalCheck := fun s => s.taskState 0 == none
  covers := ["receive.unowned-invalid"]
  negative := true

def waiting_task_cannot_send : BranchScenario where
  name := "waiting_task_cannot_send"
  description := "a parked (.waiting) task cannot send (send needs .running)"
  ops := [.spawn 7, .schedule, .receive 0, .send 0 7 ⟨1, 100⟩]
  expected := [.spawned 0, .scheduled 0, .blocked, .invalid]
  finalCheck := fun s => s.taskState 0 == some .waiting && mailboxLen s 7 == 0
  covers := ["send.waiting-task-invalid"]
  negative := true

def waiting_task_cannot_receive : BranchScenario where
  name := "waiting_task_cannot_receive"
  description := "a parked task cannot receiveUntil (needs .running)"
  ops := [.spawn 7, .schedule, .receive 0, .receiveUntil 0 5]
  expected := [.spawned 0, .scheduled 0, .blocked, .invalid]
  finalCheck := fun s => s.taskState 0 == some .waiting
  covers := ["receiveUntil.non-running-invalid"]
  negative := true

def cancelled_task_not_schedulable : BranchScenario where
  name := "cancelled_task_not_schedulable"
  description := "a cancelled task is never selected by schedule"
  ops := [.spawn 7, .spawn 9, .cancel 0, .schedule]
  expected := [.spawned 0, .spawned 1, .ok, .scheduled 1]
  finalCheck := fun s =>
    s.taskState 0 == some .cancelled && s.running == some 1 &&
    !s.readyQ.contains 0
  covers := ["schedule.skips-cancelled", "cancel.removes-from-readyQ"]
  negative := true

def closed_actor_rejects_send : BranchScenario where
  name := "closed_actor_rejects_send"
  description := "send to a closed actor is invalid; the mailbox is unchanged"
  ops := [.spawn 7, .schedule, .closeActor 7, .send 0 7 ⟨1, 100⟩]
  expected := [.spawned 0, .scheduled 0, .ok, .invalid]
  finalCheck := fun s => s.actorStatus 7 == .closed && mailboxLen s 7 == 0
  covers := ["send.closed-actor-invalid"]
  negative := true

def closed_actor_rejects_inject : BranchScenario where
  name := "closed_actor_rejects_inject"
  description := "inject to a closed actor is invalid; the mailbox is unchanged"
  ops := [.spawn 7, .closeActor 7, .inject 7 ⟨1, 100⟩]
  expected := [.spawned 0, .ok, .invalid]
  finalCheck := fun s => s.actorStatus 7 == .closed && mailboxLen s 7 == 0
  covers := ["inject.closed-actor-invalid"]
  negative := true

def shutdown_rejects_spawn : BranchScenario where
  name := "shutdown_rejects_spawn"
  description := "spawn while shutting down is invalid"
  ops := [.shutdown, .spawn 7]
  expected := [.ok, .invalid]
  finalCheck := fun s => s.taskState 0 == none && s.runtimeStatus == .shuttingDown
  covers := ["spawn.shutdown-invalid"]
  negative := true

def shutdown_rejects_inject : BranchScenario where
  name := "shutdown_rejects_inject"
  description := "inject while shutting down is invalid; the mailbox is unchanged"
  ops := [.spawn 7, .shutdown, .inject 7 ⟨1, 100⟩]
  expected := [.spawned 0, .ok, .invalid]
  finalCheck := fun s => mailboxLen s 7 == 0 && s.runtimeStatus == .shuttingDown
  covers := ["inject.shutdown-invalid"]
  negative := true

def stale_timer_cannot_wake_cancelled : BranchScenario where
  name := "stale_timer_cannot_wake_cancelled"
  description := "cancel removes a sleeper's timer; a later tick never wakes the cancelled task"
  ops := [.spawn 7, .schedule, .sleep 0 5, .cancel 0, .tick 10]
  expected := [.spawned 0, .scheduled 0, .ok, .ok, .woke []]
  finalCheck := fun s =>
    s.taskState 0 == some .cancelled && !s.readyQ.contains 0 &&
    !s.timers.any (fun e => e.task == 0)
  covers := ["tick.never-wakes-cancelled", "cancel.removes-timer"]
  negative := true

def wake_moves_sleeper_to_ready : BranchScenario where
  name := "wake_moves_sleeper_to_ready"
  description := "wake moves a sleeping task directly to the ready queue"
  ops := [.spawn 7, .schedule, .sleep 0 5, .wake 0]
  expected := [.spawned 0, .scheduled 0, .ok, .ok]
  finalCheck := fun s =>
    s.taskState 0 == some .ready && s.readyQ.contains 0 &&
    !s.timers.any (fun e => e.task == 0)
  covers := ["wake.moves-sleeper-to-ready"]

def cancelTree_cancels_subtree : BranchScenario where
  name := "cancelTree_cancels_subtree"
  description := "cancelTree cancels the root and all its descendants"
  ops := [.spawn 7, .schedule, .spawnChild 0 7, .cancelTree 0]
  expected := [.spawned 0, .scheduled 0, .spawned 1, .ok]
  finalCheck := fun s =>
    s.taskState 0 == some .cancelled && s.taskState 1 == some .cancelled
  covers := ["cancelTree.cancels-subtree"]

/-- The full branch-coverage suite. -/
def branchScenarios : List BranchScenario :=
  [ receiveUntil_timeout_fast_path, receiveUntil_park_future_deadline,
    receiveUntil_park_then_tick_wakes, receiveUntil_message_before_deadline,
    receiveByOccurrence_hit, receiveByOccurrence_miss_parks,
    receiveFrom_source_hit, receiveFrom_source_miss_parks,
    fail_marks_failed, restartOne_spawns_replacement,
    closeActor_preserves_mailbox, shutdown_sets_status,
    stopWhenIdle_quiescent, stopWhenIdle_nonquiescent,
    mesa_woken_task_can_repark, wake_moves_sleeper_to_ready,
    cancelTree_cancels_subtree,
    non_running_send_invalid, unowned_receive_invalid,
    waiting_task_cannot_send, waiting_task_cannot_receive,
    cancelled_task_not_schedulable, closed_actor_rejects_send,
    closed_actor_rejects_inject, shutdown_rejects_spawn,
    shutdown_rejects_inject, stale_timer_cannot_wake_cancelled ]

def branchAllPass : Bool := branchScenarios.all checkBranch

/-- The scenarios whose runs kernel-reduce. `cancelTree` uses well-founded
    recursion (`descendantsOf`/`isInSubtreeOf`) that does not reduce under
    `decide`; it is covered by the executable runner (`branchAllPass`, run in
    `henret-conformance`) and by the `Supervision.lean` cascade-cancel proofs. -/
def kernelScenarios : List BranchScenario :=
  branchScenarios.filter (·.name != "cancelTree_cancels_subtree")

/-- Per-scenario report. -/
def branchReport : String :=
  String.intercalate "\n" (branchScenarios.map (fun sc =>
    if checkBranch sc then s!"PASS  {sc.name}"
    else s!"FAIL  {sc.name}  results={repr (runBranch sc).2}"))


/-- **Branch-coverage gate** — every kernel-reducible branch scenario's
    observed `StepResult` sequence equals its checked-in expected sequence and
    its final-state predicate holds. Kernel-checked by `decide` (no
    `native_decide`, so no extra axioms): any `step` change that alters a
    covered branch breaks this. (`cancelTree` is runtime-checked; see
    `kernelScenarios`.) -/
theorem branch_suite_passes : kernelScenarios.all checkBranch = true := by decide

end Henret.Conformance
