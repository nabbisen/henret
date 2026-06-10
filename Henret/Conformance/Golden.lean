import Henret.Conformance.Scenario
/-!
  # Henret.Conformance.Golden  (RFC 047)

  The ten golden conformance scenarios.  Each pairs an operation sequence
  with the canonical `TraceEvent` trace Henret produces, and a
  human-readable purpose.  The expected traces were obtained from the
  model and are checked in as the conformance reference.

  `goldenScenarios` is the full suite; `allPass` is the executable gate.
-/
namespace Henret.Conformance

open Henret Henret.Trace

/-- 1. Spawn a task, schedule it, complete it. -/
def spawn_schedule_complete : GoldenScenario where
  name := "spawn_schedule_complete"
  description := "spawn → schedule → complete: a task's basic lifecycle"
  ops := [.spawn 7, .schedule, .complete 0]
  expected := [.spawned 0 7, .scheduled 0, .completed 0]

/-- 2. A yielded task is requeued (returns to readyQ). -/
def yield_requeues : GoldenScenario where
  name := "yield_requeues"
  description := "a running task that yields is requeued"
  ops := [.spawn 7, .schedule, .yield 0]
  expected := [.spawned 0 7, .scheduled 0, .yielded 0]

/-- 3. A sleeping task is woken by a timer tick. -/
def sleep_tick_wakes : GoldenScenario where
  name := "sleep_tick_wakes"
  description := "sleep then tick past the deadline wakes the sleeper"
  ops := [.spawn 7, .schedule, .sleep 0 5, .tick 10]
  expected := [.spawned 0 7, .scheduled 0, .slept 0 5, .timerWoke 10 0]

/-- 4. A receive on an empty mailbox parks the task. -/
def empty_receive_parks : GoldenScenario where
  name := "empty_receive_parks"
  description := "receive on an empty own mailbox parks the task"
  ops := [.spawn 7, .schedule, .receive 0]
  expected := [.spawned 0 7, .scheduled 0, .parked 0 7]

/-- 5. A send wakes one waiter (Mesa semantics). -/
def send_wakes_waiter_mesa : GoldenScenario where
  name := "send_wakes_waiter_mesa"
  description := "send to an actor with a parked waiter wakes exactly that waiter"
  ops := [.spawn 7, .schedule, .spawnChild 0 7, .receive 0, .schedule, .send 1 7 ⟨0, 100⟩]
  expected :=
    [.spawned 0 7, .scheduled 0, .spawnChild 0 1 7, .parked 0 7,
     .scheduled 1, .sent 1 7 0, .waiterWoke 7 0]

/-- 6. An inject wakes one waiter (Mesa semantics). -/
def inject_wakes_waiter_mesa : GoldenScenario where
  name := "inject_wakes_waiter_mesa"
  description := "environment inject to an actor with a parked waiter wakes that waiter"
  ops := [.spawn 7, .schedule, .receive 0, .inject 7 ⟨0, 100⟩]
  expected :=
    [.spawned 0 7, .scheduled 0, .parked 0 7, .injected 7 0, .waiterWoke 7 0]

/-- 7. Cancelling a ready (queued) task. -/
def cancel_ready_task : GoldenScenario where
  name := "cancel_ready_task"
  description := "cancel a queued task removes it from the ready queue"
  ops := [.spawn 7, .spawn 9, .cancel 1]
  expected := [.spawned 0 7, .spawned 1 9, .cancelled 1]

/-- 8. Cancelling a waiting (parked) task. -/
def cancel_waiting_task : GoldenScenario where
  name := "cancel_waiting_task"
  description := "cancel a parked task removes it from the waiter list"
  ops := [.spawn 7, .schedule, .receive 0, .cancel 0]
  expected := [.spawned 0 7, .scheduled 0, .parked 0 7, .cancelled 0]

/-- 9. spawnChild records the parent. -/
def spawn_child_parent_lt : GoldenScenario where
  name := "spawn_child_parent_lt"
  description := "spawnChild creates a fresh child task whose id exceeds its parent's"
  ops := [.spawn 7, .schedule, .spawnChild 0 9]
  expected := [.spawned 0 7, .scheduled 0, .spawnChild 0 1 9]

/-- 10. Occurrence ids are fresh across two mailboxes. -/
def occurrence_unique_two_mailboxes : GoldenScenario where
  name := "occurrence_unique_two_mailboxes"
  description := "two sends to different actors get distinct fresh occurrence ids"
  ops := [.spawn 7, .spawn 9, .schedule, .send 0 7 ⟨0, 100⟩, .send 0 9 ⟨0, 200⟩]
  expected :=
    [.spawned 0 7, .spawned 1 9, .scheduled 0, .sent 0 7 0, .sent 0 9 1]

/-- The full golden suite (RFC 047 required scenarios). -/
def goldenScenarios : List GoldenScenario :=
  [ spawn_schedule_complete,
    yield_requeues,
    sleep_tick_wakes,
    empty_receive_parks,
    send_wakes_waiter_mesa,
    inject_wakes_waiter_mesa,
    cancel_ready_task,
    cancel_waiting_task,
    spawn_child_parent_lt,
    occurrence_unique_two_mailboxes ]

/-- The suite passes when every scenario's observed trace matches its
    golden expected trace. -/
def allPass : Bool :=
  goldenScenarios.all checkScenario

/-- A full pass/fail report, one line per scenario. -/
def suiteReport : String :=
  String.intercalate "\n" (goldenScenarios.map scenarioReport)

/-- **Conformance gate** — every golden scenario's observed trace equals
    its checked-in expected trace.  Kernel-checked by `decide` (no
    `native_decide`, so no extra axioms).  Any change to `step` or
    `traceEvents` that alters observable behavior breaks this proof. -/
theorem conformance_suite_passes : allPass = true := by decide

end Henret.Conformance
