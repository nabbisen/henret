import Henret.Scheduler.Model
import Henret.Scheduler.Driver

namespace Henret.Examples

open Henret

/-- Render a task state for the demo output. -/
def showState : Option TaskState → String
  | none => "(never spawned)"
  | some .new => "new"
  | some .ready => "ready"
  | some .running => "running"
  | some .yielded => "yielded"
  | some .sleeping => "sleeping"
  | some .completed => "completed"
  | some .cancelled => "cancelled"
  | some .waiting => "waiting"
  | some .waitingTimed => "waitingTimed"
  | some .failed => "failed"

/-! ## Scenario 1 — task lifecycle: spawn, schedule, yield, complete -/

/-- Spawn one task for actor 0 and walk it through
`new → running → yielded → running → completed`. -/
def lifecycle : RuntimeState :=
  run .init [.spawn 0, .schedule, .yield 0, .schedule, .complete 0]

/-! ## Scenario 2 — send / receive through a mailbox -/

/-- Spawn actor 7's first task (creating its mailbox), schedule it,
have the running task send two messages to its own actor and receive
one (actor-local receive, RFC 024). Mailbox should hold exactly
message 2. -/
def mailboxScenario : RuntimeState × List StepResult :=
  runTrace .init
    [.spawn 7,           -- task 0, owned by actor 7
     .schedule,          -- task 0 running
     .send 0 7 ⟨1, 100⟩, -- running task 0 sends to actor 7
     .send 0 7 ⟨2, 200⟩,
     .receive 0]         -- task 0 receives from its OWN mailbox

/-! ## Scenario 3 — sleep and tick -/

/-- Two tasks; the first sleeps until t=10, the second until t=5.
A tick at t=7 must wake exactly the second. -/
def sleepTick : RuntimeState :=
  run .init
    [.spawn 0, .spawn 0,
     .schedule, .sleep 0 10,
     .schedule, .sleep 1 5,
     .tick 7]

/-! ## Scenario 4 — cancel -/

/-- Cancel a queued task; a later wake/schedule cannot revive it. -/
def cancelScenario : RuntimeState :=
  run .init [.spawn 3, .cancel 0, .wake 0, .schedule]

/-! ## Scenario 5 — the drivers -/

/-- Five tasks completed by the op-level round-robin driver. -/
def driven : RuntimeState :=
  driveOps 10 (run .init [.spawn 0, .spawn 0, .spawn 0, .spawn 0, .spawn 0])

/-- The same five tasks completed by the proved drain driver. -/
def drained : RuntimeState :=
  drain (run .init [.spawn 0, .spawn 0, .spawn 0, .spawn 0, .spawn 0])


/-! ## Scenario 8 — spawnChild (RFC 032) -/

/-- Root task spawns a child; verify parent chain terminates at none. -/
def spawnChildScenario : RuntimeState :=
  run .init [
    .spawn 3,       -- task 0 queued (owned by actor 3)
    .schedule,      -- task 0 running
    .spawnChild 0 3,-- task 0 spawns child task 1 (owned by actor 3)
    .complete 0]    -- task 0 completes

/-- The spawned child has task 0 as parent. -/
theorem spawnChild_parent_check :
    spawnChildScenario.taskParent 1 = some 0 := by native_decide

/-- The parent (task 0) was running (now completed after the last op). -/
theorem spawnChild_parent_was_running :
    spawnChildScenario.taskState 0 = some .completed := by native_decide

/-- Task 1 is queued as .new (spawnChild enqueues it). -/
theorem spawnChild_child_state :
    spawnChildScenario.taskState 1 = some .new := by native_decide

end Henret.Examples

/-!
# Henret.Examples.Basic

Small executable scenarios (RFC 011, first slice).

Each definition builds one scenario as a list of operations, runs it
through the model, and exposes observations the demo executable
prints and checks. Everything here is Lean-only and pure.
-/
