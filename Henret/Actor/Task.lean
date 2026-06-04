import Henret.Core.Id

namespace Henret

/-- Lifecycle state of one task. -/
inductive TaskState where
  /-- Spawned, queued, never scheduled yet. -/
  | new
  /-- Woken or otherwise re-queued; eligible to run. -/
  | ready
  /-- Currently selected by the scheduler. -/
  | running
  /-- Voluntarily gave up the processor; re-queued. -/
  | yielded
  /-- Waiting for a timer (`sleep` / `tick`) or explicit `wake`. -/
  | sleeping
  /-- Finished successfully. Terminal. -/
  | completed
  /-- Cancelled. Terminal. -/
  | cancelled
deriving Repr, DecidableEq, Inhabited

namespace TaskState

/-- Terminal states never transition again. -/
def isTerminal : TaskState → Bool
  | .completed => true
  | .cancelled => true
  | _ => false

/-- States from which `schedule` may select a queued task. -/
def isRunnable : TaskState → Bool
  | .new | .ready | .yielded => true
  | _ => false

@[simp] theorem isTerminal_completed : isTerminal .completed = true := rfl
@[simp] theorem isTerminal_cancelled : isTerminal .cancelled = true := rfl

end TaskState

/-- Per-task state map. `none` means the id was never spawned. -/
abbrev TaskMap := TaskId → Option TaskState

end Henret

/-!
# Henret.Actor.Task

Task lifecycle states (RFC 004).

```
new -> ready -> running -> yielded -> ready
new -> ready -> running -> sleeping -> ready
running -> completed
running -> cancelled / sleeping -> cancelled / ready -> cancelled
completed and cancelled are terminal
```

`completed` and `cancelled` are terminal: no operation of the model
moves a task out of them. This is not a convention but a theorem —
see `Henret.Proofs.Lifecycle.step_preserves_completed` and
`step_preserves_cancelled`.
-/
