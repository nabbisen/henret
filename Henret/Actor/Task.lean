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

The runnable states are `new`, `ready`, and `yielded` — all three can be
scheduled directly (see `TaskState.isRunnable`).  The actual transitions
performed by `step`:

```
spawn    : (no task)            -> new       (+ enqueued)
schedule : new | ready | yielded -> running
yield    : running              -> yielded   (+ re-enqueued)
sleep    : running              -> sleeping  (+ timer registered)
wake     : sleeping             -> ready     (+ enqueued)
tick     : sleeping (expired)   -> ready     (+ enqueued)
complete : running              -> completed
cancel   : any non-terminal     -> cancelled (dequeued, timer dropped)
```

`completed` and `cancelled` are terminal: no operation of the model
moves a task out of them. This is not a convention but a theorem —
see `Henret.Proofs.Lifecycle.step_preserves_completed` and
`step_preserves_cancelled`.
-/
