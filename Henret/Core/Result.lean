import Henret.Core.Id
import Henret.Actor.Mailbox

namespace Henret

/-- Result of applying one `RuntimeOp` to a `RuntimeState`. -/
inductive StepResult where
  /-- Operation applied; no interesting value. -/
  | ok : StepResult
  /-- `spawn` created this task. -/
  | spawned (t : TaskId) : StepResult
  /-- `schedule` selected this task to run. -/
  | scheduled (t : TaskId) : StepResult
  /-- `receive` dequeued this envelope (RFC 033). -/
  | received (e : Envelope) : StepResult
  /-- The operation was legal but cannot make progress now — currently
      produced only by `receive` on an empty own mailbox.  Distinct
      from `invalid`: a blocked receive is a normal actor condition
      (the task would wait for a message), not a protocol violation
      (RFC 029). -/
  | blocked : StepResult
  /-- `tick` woke these tasks (in timer order). -/
  | woke (ts : List TaskId) : StepResult
  /-- The operation was not valid in the current state.
      The state is guaranteed unchanged. -/
  | invalid : StepResult
deriving Repr, DecidableEq

end Henret

/-!
# Henret.Core.Result

Step results for the scheduler model (RFC 005).

Every operation produces a `StepResult`. Invalid operations leave the
state unchanged and return `.invalid` — option 1 of RFC 005's
invalid-operation policy. The model never silently mutates state on an
invalid operation; this is proved in `Henret.Proofs.Lifecycle`.
-/
