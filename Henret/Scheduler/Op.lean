import Henret.Core.Id
import Henret.Actor.Mailbox

namespace Henret

/-- Operations of the actor/task runtime model. -/
inductive RuntimeOp where
  /-- Create a fresh task owned by actor `a` (creating the actor's
      mailbox if it does not exist) and queue it. -/
  | spawn (a : ActorId) : RuntimeOp
  /-- Select the head of the ready queue to run. -/
  | schedule : RuntimeOp
  /-- The running task `t` gives up the processor and is re-queued. -/
  | yield (t : TaskId) : RuntimeOp
  /-- The running task `t` finishes. Terminal. -/
  | complete (t : TaskId) : RuntimeOp
  /-- Cancel task `t` from any non-terminal state. Terminal. -/
  | cancel (t : TaskId) : RuntimeOp
  /-- Append message `m` to actor `a`'s mailbox. -/
  | send (a : ActorId) (m : Message) : RuntimeOp
  /-- Dequeue one message from actor `a`'s mailbox. -/
  | receive (a : ActorId) : RuntimeOp
  /-- The running task `t` sleeps until logical time `deadline`. -/
  | sleep (t : TaskId) (deadline : Nat) : RuntimeOp
  /-- Advance logical time to `now`, waking expired sleepers. -/
  | tick (now : Nat) : RuntimeOp
  /-- Wake the sleeping task `t` directly. -/
  | wake (t : TaskId) : RuntimeOp
deriving Repr, DecidableEq

end Henret

/-!
# Henret.Scheduler.Op

The operation grammar (RFC 005).

Every way the actor/task runtime can be driven is one constructor
here. The grammar is the single point of extension: a new runtime
capability means a new constructor plus its `step` case, its proofs,
and its matrix entry — never an ad-hoc state mutation elsewhere.
-/
