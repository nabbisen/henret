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
  /-- The running task `t` sends message body `m` to actor `b`'s mailbox.

      The delivered value is wrapped in an `Envelope` (RFC 033) stamped with:
      - `occurrence = s.nextMsgId`  — globally unique delivery identity
      - `source = taskOwner t`      — source actor provenance

      Guards: `t` is the running task in `.running` state, `t` has an
      owning actor, and `b`'s mailbox exists. -/
  | send (t : TaskId) (b : ActorId) (m : Message) : RuntimeOp
  /-- The running task `t` dequeues one message from its **own**
      actor's mailbox — the actor is derived from `taskOwner t`, never
      passed in. This is the actor-local receive discipline (RFC 024). -/
  | receive (t : TaskId) : RuntimeOp
  /-- Environment injection: append `m` to actor `a`'s mailbox with no
      task involvement. Models messages arriving from outside the
      modeled system. -/
  | inject (a : ActorId) (m : Message) : RuntimeOp
  /-- The running task `t` sleeps until logical time `deadline`.

      PAST-DEADLINE POLICY (explicit per RFC 029/SF-03): a deadline at
      or before the current clock is **legal**; the task simply wakes at
      the next valid `tick` (every tick time `≥ s.now` satisfies an
      expired deadline).  Rejecting or normalizing past deadlines was
      considered and recorded in RFC 029 as an alternative; the current
      policy keeps `sleep` total over deadlines and pushes all time
      reasoning into `tick`'s monotone guard. -/
  | sleep (t : TaskId) (deadline : Nat) : RuntimeOp
  /-- Advance logical time to `now`, waking expired sleepers. -/
  | tick (now : Nat) : RuntimeOp
  /-- Wake the sleeping task `t` directly. -/
  | wake (t : TaskId) : RuntimeOp
  /-- The running task `t` creates a fresh child task owned by actor `a`
      (creating the actor's mailbox if it does not exist) and queues it.
      The child records `t` as its parent (`taskParent child = some t`).
      Guards: `t` is the running task in `running` state with an owning
      actor. The child's actor `a` is unrestricted (same-actor and
      cross-actor spawning are both legal — RFC 032). -/
  | spawnChild (t : TaskId) (a : ActorId) : RuntimeOp
  /-- Cancel the task `root` and every descendant (tasks whose parent chain
      reaches `root`). All affected tasks move to `.cancelled`; they are
      removed from `readyQ`, `timers`, and `mailboxWaiters`. The `running`
      slot is cleared if it holds a task in the cancellation set.
      Mailbox contents and `taskOwner`/`taskParent` metadata are retained
      for auditability. Always succeeds (returns `.ok`) regardless of
      whether `root` is spawned. (RFC 039) -/
  | cancelTree (root : TaskId) : RuntimeOp
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
