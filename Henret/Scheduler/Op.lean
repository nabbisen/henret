import Henret.Core.Id
import Henret.Actor.Mailbox
import Henret.Resource.Ledger

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
  /-- The running task `t` attempts to dequeue one message from its own actor's
      mailbox with a deadline.

      - Non-empty mailbox: dequeue immediately, return `.received env`.
      - Empty mailbox, `deadline ≤ s.now`: return `.timedOut` (no parking).
      - Empty mailbox, `deadline > s.now`: park as `.waitingTimed`:
        - `taskState t := .waitingTimed`
        - `running := none`
        - append `t` to `timedMailboxWaiters (taskOwner t)`
        - insert timer `⟨deadline, t⟩` into `timers`
        - `waitDeadline t := some deadline`
        - result `.blocked`

      When scheduled after waking, the task calls `receive` to check whether
      a message arrived (non-empty mailbox = message won; empty = timed out).
      Task-local return-value modeling deferred to RFC 045. (RFC 040) -/
  | receiveUntil (t : TaskId) (deadline : Nat) : RuntimeOp
  /-- Selective receive by occurrence id (RFC 041).

      The running task `t` consumes the first envelope in its owning actor's
      mailbox whose `occurrence` equals `occ`, preserving the relative order
      of every other envelope. If no match is present the task parks in the
      ordinary `mailboxWaiters` list (Mesa-style, Option A): any future
      delivery wakes it and it re-runs the selective receive. Blocking is
      mailbox-level, not selector-level. -/
  | receiveByOccurrence (t : TaskId) (occ : MessageId) : RuntimeOp
  /-- Selective receive by source actor (RFC 041).

      The running task `t` consumes the first envelope in its owning actor's
      mailbox whose `source` equals `some src`, preserving the relative order
      of every other envelope. Parks in `mailboxWaiters` if no match
      (Option A). -/
  | receiveFrom (t : TaskId) (src : ActorId) : RuntimeOp
  /-- `fail t`: abnormally terminate a non-terminal task `t`, moving it to
      the `.failed` state and clearing its ready/waiter/timer locations.
      Distinct from `cancel` so supervisors can restart only failures
      (RFC 049). -/
  | fail (t : TaskId) : RuntimeOp
  /-- `restartOne parent failedChild actor`: one-for-one restart. The
      supervisor `parent` spawns a fresh replacement child for the failed
      `failedChild` (which must be `.failed` and parented by `parent`),
      owned by `actor`, recording restart provenance (RFC 049). -/
  | restartOne (parent : TaskId) (failedChild : TaskId) (actor : ActorId) : RuntimeOp
  /-- Close actor `a` to new admission (RFC 055): subsequent `send`/`inject`
      targeting `a` are rejected, but existing mailbox contents remain and
      may still be drained by `receive`. Invalid if `a` has no mailbox. -/
  | closeActor (a : ActorId) : RuntimeOp
  /-- Begin runtime shutdown (RFC 055): subsequent root `spawn`s and
      environment `inject`s are rejected. Existing tasks continue to drain.
      Idempotent. -/
  | shutdown : RuntimeOp
  /-- Transition the runtime to `stopped` **only if** it is quiescent
      (no running task, empty ready queue, no pending timers). Invalid
      otherwise (RFC 055). -/
  | stopWhenIdle : RuntimeOp
  /-- Transition the runtime to `stopped` **only if** it is quiescent **and**
      the resource ledger is fully drained (no `allocated`/`closing` resource).
      A drain-gated stop never leaves a resource leaked (RFC 087). -/
  | stopWhenDrained : RuntimeOp
  /-- Running task `t` acquires a fresh resource (RFC 057). -/
  | acquire (t : TaskId) : RuntimeOp
  /-- Actor `a` acquires a fresh **actor-owned** resource (RFC 091): a
      control-plane allocation guarded by runtime running status and actor
      existence. The resource outlives any single task and closes only when
      the actor is closed (`closeActor`). Invalid if the runtime is not
      running, the actor is closed, or `a` has no mailbox. -/
  | acquireActor (a : ActorId) : RuntimeOp
  /-- Actor `a` voluntarily releases its `allocated` actor-owned resource `r`
      (RFC 093). Control-plane and running-gated, symmetric with `acquireActor`.
      Invalid if the runtime is not running, `r` is not owned by `.actor a`, or
      `r` is not `allocated`. A closed actor's resources are `closing`, not
      `allocated`, so this only applies to a live actor's handle. -/
  | releaseActor (a : ActorId) (r : ResourceId) : RuntimeOp
  /-- Running task `t` releases its live resource `r` (RFC 057). -/
  | release (t : TaskId) (r : ResourceId) : RuntimeOp
  /-- The environment reclaims a `closing` resource `r` (RFC 057). -/
  | finalize (r : ResourceId) : RuntimeOp
  /-- Set spawned task `t`'s scheduling priority to `p` (RFC 059). -/
  | setPriority (t : TaskId) (p : Nat) : RuntimeOp
  /-- Set spawned task `t`'s logical deadline to `d` (RFC 059). -/
  | setDeadline (t : TaskId) (d : Nat) : RuntimeOp
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
