import Henret.Scheduler.Model
/-!
  # Henret.Trace.Event  (RFC 045)

  A compact, semantic event vocabulary for execution traces.  Each
  constructor records a *semantic observation* about an operation — which
  task was scheduled, which envelope was delivered, which waiter was woken
  — not a low-level proof artifact.

  Events are produced by `stepTrace` (see `Henret.Trace.Run`), which is
  defined to agree with `step` on state and result by construction.
-/
namespace Henret.Trace

open Henret

/-- A semantic observation produced by one `step`.

    The vocabulary is intentionally small: one constructor per meaningful
    runtime observation.  `invalid` records a rejected operation;
    `noEffect` records a legal operation that produced no state change
    (e.g. a `receiveUntil` past-deadline fast path). -/
inductive TraceEvent where
  /-- An operation was rejected (guard failed). -/
  | invalid     (op : RuntimeOp)                                        : TraceEvent
  /-- `spawn`: task `t` created, owned by actor `a`. -/
  | spawned     (t : TaskId) (a : ActorId)                              : TraceEvent
  /-- `spawnChild`: `parent` created `child`, owned by actor `a`. -/
  | spawnChild  (parent child : TaskId) (a : ActorId)                   : TraceEvent
  /-- `schedule`: task `t` selected to run. -/
  | scheduled   (t : TaskId)                                            : TraceEvent
  /-- `yield`: task `t` yielded. -/
  | yielded     (t : TaskId)                                            : TraceEvent
  /-- `complete`: task `t` completed. -/
  | completed   (t : TaskId)                                            : TraceEvent
  /-- `cancel`/`cancelTree`: task `t` cancelled. -/
  | cancelled   (t : TaskId)                                            : TraceEvent
  /-- `sleep`: task `t` parked until `deadline`. -/
  | slept       (t : TaskId) (deadline : Nat)                           : TraceEvent
  /-- `tick`: timer at `now` woke task `t`. -/
  | timerWoke   (now : Nat) (t : TaskId)                                : TraceEvent
  /-- `wake`: task `t` directly woken. -/
  | directWoke  (t : TaskId)                                            : TraceEvent
  /-- `send`: `sender` delivered occurrence `occurrence` to actor `target`. -/
  | sent        (sender : TaskId) (target : ActorId) (occurrence : MessageId) : TraceEvent
  /-- `inject`: environment delivered occurrence `occurrence` to actor `target`. -/
  | injected    (target : ActorId) (occurrence : MessageId)            : TraceEvent
  /-- `receive*`: task `t` received occurrence `occurrence` from its own
      actor `actor`'s mailbox. -/
  | received    (t : TaskId) (actor : ActorId) (occurrence : MessageId) : TraceEvent
  /-- `receive*`: task `t` parked on actor `actor`'s empty/unmatched mailbox. -/
  | parked      (t : TaskId) (actor : ActorId)                          : TraceEvent
  /-- `send`/`inject`: delivery woke waiter `t` on actor `actor`. -/
  | waiterWoke  (actor : ActorId) (t : TaskId)                          : TraceEvent
  /-- A legal operation with no state change (carries its result). -/
  | noEffect    (op : RuntimeOp) (result : StepResult)                  : TraceEvent
deriving Repr, DecidableEq, Inhabited

end Henret.Trace
