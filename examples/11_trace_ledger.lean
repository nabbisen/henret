import Henret
/-!
# Example 11 — Execution Trace Ledger (RFC 045)

`stepTrace` and `runTraceLedger` produce, alongside the ordinary
`(state, result)` effect, a list of semantic `TraceEvent`s: which task
was scheduled, which envelope was delivered, which task parked, which
timer fired.  The ledger agrees with `step`/`run` on state and result by
construction.

Run with:  `lake env lean examples/11_trace_ledger.lean`
-/
open Henret Henret.Trace

/-! ## A small scenario, with its trace -/

def trace : List RuntimeOp :=
  [ .spawn 7,            -- spawn task 0 for actor 7
    .spawn 9,            -- spawn task 1 for actor 9
    .schedule,           -- run task 0
    .inject 7 ⟨0, 100⟩,  -- environment delivers to actor 7
    .receive 0,          -- task 0 receives its head
    .receive 0,          -- task 0 receives again — mailbox empty → parks
    .sleep 1 5,          -- (task 1 isn't running, so this is invalid; shows an invalid event)
    .tick 10 ]           -- advance time

-- The event ledger of the whole run:
#eval (runTraceLedger RuntimeState.init trace).2.2
-- A readable list of TraceEvents: spawned 0 7, spawned 1 9, scheduled 0,
-- injected 7 0, received 0 7 0, parked 0 7, invalid (.sleep 1 5), ...

-- The per-op results, in order:
#eval (runTraceLedger RuntimeState.init trace).2.1

/-! ## The ledger agrees with `step` / `run` -/

-- PROVEN (by construction): stepTrace's state and result are exactly step's.
example (s : RuntimeState) (op : RuntimeOp) :
    (stepTrace s op).1 = (step s op).1 := stepTrace_state_eq_step s op

example (s : RuntimeState) (op : RuntimeOp) :
    (stepTrace s op).2.1 = (step s op).2 := stepTrace_result_eq_step s op

-- PROVEN (by induction): runTraceLedger's final state is exactly run's.
example (s : RuntimeState) (ops : List RuntimeOp) :
    (runTraceLedger s ops).1 = run s ops := runTraceLedger_state_eq_run s ops

/-! ## Events are sound

A `received` event certifies the dequeue actually happened. -/
example {s : RuntimeState} {t : TaskId} {a : ActorId} {occ : MessageId}
    (he : .received t a occ ∈ eventsOf s (.receive t)) :
    ∃ mb env mb',
      s.running = some t ∧ s.taskState t = some .running ∧
      s.taskOwner t = some a ∧ s.mailboxes a = some mb ∧
      mb.dequeue = some (env, mb') ∧ env.occurrence = occ :=
  event_received_sound he

-- A `parked` event certifies the receiver is now waiting and queued.
example {s : RuntimeState} {t : TaskId} {a : ActorId}
    (he : .parked t a ∈ eventsOf s (.receive t)) :
    ((step s (.receive t)).1).taskState t = some .waiting ∧
    t ∈ ((step s (.receive t)).1).mailboxWaiters a :=
  event_parked_sound he

#check @runTraceLedger_state_eq_run
#check @event_timerWoke_sound
