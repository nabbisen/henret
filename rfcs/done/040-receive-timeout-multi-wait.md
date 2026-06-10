# RFC 040 — Receive Timeout and Multi-Wait Semantics

**Status.** Implemented (v0.11.0)  
**Target version.** v0.11.0  
**Priority.** Medium  
**Track.** Advanced actor execution semantics  
**Depends on.** RFC 031 completed; RFC 036; RFC 042  
**Touches.** `TaskState`, `RuntimeOp`, timers, mailbox waiters, preservation proofs, examples, docs

## Summary

Add timeout-aware receive semantics via `receiveUntil (t deadline)`. A task waits
for a message with a deadline; whichever event arrives first — message delivery or
timer expiry — makes the task ready. Timeout result is modeled as a **wake cause**,
not yet as a task-local return value (deferred to a later RFC).

## Design decisions

### Separate timed-waiter queue

Timed-waiting tasks live in a NEW field `timedMailboxWaiters : ActorId → List TaskId`,
separate from `mailboxWaiters` (which retains only `.waiting` tasks).

**Rationale**: This preserves the `waiters_waiting` invariant intact (47 uses), avoiding
~47-site proof churn. The cost is that regular waiters are serviced before timed waiters
if both exist (explicit priority). Interleaved FIFO between the two types is deferred to
a later RFC.

### waitingTimed with side map

New `TaskState.waitingTimed` constructor (no inline payload). Deadline stored in
`waitDeadline : TaskId → Option Nat`. Keeps `isRunnable`/`isTerminal` as simple
pattern matches.

### timers_sleep generalized

Field 5 `timers_sleep` is broadened to cover both `.sleeping` and `.waitingTimed` timer
entries. The name is kept to minimize reference churn; the statement changes from
`→ .sleeping` to `→ .sleeping ∨ .waitingTimed`.

### Wake semantics

- **Message wins** (`send`/`inject`): check `mailboxWaiters` first; if empty, check head
  of `timedMailboxWaiters`. Waking a timed waiter also removes its timer entry and clears
  `waitDeadline`. Uses unconditional `timers.filter (· ≠ w)` (harmless no-op for regular
  waiters whose timers don't exist by invariant).
- **Timer wins** (`tick`): expired-timer tasks with state `.waitingTimed` are woken via
  generalized `wakeMany`, removed from `timedMailboxWaiters`, and have `waitDeadline`
  cleared. `wakeOne` is generalized to handle `.waitingTimed → .ready`.
- **Cancel** (`cancel`, `cancelTree`): clears `waitDeadline` for cancelled tasks.

### Timeout result

For v0.11.0: timeout only wakes the task. No task-local return value. When the task is
scheduled after a timeout, it can call `receive` to check whether a message arrived;
empty mailbox means it timed out. Task-local result memory deferred to RFC 045.

## New and changed definitions

### `Henret/Actor/Task.lean`
```lean
| waitingTimed   -- parked, waiting for a message with a deadline
```

### `Henret/Core/Result.lean`
```lean
| timedOut       -- receiveUntil returned immediately (deadline already past)
```

### `Henret/Scheduler/Op.lean`
```lean
| receiveUntil (t : TaskId) (deadline : Nat)
```

### `Henret/Scheduler/Model.lean` — `RuntimeState` new fields
```lean
timedMailboxWaiters : ActorId → List TaskId   -- .waitingTimed tasks per actor
waitDeadline        : TaskId → Option Nat     -- deadline for .waitingTimed tasks
```

### `receiveUntil` semantics
- Not running / no owner / no mailbox: `.invalid`
- Own mailbox non-empty: dequeue, return `.received env`
- `deadline ≤ s.now`: return `.timedOut` (no parking)
- `deadline > s.now` and own mailbox empty: park as `.waitingTimed`:
  - `taskState t := .waitingTimed`
  - `running := none`
  - append `t` to `timedMailboxWaiters owner`
  - insert timer `⟨deadline, t⟩` into timers
  - `waitDeadline t := some deadline`
  - result `.blocked`

## WellFormed changes (21 → 27 fields)

Field 5 broadened; 6 new fields added:

```lean
timers_sleep :  -- BROADENED
  ∀ e, e ∈ s.timers → s.taskState e.task = some .sleeping
                     ∨ s.taskState e.task = some .waitingTimed

timed_has_deadline :  -- NEW (field 22)
  s.taskState t = some .waitingTimed → ∃ d, s.waitDeadline t = some d

deadline_is_timed :  -- NEW (field 23)
  s.waitDeadline t = some d → s.taskState t = some .waitingTimed

timed_has_timer :  -- NEW (field 24)
  s.taskState t = some .waitingTimed → ∃ e ∈ s.timers, e.task = t

timed_is_waiter :  -- NEW (field 25)
  s.taskState t = some .waitingTimed → ∃ a, t ∈ s.timedMailboxWaiters a

timed_waiters_valid :  -- NEW (field 26)
  ∀ a u, u ∈ s.timedMailboxWaiters a → s.taskState u = some .waitingTimed

timed_waiters_nodup :  -- NEW (field 27)
  ∀ a, (s.timedMailboxWaiters a).Nodup
```

## New file: `Henret/Proofs/Timeout.lean`

Key theorems:
```lean
receiveUntil_parks_timed    -- empty mailbox + future deadline → taskState = .waitingTimed
receiveUntil_dequeues       -- non-empty mailbox → direct dequeue, no state change
receiveUntil_timedout       -- deadline ≤ now → returns .timedOut immediately
tick_wakes_timed_waiter     -- expired timer for .waitingTimed task → .ready
send_wakes_timed_waiter     -- no regular waiter, timed waiter head → .ready + timer removed
reachable_timed_waiter_coherence  -- reachable timed waiters satisfy all 6 new fields
```

## Bridge implications

`toQOps (.receiveUntil t d)`:
- Valid (parks): `[Pop 0]` — equivalent to descheduling the running task
- Valid (immediate dequeue/timeout): `[]`
- Invalid: `[]`

`tick` now also emits `Push 0 t` for expired `.waitingTimed` tasks (already handled by
the generalized tick QOp emission pattern from RFC 036).

## Acceptance criteria

- `receiveUntil` modeled; timed wait/timer/timedMailboxWaiter coherence preserved.
- Message-first and timer-first races are deterministic under sequential semantics.
- `reachable_wf` remains the headline invariant (27 fields).
- Zero `sorry`, zero project-specific axioms.
- Demo scenarios: message-before-deadline, timeout-before-message.
