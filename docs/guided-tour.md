# Guided Tour

Read top to bottom; each stop is small.

## 1. Run the demo

```bash
lake exe henret-demo
```

Six scenarios print their state and assert expected outcomes.

## 2. The operation grammar — `Henret/Scheduler/Op.lean`

`RuntimeOp` is the entire surface of the model — eleven operations:
`spawn a`, `schedule`, `yield t`, `complete t`, `cancel t`,
`send t b m` (the running task `t` sends to actor `b`),
`receive t` (the running task `t` dequeues from its **own** actor's
mailbox, derived from `taskOwner t` — never named by the caller),
`inject a m` (task-free environment delivery),
`sleep t deadline`, `tick now`, `wake t`.

The actor-local receive discipline is a theorem, not a convention:
`receive_only_own` proves that any successful receive dequeues the head
of the receiver's own actor's mailbox and touches no other mailbox
(RFC 024).

## 3. The state — `Henret/Scheduler/Model.lean`

`RuntimeState` holds a task-state map, a ready queue, an optional running
task, a sorted timer queue, mailboxes, and a fresh-id counter. `init` is the
empty state.

## 4. The semantics — `step`

`step : RuntimeState → RuntimeOp → RuntimeState × StepResult` is total and
executable. Each transition is guarded; invalid operations return the state
*unchanged* plus `.invalid`. Try it:

```lean
#eval (run .init [.spawn 7, .schedule, .yield 0]).taskState 0
-- some Henret.TaskState.yielded
```

## 5. The lifecycle — `Henret/Actor/Task.lean`

```text
spawn    : (no task)             -> new       (+ enqueued)
schedule : new | ready | yielded -> running   (from queue head)
yield    : running               -> yielded   (+ re-enqueued)
sleep    : running               -> sleeping  (+ timer)
wake/tick: sleeping              -> ready     (+ enqueued)
complete : running               -> completed
cancel   : any non-terminal      -> cancelled
completed and cancelled are terminal (a theorem, not a convention)
```

Note that `new` and `yielded` are themselves runnable: `schedule` takes the
queue head directly from any of the three runnable states; there is no
separate "promotion" of `new` to `ready`.

## 6. The flagship proof — `Henret/Proofs/Lifecycle.lean`

`step_preserves_terminal` walks all eleven operations and shows none of them can
move a task out of `completed`/`cancelled`. `run_preserves_terminal` lifts it
to whole programs by induction. Note *why* it holds: every state write goes
through `upd` at a guarded key, and every guard excludes terminal states.

## 7. Messages and timers — `Proofs/Messaging.lean`, `Proofs/Timers.lean`

`receive_consumes_one` (exactly the head), `send_appends` (exactly one tail
append), `tick_no_early_wake` / `tick_wakes_expired` (logical time is exact),
`run_preserves_sorted` (the timer queue invariant survives any program).

## 8. Blocked receive and mailbox wait queues — `Proofs/Messaging.lean`

`receive_empty_parks` and `receive_blocked_parks` (RFC 031) describe what
happens when a running task receives from an empty own mailbox: the task
enters `TaskState.waiting`, the running slot is cleared, and the task is
appended to its actor's `mailboxWaiters` queue. A later `send`/`inject` wakes
the head waiter to `.ready`.

**`mailboxWaiters` is a notification queue, not a mailbox-empty assertion.**
Under Mesa semantics, a delivery wakes at most one waiter; the woken task
must be rescheduled and re-issue `receive` to consume the message. Another
task of the same actor might consume it first, in which case the re-issued
receive parks again. Henret makes no liveness claim: a waiting task is
eventually woken only if a delivery occurs; no fairness policy is modelled.

`reachable_waiters_exact` is the exactness theorem for waiters (mirroring
`reachable_queue_exact` for the ready queue): in every reachable state,
`t ∈ mailboxWaiters a ↔ taskState t = .waiting ∧ taskOwner t = a`.

## 9. Drivers — `Henret/Scheduler/Driver.lean`

Two drivers: `driveOps` (op-level round-robin, fueled, TESTED) and `drain`
(model-level, with the PROVEN liveness theorem `drain_completes`).

## 9. The refinement pattern — `Henret/Refinement/`

`MailboxBackend σ` is a contract: operations plus observation laws over
`toList`. `listBackend` and `mailboxBackend` are reference implementations
whose laws are kernel-checked fields. Copy this shape for your own component —
see `docs/patterns/refinement-contract.md`.

## 10. The honesty ledger

Finish with `docs/proof-trust-test-matrix.md`: every claim is PROVEN, ASSUMED,
TESTED, or OUTSCOPE. That file is the project's contract with its readers.
