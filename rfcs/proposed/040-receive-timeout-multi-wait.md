# RFC 040 — Receive Timeout and Multi-Wait Semantics

**Status.** Proposed  
**Target version.** v0.11.0  
**Priority.** Medium  
**Track.** Advanced actor execution semantics  
**Depends on.** RFC 031 completed; RFC 036 recommended; RFC 039 optional  
**Touches.** `TaskState`, `RuntimeOp`, timers, mailbox waiters, preservation proofs, examples, docs

## Summary

Add timeout-aware receive semantics. A task may wait for a mailbox message with a deadline, and the first event wins:

1. message delivery wakes the task before deadline, or
2. timer expiration wakes the task with timeout result.

This RFC is subtle because it composes the two side structures Henret currently keeps separate:

- `mailboxWaiters : ActorId → List TaskId`
- `timers : List TimerEntry`

The design must preserve `WellFormed` and avoid duplicate wakeups.

## Motivation

Real actor runtimes need operations like:

```text
receive message, but do not wait forever
```

Henret already models waiting and sleeping separately. Timeout receive is the first feature that requires a task to be registered in both the mailbox-wait domain and the timer domain.

This will make Henret's execution-management character significantly more sophisticated.

## Key design question

Can one task be in two side structures at once?

Current Henret shape treats side structures as coherence witnesses:

- `.sleeping` task appears in timers;
- `.waiting` task appears in mailboxWaiters.

Timeout receive needs a combined state.

## Proposed state model

Add a new task state:

```lean
| waitingUntil (deadline : Nat)
```

or, if constructors cannot carry payloads conveniently for current proofs:

```lean
| waitingTimed
```

with a separate map:

```lean
waitDeadline : TaskId → Option Nat
```

### Recommendation

Use explicit side map if proof ergonomics are better:

```lean
TaskState.waitingTimed
waitDeadline : TaskId → Option Nat
```

Reason: many existing proofs compare `TaskState` by equality. A payload constructor may complicate `isRunnable`, terminal-state lemmas, and projections.

## New operation

```lean
| receiveUntil (t : TaskId) (deadline : Nat)
```

Semantics:

- If `t` is not running: `.invalid`, no state change.
- If `t` has no owner: `.invalid`, no state change.
- If own mailbox has a message: dequeue and return `.received env`.
- If own mailbox is empty and `deadline ≤ s.now`: return `.timeout`, with no parking.
- If own mailbox is empty and `deadline > s.now`: park task as timed waiter:
  - `taskState t := .waitingTimed`
  - `running := none`
  - append `t` to `mailboxWaiters owner`
  - insert timer `⟨deadline, t⟩`
  - `waitDeadline t := some deadline`
  - result `.blocked`

## New StepResult

Add:

```lean
| timeout (t : TaskId)
```

or just:

```lean
| timeout
```

Recommendation: use `timeout t` only if existing result style carries subject ids. Otherwise keep result minimal.

## Wake semantics

### Message wins

When `send` or `inject` wakes a timed waiter:

- taskState becomes `.ready`;
- task is appended to `readyQ`;
- task is removed from `mailboxWaiters` head;
- its timer entry is removed;
- `waitDeadline t := none`.

This prevents a later tick from waking it again.

### Timer wins

When `tick now` expires a timed waiter:

- taskState becomes `.ready` or a separate `.readyTimedOut` state;
- task is appended to `readyQ`;
- task is removed from `mailboxWaiters`;
- timer entry is removed;
- `waitDeadline t := none`;
- no message is consumed.

The next scheduled action may inspect state/result? Since Henret's `step` result is per-operation and not stored, modeling a timeout result for the task is tricky.

### Recommended first design

Use a timeout inbox signal rather than hidden result memory:

```lean
Envelope.source = none
Envelope.body = timeoutMarker
```

This is ugly because it pollutes mailbox semantics.

Better first design:

Add a per-task pending result map:

```lean
pendingWake : TaskId → Option WakeReason

inductive WakeReason where
  | messageAvailable
  | timedOut
  | directWake
```

But this expands the model.

### Minimal acceptable design

For the first RFC, timeout only wakes the task; it does not deliver a result to the task. The theorem says the task becomes schedulable after deadline. A later RFC can model task-local result memory.

Document clearly:

```text
Timeout is modeled as a wake cause, not yet as a value returned into user code.
```

## New invariants

If using `waitingTimed` and `waitDeadline`:

```lean
timed_waiters_have_deadline :
  s.taskState t = some .waitingTimed → ∃ d, s.waitDeadline t = some d

deadline_waiters_waiting :
  s.waitDeadline t = some d →
    s.taskState t = some .waitingTimed

timed_waiters_have_timer :
  s.taskState t = some .waitingTimed → ∃ e, e ∈ s.timers ∧ e.task = t

timer_waiter_coherence :
  e ∈ s.timers → s.taskState e.task = some .sleeping ∨ s.taskState e.task = some .waitingTimed
```

Existing `timers_sleep` must be generalized because timer entries may now target sleeping or timed-waiting tasks.

## Theorems

```lean
receiveUntil_empty_parks_timed : ...
receiveUntil_ready_message_dequeues : ...
send_wakes_timed_waiter_removes_timer : ...
tick_times_out_waiter_removes_mailbox_waiter : ...
timed_waiter_no_double_wake : ...
reachable_timed_waiter_coherence : ...
```

## Bridge implications

Timeout wake has readyQ effects similar to `tick` and `send/inject` wake-one. After RFC 036, bridge translation should emit `Push 0 t` when timeout wakes a task.

## Examples

Add at least two scenarios:

1. message before deadline:
   - receiveUntil parks;
   - inject sends message;
   - waiter wakes;
   - timer removed;
   - no duplicate wake on later tick.

2. timeout before message:
   - receiveUntil parks;
   - tick reaches deadline;
   - waiter wakes;
   - waiter removed from mailboxWaiters;
   - later inject does not wake the same task twice.

## Acceptance criteria

- `receiveUntil` is modeled.
- Timed wait state is explicit.
- Timed wait/timer/mailboxWaiter coherence is preserved.
- Message-first and timer-first races are deterministic under sequential semantics.
- No duplicate readyQ entry is possible.
- `reachable_wf` remains the headline invariant.
- Public docs state whether timeout result is modeled as a wake cause or task-local return value.

## Risks

### Result modeling

Henret's step model does not currently store task-local return values. Timeout semantics can expose this limitation. Do not overcomplicate the first implementation; document the model boundary.

### Invariant churn

Generalizing timer invariants will touch many proofs. RFC 042 proof automation may be worth implementing before this RFC if proof size becomes excessive.

## Non-goals

- Selective receive.
- Fairness or liveness.
- OS wall-clock time.
- Multi-worker timer placement.
