---
title: Blocked Waiting State and Mailbox Wait Queue
rfc: RFC-HENRET-031
status: Implemented (v0.5.0 core model; v0.5.1 acceptance criteria complete)
project: Henret
package: henret
namespace: Henret
depends: RFC 029 (blocked result), RFC 028 (queue exactness); RFC 034 recommended first
---

# RFC-HENRET-031: Blocked Waiting State and Mailbox Wait Queue

## Motivation

RFC 029 made an empty own-mailbox receive return `.blocked` — a legal
no-progress result, distinct from `.invalid`. But it is only a result
label: the task remains `running`, nothing is parked, and a driver that
sees `.blocked` has no model-level way to suspend the task until a
message arrives. The v0.4.0 review framed this as deliberately
transitional: "blocked receive is currently a no-op result, not a
waiting-state transition."

This RFC turns blocking into execution-management state: a blocked
receive parks the running task, and message delivery wakes a waiter.
This is what makes Henret's blocking model comparable to a real actor
runtime, and it is a prerequisite for any future selective-receive,
fairness, or progress claim.

## Design

### Representation: waiting state + per-actor wait queue (hybrid)

Two candidate representations were considered:

**(A) `TaskState.waiting` + `waitingOn : TaskId → Option ActorId`.**
Rejected as stated: under the actor-local receive discipline (RFC 024),
a task can only ever wait on its *own* actor's mailbox, so
`waitingOn t` would always equal `taskOwner t` — a redundant field whose
consistency would need its own invariant.

**(B) `mailboxWaiters : ActorId → List TaskId` alone.** Workable, but
the task's situation would be invisible in `taskState`, breaking the
model's convention that `taskState` is the authoritative lifecycle view
(sleeping tasks are visible both as `.sleeping` and as timer entries).

**Decision: hybrid — `TaskState.waiting` + `mailboxWaiters`.** This
mirrors the existing timer pattern exactly:

| domain | task state | side structure | coherence invariant |
|---|---|---|---|
| time   | `.sleeping` | `timers : List TimerEntry` | `timers_sleep` |
| messaging | `.waiting` (new) | `mailboxWaiters : ActorId → List TaskId` (new) | `waiters_waiting` (new) |

The symmetry is a maintainability argument: every proof pattern needed
here already exists in the timer corpus.

`TaskState.waiting` is non-terminal and **not** runnable
(`isRunnable = false`), so RFC 028's `runnable_queued` imposes no
obligation on waiting tasks, and `readyQ_queued` automatically excludes
them from the ready queue.

### Operational semantics

**Park (modified `receive` empty branch).** `receive t` with all guards
satisfied (running, `running` state, owned by `a`, mailbox exists) and
`mailbox.dequeue = none`:

```
taskState t      := some .waiting
running          := none
mailboxWaiters a := (mailboxWaiters a) ++ [t]     -- FIFO tail
result           := .blocked
```

The `.blocked` result label is retained; what changes is that it now
accompanies the parking transition.

**Wake-one on delivery (modified `send`/`inject` valid branches).**
When a message is delivered to actor `a` and `mailboxWaiters a = w :: ws`:

```
mailboxes a      := enqueue m                      -- delivery still happens
taskState w      := some .ready
readyQ           := readyQ ++ [w]
mailboxWaiters a := ws
```

With no waiters, delivery behaves as today.

**Wake-one, not wake-all.** One delivered message can satisfy exactly
one receive; waking all waiters causes a thundering herd in which all
but one immediately re-block. Wake-one FIFO is deterministic, fair in
arrival order, and keeps the woken-set reasoning trivial. (Recorded
alternative: wake-all is simpler to prove but semantically worse;
selective wake needs selective receive, out of scope.)

**Mesa semantics, not Hoare.** The woken task does **not** atomically
consume the message. It is made ready, must be scheduled, and re-issues
`receive`. If a sibling task of the same actor consumed the message
first, the re-issued receive blocks again — legal and well-defined.
Atomic handoff was rejected because it would make one task's operation
produce a result on behalf of a different task, breaking the
one-op-one-subject shape of `step` and most of the proof corpus.
Consequence (documented, not hidden): no per-message wake guarantee is
claimed — if a woken task is cancelled before consuming, the message
waits for the next delivery's wake. Liveness/fairness remain OUTSCOPE.

**`cancel` on a waiting task** removes it from its owner's waiter list
(exactly as cancel drops pending timers today). This keeps the waiter
list free of dead entries and the coherence invariant preservable.

**`wake t` remains sleeping-only.** Directly waking a waiting task
without a message would have it re-receive and immediately re-block —
operationally pointless. Recorded as a decided alternative; revisit if
timeout-receive is ever modeled (a task waiting with a deadline would
need exactly this composition).

## State and grammar changes

- `TaskState` += `| waiting` (every `cases st` proof gains one case).
- `RuntimeState` += `mailboxWaiters : ActorId → List TaskId`
  (init: `fun _ => []`).
- No new operation; `receive`, `send`, `inject`, `cancel` step cases
  change.

## Invariants (`WellFormed` += 3 fields, → 13)

```lean
  waiters_waiting :  -- soundness (parallel to timers_sleep)
    ∀ a t, t ∈ s.mailboxWaiters a → s.taskState t = some .waiting
  waiters_owned :    -- waiters wait on their OWN mailbox
    ∀ a t, t ∈ s.mailboxWaiters a → s.taskOwner t = some a
  waiting_queued :   -- completeness (parallel to runnable_queued)
    ∀ t, s.taskState t = some .waiting →
      ∃ a, s.taskOwner t = some a ∧ t ∈ s.mailboxWaiters a
```

plus `waiters_nodup : ∀ a, (s.mailboxWaiters a).Nodup` (needed for
"wake exactly one"). Note `waiters_owned` + `waiters_nodup` give
cross-actor uniqueness: a task in two different actors' lists would
have two owners.

## Headline theorems

- **`reachable_waiters_exact`** — the wait-queue analogue of RFC 028's
  queue exactness: in every reachable state,
  `t ∈ mailboxWaiters a ↔ taskState t = some .waiting ∧ taskOwner t = some a`.
- `receive_empty_parks` — guards + empty mailbox ⇒ the precise parking
  transition above (replaces the no-op claim).
- `deliver_wakes_head` — delivery to an actor with waiters `w :: ws`
  enqueues the message, readies exactly `w`, queues it, leaves `ws`.
- `cancel_unparks` — cancelling a waiting task removes it from its
  owner's waiter list.

## Breaking change, called out

**`step_blocked_unchanged` (RFC 029) is intentionally invalidated**: a
blocked receive now mutates state by design. The theorem is replaced by
`receive_empty_parks`; matrix row 47 is rewritten; the doc-symbol gate
forces the rename to propagate. The v0.4.0 review's "transitional"
framing (SF-04) was added precisely to license this change.

## Proof plan and cost

The most invasive change since RFC 024: one new `TaskState` constructor
(every state case analysis), one new `RuntimeState` field (projection
lemmas for all eleven operations that don't touch it), three new
`WellFormed` fields (preservation through all branches). All three new
preservation arguments have existing templates (timers_sleep,
runnable_queued, owned_has_mailbox). **RFC 034 should land first** so
the new sub-proofs go into a modular preservation structure rather than
growing the monolith past 1,000 lines.

## Out of scope

Selective receive; receive with timeout; wake-all or priority wake;
fairness/liveness ("a waiting task is eventually woken"); blocked sends
(mailboxes are unbounded).

## Acceptance criteria

- [ ] `reachable_waiters_exact` kernel-checked, audit-allowlisted.
- [ ] Demo: park → deliver → wake → scheduled re-receive consumes the
      message, end-to-end as a scenario.
- [ ] Non-running/unowned receive remains `.invalid` (untouched).
- [ ] All prior headlines re-proved over the new state.
