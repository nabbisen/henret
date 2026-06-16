---
rfc: 89
title: Sleeping-Timer Coherence (RFC 057 Tier 2 groundwork)
status: Implemented
implemented_in: v0.25.0
supersedes: []
superseded_by: []
depends_on: [57, 88]
blocks: []
category: model-semantics
---

# RFC 089 — Sleeping-Timer Coherence (RFC 057 Tier 2 groundwork)

## Status

Implemented (v0.25.0). Delivers the invariant and the `quiescent_no_sleeping`
corollary; multi-step drained permanence / "stopped stays quiescent" build on
it and are the next slice.

## Motivation

RFC 088 proved drained-state persistence only for a **single step**, and the
write-up was explicit about why: multi-step permanence needs `running = none`
to be preserved across a whole run, which in turn requires ruling out a `wake`
re-populating `readyQ` after a stop. A `wake` fires only on a *sleeping* task,
so the missing fact is: a runtime with an **empty timer queue has no sleeping
tasks**.

The model's `WellFormed` could not establish this. `WellFormed.timers_sleep`
records only the *converse* — every timer's task is `sleeping` or
`waitingTimed`. Nothing said a sleeping task must *have* a timer, so `timers =
[]` did not rule out a stranded sleeping task.

This RFC closes that gap.

## The invariant

```lean
def SleepingHasTimer (s : RuntimeState) : Prop :=
  ∀ t, s.taskState t = some .sleeping → ∃ e ∈ s.timers, e.task = t

theorem reachable_sleepingHasTimer (ops : List RuntimeOp) :
    SleepingHasTimer (run RuntimeState.init ops)
```

It is proven as a **standalone reachable invariant**, not a 34th `WellFormed`
field — keeping the change off every preservation file, mirroring RFC 057's
`reachable_released_resource_never_live`. The base case is trivial (`init` has
no tasks). Preservation (`step_preserves_sleepingHasTimer`) is by cases on all
27 operations; the shape of the argument:

- `sleep` is the only operation that introduces a sleeping task, and it
  registers a timer for exactly that task.
- Every timer-removing operation — `wake`, `tick`, `cancel`, `fail`,
  `cancelTree`, and `send`/`inject` when they wake a mailbox waiter —
  simultaneously moves the affected task *out* of `sleeping`. So a task that is
  still sleeping after the step kept its timer. (`tick` is the subtle case: a
  still-sleeping task was not woken, hence its timer was not expired, hence it
  survives in `Timer.remaining`.)
- No other operation creates a sleeping task or drops a timer.

## The payoff

```lean
theorem quiescent_no_sleeping (h : SleepingHasTimer s)
    (hq : RuntimeQuiescent s) (t : TaskId) : s.taskState t ≠ some .sleeping
```

A quiescent runtime (empty timer queue in particular) has no sleeping tasks.
This is exactly the fact a future slice needs to show `running = none` is
preserved across a run from a stopped state — turning RFC 088's single-step
drained persistence into full multi-step permanence, and giving a
"stopped stays quiescent" result.

## Scope and non-goals

This RFC delivers the invariant and the immediate corollary. It does **not**
yet prove multi-step drained permanence or "stopped stays quiescent" — those
build a `Frozen` bundle invariant on top of `quiescent_no_sleeping` and are the
next slice. Actor-owned resources, the breaking global `stopped → Drained`
invariant, and wall-clock liveness remain deferred (from RFC 087).

## Proof obligations

| Obligation | Theorem |
|---|---|
| No sleeping task in `init` | `sleepingHasTimer_init` |
| Every operation preserves the invariant | `step_preserves_sleepingHasTimer` |
| Holds across any run | `run_preserves_sleepingHasTimer`, `reachable_sleepingHasTimer` |
| Quiescent ⟹ no sleeping tasks | `quiescent_no_sleeping` |
