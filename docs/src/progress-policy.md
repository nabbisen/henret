# Fairness and Conditional Liveness (RFC 046)

Henret's core is a **safety** model: `reachable_wf` proves reachable
states are well-formed, but says nothing about whether tasks make
progress. RFC 046 adds an **optional, separate** policy layer for
conditional liveness — without smuggling progress into `WellFormed`.

The guiding principle is honesty: *weak but honest progress is better
than attractive but false liveness*. Every progress statement here is
conditional on an explicit, named scheduling assumption.

## What is unconditional, and what is not

The model's `readyQ` is **FIFO**: `schedule` takes the head, and `yield`,
`spawn`, and wakeups append to the tail. So one fact is genuinely
unconditional and local:

```lean
theorem schedule_schedules_head
    (hrun : s.running = none) (hq : s.readyQ = t :: q)
    (hrunnable : (s.taskState t).any TaskState.isRunnable) :
    (step s .schedule).2 = .scheduled t
```

The head of the ready queue is always the next task scheduled. No
fairness assumption is needed for this step.

**Whole-program fairness is not unconditional.** An operation sequence
that simply stops issuing `schedule` starves every queued task. This is
representable and documented (see the unfair trace below).

## The bounded-fairness assumption

```lean
def BoundedReadyFair (k : Nat) (s : RuntimeState) (ops : List RuntimeOp) : Prop :=
  ∀ i t, runnableAtStep s ops i t →
    ∃ j, i ≤ j ∧ j ≤ i + k ∧ scheduledAtStep s ops j t
```

This is a property of the *operation sequence* (the scheduler's choices),
not of `WellFormed`. It says: every task runnable at some step is
scheduled within `k` further steps.

## The conditional progress theorem

```lean
theorem ready_eventually_scheduled_under_bounded_fairness
    (hfair : BoundedReadyFair k s ops) (hrun : runnableAtStep s ops i t) :
    ∃ j, i ≤ j ∧ j ≤ i + k ∧ scheduledAtStep s ops j t
```

This is deliberately close to tautological — its value is making the
assumption explicit and reusable, then tying it to concrete driver
policies later. It does **not** add any unconditional claim.

## Fair and unfair traces (kernel-checked)

A **fair** schedule gives each task a turn:

```lean
def fairOps := [.spawn 7, .spawn 9, .schedule, .complete 0, .schedule, .complete 1]
-- fair_task0_scheduled : task 0 scheduled at step 2
-- fair_task1_scheduled : task 1 scheduled at step 4
```

An **unfair** schedule starves a runnable task:

```lean
def unfairOps := [.spawn 7, .spawn 9, .schedule]
-- unfair_task1_runnable        : task 1 is runnable at step 3
-- unfair_task1_never_scheduled : task 1 is never scheduled
-- unfairOps_not_bounded_fair_0 : unfairOps does not satisfy BoundedReadyFair 0
```

The starvation is a genuine, representable property of the op sequence —
exactly the kind of dishonesty that a false unconditional liveness claim
would hide.

## Honesty ledger

Progress in Henret is **conditional**, classified as follows:

- **Unconditional, local**: the FIFO head is scheduled next
  (`schedule_schedules_head`).
- **Conditional**: whole-task progress under an explicit
  `BoundedReadyFair` assumption
  (`ready_eventually_scheduled_under_bounded_fairness`).
- **Representably false without the assumption**: starvation under an
  unfair op sequence (`unfairOps_not_bounded_fair_0`).

Nothing about progress is added to `reachable_wf`. The safety model and
the liveness layer remain cleanly separated.
