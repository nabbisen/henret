# RFC 046 — Fairness and Conditional Liveness Layer

## Status

Proposed.

## Summary

Add an optional policy layer for conditional liveness and fairness reasoning.
Henret's core model is intentionally a safety model: it proves that reachable
states are well-formed, not that tasks always make progress. This RFC keeps that
separation intact while introducing explicit scheduling assumptions under which
progress theorems can be stated and proved.

## Motivation

Henret currently says, correctly, that fairness and liveness are out of scope for
the unconditional model. However, advanced runtime consumers will eventually ask:

- if a task remains runnable, is it eventually scheduled?
- if a timer expires, is the task eventually run?
- if a message wakes a waiter, does that waiter eventually get a chance to receive?
- under which scheduler policy are those statements true?

The right answer is not to smuggle progress into `WellFormed`. The right answer
is a separate policy layer.

## Non-goals

This RFC does not:

- claim liveness for arbitrary `List RuntimeOp` programs;
- prove fairness of C or OS threads;
- force Henret to choose a production scheduling algorithm;
- require infinite coinductive traces in the first implementation.

## Proposed design

### Finite policy first

Start with bounded finite progress theorems rather than infinite temporal logic.
Define policy predicates over traces produced by RFC 045.

```lean
structure SchedulePolicy where
  choosesRunnable : RuntimeState → TaskId → Prop
  respectsReadyQ  : Prop
  deterministic   : Prop := False
```

A simpler first version may use predicates only:

```lean
def EventuallyScheduledWithin
  (fuel : Nat) (t : TaskId) (ops : List RuntimeOp) : Prop := ...
```

### Weak fairness over finite windows

Define a bounded fairness predicate:

```lean
def BoundedReadyFair (k : Nat) (trace : List TraceEvent) : Prop :=
  ∀ t i, taskRunnableAt trace i t →
    ∃ j, i ≤ j ∧ j ≤ i + k ∧ scheduledAt trace j t
```

The exact representation depends on RFC 045 trace indexing.

### Conditional theorems

Examples:

```lean
theorem ready_eventually_scheduled_under_bounded_fairness :
  BoundedReadyFair k tr →
  runnableAt tr i t →
  ∃ j, i ≤ j ∧ j ≤ i + k ∧ scheduledAt tr j t
```

This theorem may look tautological at first. That is acceptable. The goal is to
make the assumption explicit and reusable, then later tie it to concrete driver
policies.

### Driver-specific liveness

For Henret's simple single-worker driver, prove stronger bounded progress:

```lean
theorem readyQ_round_robin_progress :
  WellFormed s →
  t ∈ s.readyQ →
  ∃ n, n ≤ s.readyQ.length ∧ scheduledByDriverWithin s t n
```

If current driver semantics are stack-like rather than round-robin, name the
policy accordingly. Do not overclaim fairness for LIFO if starvation is possible.

## Implementation tasks

1. Implement RFC 045 first or define a temporary event accessor.
2. Create `Henret/Progress/Policy.lean`.
3. Define finite trace indexing helpers.
4. Define runnable/scheduled/woken predicates over traces.
5. Define bounded fairness predicates.
6. Prove small conditional progress theorems.
7. Add driver-specific progress theorem only where valid.
8. Update honesty ledger: progress is conditional, not unconditional.
9. Add examples showing a fair trace and an unfair trace.

## Acceptance criteria

- Progress theorems require explicit policy assumptions.
- No unconditional liveness claim is added to `reachable_wf`.
- At least one unfair trace is representable and documented.
- At least one bounded progress theorem is kernel-checked.

## Risks

The first progress theorems may feel weak. That is acceptable. Weak but honest
progress is better than attractive but false liveness claims.
