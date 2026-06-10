import Henret.Progress.Policy
import Henret.Progress.Examples
/-!
# Henret.Progress  (RFC 046)

An **optional** policy layer for conditional liveness and fairness.

Henret's core stays a safety model — nothing here is added to
`WellFormed`, and no unconditional liveness is claimed.  Every progress
statement is conditional on an explicit, named scheduling assumption.

## Exports

- `Henret.Progress.runnableAtStep` / `scheduledAtStep` — trace-step predicates.
- `Henret.Progress.BoundedReadyFair` — the explicit bounded-fairness assumption.
- `Henret.Progress.ready_eventually_scheduled_under_bounded_fairness` —
  conditional progress under that assumption.
- `Henret.Progress.schedule_schedules_head` /
  `head_scheduled_within_one` — the unconditional FIFO head-progress fact.
- `Henret.Progress.fairOps` / `unfairOps` with kernel-checked witnesses,
  including `unfairOps_not_bounded_fair_0` (a representable starvation).

## Honesty

Progress is **conditional**, not unconditional.  The model's `readyQ` is
FIFO, so the head is always scheduled next (unconditional, local), but
whole-program fairness depends on the scheduler actually issuing
`schedule` ops — an op sequence that stops scheduling starves runnable
tasks, as `unfairOps` demonstrates.

See `docs/progress-policy.md`.
-/
