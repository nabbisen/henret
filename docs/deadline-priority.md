# Deadline & priority semantics (RFC 059)

Henret models per-task **priority** and **deadline** as optional scheduling
metadata, plus three metadata-driven policies built on the RFC 058 policy layer.

> **Not a real-time guarantee.** A deadline here is *logical-time ordering
> metadata only*. Henret makes **no** wall-clock or hard-real-time claim, and
> proves **no** theorem stating a deadline is met. Meeting a deadline would
> require a fairness/liveness policy, which this RFC deliberately does not add
> (see the negative example below). Scheduling deadlines are also kept distinct
> from timer deadlines (`receiveUntil`): the two never interact.

## Metadata

```lean
structure TaskMeta where
  priority : Nat        := 0
  deadline : Option Nat := none

taskMeta : TaskId → Option TaskMeta   -- field on RuntimeState; none ⇒ defaultMeta
```

Metadata is **optional** (RFC 059 non-goal: not every task must carry it). A
task without an entry is treated as `defaultMeta` (priority `0`, no deadline).

Conventions (resolving the RFC's review questions):
- **higher `priority` Nat = higher priority** (`priorityPolicy` picks the max);
- a **smaller `deadline` is more urgent**; a **missing deadline sorts last**;
- ties keep the earlier ready task (stable);
- metadata is **mutable** via the two operations and **persists** through
  terminal states (it is never cleared).

## Operations

```lean
| setPriority (t : TaskId) (p : Nat)   -- → .ok if t spawned, else .invalid
| setDeadline (t : TaskId) (d : Nat)   -- → .ok if t spawned, else .invalid
```

Both guard on `t` being spawned, so metadata is only ever attached to spawned
tasks. They touch only `taskMeta`, which is **not** part of `WellFormed`; hence
`preserves_wf_setPriority` / `preserves_wf_setDeadline` hold trivially (all 33
invariant fields are untouched). `taskMeta` is kept out of `WellFormed` on
purpose: a "every spawned task has metadata" invariant would contradict the
optional-metadata non-goal.

## Policies

All three are ordinary `SchedulingPolicy` values, so each inherits
`policyStep_preserves_wf` from RFC 058 (every policy preserves the full
invariant) and `policy_does_not_create_task`.

- `priorityPolicy` — highest priority first. `priority_policy_selects_max`
  proves the chosen ready task's priority is ≥ that of every ready task.
- `edfPolicy` — earliest deadline first (missing deadline last).
- `hybridPolicy` — priority first, deadline as tiebreak.

Each is proved **sound** (`choose_sound` via `pickBy_mem`: the chosen task is
always in `readyQ`).

### Worked selection (logical only)

Three spawned tasks `0,1,2` with priorities `1,5,3`: `priorityPolicy` selects
task `1`. With deadlines `9, none, 4`: `edfPolicy` selects task `2` (deadline
`4`); task `1` (no deadline) sorts last.

## Negative example — a deadline can be missed

Nothing in this RFC forces an urgent task to run. Suppose task `A` has deadline
`5` and task `B` has no deadline, both ready, and the active policy is FIFO (or
any non-EDF policy) with `B` ahead of `A`. The scheduler may run `B`
indefinitely, and logical time may advance past `5` (via `tick`) with `A` still
queued. This is **not** a bug in the model — it is the honest absence of a
liveness guarantee. EDF *orders* by deadline but, without a fairness policy,
does not *guarantee* the deadline is met. Henret states ordering facts only.

## Status

Soundness of all three policies and `priority_policy_selects_max` are proved.
The analogous EDF ordering-optimality theorem
(the EDF analogue of priority_policy_selects_max) requires transitivity/asymmetry lemmas
over the bespoke `Option Nat` deadline order and is tracked as a closeout
follow-up; the EDF *selection* is demonstrated by example in the meantime.
