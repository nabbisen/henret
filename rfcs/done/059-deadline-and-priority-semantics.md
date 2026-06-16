---
rfc: 59
title: Deadline and Priority Semantics
status: Implemented
implemented_in: v0.22.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC 059 — Deadline and Priority Semantics

## Status

Implemented (v0.22.0). Policy soundness and `priority_policy_selects_max` are
proved; the EDF ordering-optimality theorem is a tracked closeout follow-up.

## Summary

Add explicit priority and deadline metadata and prove policy-specific ordering facts without claiming real-time guarantees.

## Motivation

Actor/task runtimes often need priorities and deadlines. Henret can model these as semantic ordering constraints. It should not claim wall-clock real-time behavior; deadlines are logical-time metadata only.

## Non-goals

- Do not claim hard real-time scheduling.
- Do not conflate timer deadlines with scheduling deadlines.
- Do not add priority inheritance in this RFC.
- Do not make every task require priority/deadline metadata.

## Design

Extend task metadata:

```lean
structure TaskMeta where
  priority : Nat
  deadline : Option Nat

taskMeta : TaskId → Option TaskMeta
```

Add operations:

```lean
| setPriority (t : TaskId) (p : Nat)
| setDeadline (t : TaskId) (d : Nat)
```

Define policies:

- highest-priority-first, stable among equals,
- earliest-deadline-first, stable among equals,
- hybrid priority-then-deadline.

## Formal model changes

- Add metadata consistency fields: metadata exists for spawned tasks.
- Decide whether metadata is immutable after spawn or mutable via explicit operations.

## Proof obligations

- `priority_policy_selects_max`
- `deadline_policy_selects_min_deadline`
- `metadata_spawned`
- `setPriority_preserves_wf`
- `setDeadline_preserves_wf`
- No theorem should claim deadline satisfaction without fairness assumptions.

## Tests and examples

- Demo: three tasks with priorities, selected order.
- Demo: deadline ordering using logical deadlines.
- Negative doc example: deadline missed is possible without liveness policy.

## Documentation updates

- Add warning: deadline is semantic ordering, not real-time guarantee.
- Update proof matrix with ordering claims only.

## Acceptance criteria

- Priority/deadline metadata is well formed.
- Built-in policies are sound.
- No real-time overclaim remains in docs.

## Risks and review questions

- Should lower Nat mean higher priority or the opposite?
- Should missing deadline sort last?
- Should cancelled/completed tasks retain metadata?
