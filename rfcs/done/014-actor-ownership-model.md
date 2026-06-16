---
rfc: 14
title: Actor Ownership Model
status: Implemented
implemented_in: v0.2.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC-HENRET-014: Actor Ownership Model

## Motivation

`spawn a` created actor `a`'s mailbox, but the task itself did not remember
its owning actor (v0.1.0 review must-fix 2). Future actor semantics —
actor-scoped receive, supervision, actor-wide cancellation — need the
ownership relation to exist in the state and to be stable.

## Design

A new `RuntimeState` field, mirroring `taskState`'s map shape:

```lean
taskOwner : TaskId → Option ActorId
```

`spawn a` sets `taskOwner t := some a` for the fresh task `t` in the same
update that sets `taskState t := some .new`. No other operation writes
`taskOwner`. A function map (not a richer `TaskRecord`) keeps the `upd`-based
proof style uniform; a record refactor remains possible later without
changing the theorems' content.

## Theorems

- `spawn_sets_owner` — spawn records the spawning actor.
- `step_preserves_owner` / `run_preserves_owner` — a spawned task's owner is
  immutable across any operation and any program.
- `step_preserves_spawned` — no operation un-spawns a task (`some` never
  returns to `none`); this is what makes ownership preservation inductive.

## Acceptance criteria

- [x] Ownership recorded at spawn.
- [x] Immutability proven at step and run level.
- [x] Demo regression checks (scenario 6).
- [x] Example 02 demonstrates `taskOwner`.

## Implementation note (v0.2.0)

`Henret/Scheduler/Model.lean` (field + spawn write),
`Henret/Proofs/Ownership.lean` (theorems). Actor-scoped receive and
supervision remain future RFCs; this RFC provides the substrate.
