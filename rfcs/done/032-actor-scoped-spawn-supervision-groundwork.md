---
rfc: 32
title: Actor-Scoped Spawn and Supervision Groundwork
status: Implemented
implemented_in: v0.6.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC-HENRET-032: Actor-Scoped Spawn and Supervision Groundwork

## Motivation

RFC 024 made messaging actor-local, but `spawn` is still purely an
environment operation: tasks appear with no record of *who* created
them. The v0.4.0 review: "the actor-locality story is not complete;
parent-task spawn is the right next semantic step." Parenthood is the
substrate every supervision feature stands on — cascade cancel, restart
policies, supervision trees — and none of those can be modeled, let
alone proved, without it.

This RFC adds the parenthood relation and its invariants. It is
*groundwork*: supervision semantics themselves (cascading cancel,
restarts) are explicitly deferred.

## Design

### Two spawn paths, mirroring the messaging design

RFC 024 split message delivery into a task-scoped path (`send`) and an
environment path (`inject`). Task creation gets the same treatment:

```lean
| spawn      (a : ActorId)              -- environment creates a ROOT task
| spawnChild (t : TaskId) (a : ActorId) -- running task t creates a CHILD
```

`spawn` is unchanged and remains necessary — root tasks must come from
somewhere, and demos/tests/initial system setup are environment acts.
A task created by `spawn` has no parent (it is a root).

**Guards for `spawnChild t a`** (consistent with `send`): `t` is the
running task, in `running` state, with an owning actor. The child's
actor `a` is unrestricted — same-actor and cross-actor spawning are
both legal; restricting to same-actor is a policy choice above the
model (recorded alternative; Erlang permits cross-"actor" spawn).

**Effect**: identical to `spawn` (fresh id `n = nextId`, state `.new`,
owner `a`, mailbox ensured, queued, `nextId + 1`) plus
`taskParent n := some t`. Result `.spawned n`.

### State

```lean
taskParent : TaskId → Option TaskId   -- init: fun _ => none
```

Written exactly once per task, by `spawnChild`, at creation. `none`
means root (created by `spawn`) or unspawned — disambiguated by
`taskState`, exactly as `taskOwner` is.

### Acyclicity for free: the `parent_lt` invariant

The reviewer asked for "parent tree is acyclic, if feasible." It is
feasible without any graph theory, by exploiting fresh-id monotonicity:

> At `spawnChild t a` time, the parent `t` is spawned, so `t < nextId`
> (contrapositive of `fresh_none`). The child *is* `nextId`. Therefore
> **every parent has a strictly smaller id than its child**:

```lean
  parent_lt : ∀ t p, s.taskParent t = some p → p < t
```

Acyclicity is then a corollary of well-foundedness of `<` on `Nat`: any
parent chain `t > p > p' > ...` strictly decreases and must terminate
at a root in at most `t` steps. No inductive tree structure, no
path-tracking — the id discipline already proves it. This is the same
move that made RFC 019's ownership invariants cheap: lean on `fresh_none`.

## Invariants (`WellFormed` += 2 fields)

```lean
  parent_lt :       -- acyclicity carrier
    ∀ t p, s.taskParent t = some p → p < t
  parent_spawned :  -- parents are real tasks
    ∀ t p, s.taskParent t = some p → ∃ st, s.taskState p = some st
```

A third candidate, `child_spawned` (only spawned tasks have parents,
i.e. `taskParent t = some p → ∃ st, taskState t = some st`), is
implied operationally but is cheap and makes `taskParent` self-
describing like `taskOwner`; include it unless preservation cost
surprises (decide at implementation, record outcome here).

Note `parent_spawned` is *stable* even though tasks terminate: terminal
tasks keep their `taskState` entry (`.completed`/`.cancelled`), so a
parent finishing does not invalidate the field. This is why the field
demands spawnedness, not aliveness — demanding a live parent would be
unpreservable under `complete`.

## Theorems

- `spawnChild_sets_parent`, `spawnChild_sets_owner`,
  `spawnChild_queues_child` — creation effects, mirroring the `spawn`
  theorem family.
- Guard theorems: `spawnChild_not_running_invalid`,
  `spawnChild_unowned_invalid` — only a running actor task spawns
  children.
- `step_preserves_parent` / `run_preserves_parent` — parenthood is
  immutable (mirrors owner immutability, RFC 014).
- **`reachable_parent_lt`** — headline; with it:
- **`parent_chain_terminates`** — every parent chain from a task `t`
  reaches a root in at most `t` steps (stated via an explicit
  fuel-indexed `ancestor` function: `ancestor s t (t+1)` reaches a
  fixed point with `taskParent = none`). This is the acyclicity
  deliverable in executable, checkable form.
- `reachable_parent_spawned` — projection of the invariant.

## Proof plan and cost

One new operation (grammar → 12; every full case analysis gains a
branch — but the `spawnChild` branch is a near-copy of `spawn`'s, the
best-understood branch in the corpus). One new state field (projection
lemmas: no operation except `spawnChild` touches it — eleven one-line
`@[simp]` lemmas, the RFC 024 pattern). Two or three new `WellFormed`
fields, each with a `fresh_none`-style preservation argument.
**RFC 034 first** for the same reason as RFC 031.

Independent of RFC 031 (no shared state or semantics); if both land,
implement serially in either order — textual conflicts are limited to
the shared case-analysis scaffolding.

## Out of scope (the supervision RFCs this enables)

Cascading cancel (cancelling a parent cancels descendants); restart
policies; supervisor strategies; linking/monitoring; exit signals.
Each becomes provable once `parent_lt` exists: e.g. cascade-cancel
termination is induction on the same decreasing measure.

## Acceptance criteria

- [ ] `reachable_parent_lt` and `parent_chain_terminates`
      kernel-checked, audit-allowlisted.
- [ ] Parent immutability through all twelve operations.
- [ ] Demo: environment root spawns a child via a scheduled task;
      the parent chain prints and terminates at the root.
- [ ] `spawn` behavior byte-identical for existing scenarios.
