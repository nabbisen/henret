---
rfc: 68
title: Invariant Dependency Graph
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: proofs
---

# RFC 068 — Invariant Dependency Graph

## Status

Proposed strategic RFC.

## Summary

Document and optionally encode dependencies among `WellFormed` fields and derived theorems. The goal is to help maintain the growing invariant corpus and make review easier.

## Motivation

Henret's `WellFormed` invariant has grown to many fields. Derived theorems such as queue exactness, waiter exactness, occurrence uniqueness, and parent chain termination rely on combinations of fields. Reviewers and maintainers need to know which fields support which claims.

Without a dependency graph, later changes may accidentally break a theorem's conceptual basis even if proof scripts are repaired mechanically.

## Goals

- Build a human-readable invariant dependency graph.
- Identify direct vs derived claims.
- Distinguish preservation obligations from derived corollaries.
- Prepare for automated documentation extraction.

## Non-goals

- Do not replace Lean dependency analysis.
- Do not require fully machine-generated proof dependency graphs in the first version.
- Do not expose internal helper lemmas as public API solely because they appear in the graph.

## Proposed document structure

`docs/invariant-dependency-graph.md`:

```text
WellFormed.readyQ_queued
WellFormed.runnable_queued
WellFormed.readyQ_nodup
  -> reachable_queue_exact

WellFormed.waiter_is_waiting
WellFormed.waiting_has_owner
WellFormed.waiter_actor_unique
WellFormed.waiters_nodup
  -> reachable_waiters_exact

WellFormed.parent_lt
  -> reachable_parent_lt
  -> parent_chain_terminates

WellFormed.occ_fresh
WellFormed.occ_nodup
WellFormed.occ_disjoint
  -> reachable_occurrence_unique
```

## Optional Lean representation

```lean
inductive InvariantId where
  | readyQ_queued
  | runnable_queued
  | readyQ_nodup
  | waiters_waiting
  | waiting_has_owner
  | waiter_actor_unique
  | waiters_nodup
  | parent_lt
  | occ_fresh
  | occ_nodup
  | occ_disjoint

structure DerivedClaim where
  name : String
  dependencies : List InvariantId
```

This representation is documentation-friendly and can be exported later.

## Design note

The graph should describe conceptual dependency, not exact proof-script dependency. A theorem may use helper lemmas, but the graph should show which semantic invariant fields justify the public claim.

## Concerns

- The graph can drift if maintained manually.
- Naming of `WellFormed` fields must be stable.
- Generated graph from proof terms may be too noisy.

## Implementation tasks

1. Create `docs/invariant-dependency-graph.md`.
2. Add a table mapping each public derived theorem to invariant fields.
3. Add a release checklist item requiring graph update when `WellFormed` changes.
4. Optionally add a Lean data table under `Henret/Docs/InvariantGraph.lean`.
5. Update proof index to link each theorem to graph entries.

## Acceptance criteria

- Every headline theorem lists its conceptual invariant dependencies.
- Every `WellFormed` field is referenced by at least one direct preservation obligation or marked as foundational.
- Reviewers can understand why each invariant exists.
