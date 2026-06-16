---
rfc: 13
title: Runtime Invariants and Reachability
status: Implemented
implemented_in: v0.2.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: proofs
---

# RFC-HENRET-013: Runtime Invariants and Reachability

## Motivation

The v0.1.0 architecture review found that RFC 004's ownership-uniqueness claim
("a task appears in at most one ownership location") was stated but not proven.
More broadly, the model had per-operation theorems but no global invariant
discipline: nothing characterized what is true in *every reachable state*.

## Design

A single `WellFormed` predicate over `RuntimeState` with six fields:

```lean
structure WellFormed (s : RuntimeState) : Prop where
  readyQ_nodup  : s.readyQ.Nodup
  readyQ_queued : ∀ t ∈ s.readyQ, (s.taskState t).any TaskState.isRunnable = true
  running_runs  : ∀ t, s.running = some t → s.taskState t = some .running
  timers_nodup  : (s.timers.map TimerEntry.task).Nodup
  timers_sleep  : ∀ e ∈ s.timers, s.taskState e.task = some .sleeping
  fresh_none    : ∀ t, s.nextId ≤ t → s.taskState t = none
```

The key design decision: **location disjointness is derived, not stated**.
Each ownership location pins the task to a distinct lifecycle state (queued ⇒
runnable, running slot ⇒ `running`, timer ⇒ `sleeping`), and a task has
exactly one state — so a task can occupy at most one location. The corollaries
`ready_not_running`, `ready_no_timer`, `running_no_timer` make this explicit.

## Theorems

- `wf_init` — the initial state is well-formed.
- `step_preserves_wf` — all ten operations preserve well-formedness.
- `run_preserves_wf` / `reachable_wf` — **every reachable state is
  well-formed**.

This discharges the roadmap claim "the scheduler never duplicates a ready
task" (`readyQ_nodup` in every reachable state) and RFC 004's ownership
uniqueness as PROVEN.

## Acceptance criteria

- [x] `WellFormed` predicate with per-field documentation.
- [x] Preservation through all ten operations, kernel-checked.
- [x] Reachability corollary at `init`.
- [x] Disjointness corollaries derived from state uniqueness.
- [x] Axiom audit: `propext`, `Quot.sound` only.

## Implementation note (v0.2.0)

`Henret/Proofs/Invariants.lean` (predicate, helpers, `wf_init`, corollaries)
and `Henret/Proofs/InvariantsPreservation.lean` (the ten-operation
preservation grind, `run_preserves_wf`, `reachable_wf`). Split into two files
per the 300-ELOC guidance. Helper lemmas (`nodup_task_inj`,
`insertSorted_task_nodup`, `mem_map_insertSorted`) use Lean-core list lemmas
only — no Mathlib.
