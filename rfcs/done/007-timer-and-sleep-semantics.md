---
rfc: 7
title: Timer and Sleep Semantics
status: Implemented
implemented_in: v0.1.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC-HENRET-007: Timer and Sleep Semantics


## Motivation

Sleep/timer behavior is a compact and useful way to demonstrate actor/task runtime modeling without real OS I/O.

## Design

Define:

```lean
structure TimerEntry where
  at   : Nat
  task : TaskId
```

Represent time as logical ticks, not wall-clock time.

Required operations:

```text
sleep task deadline
tick now
wake expired tasks
leave future tasks sleeping
```

## Invariants

- Timer queue remains sorted if sortedness is selected.
- `tick now` does not wake timers with `at > now`.
- `tick now` wakes timers with `at <= now`.
- Woken task identity is exact.

## Tasks

1. Define timer entry.
2. Define timer queue.
3. Define sortedness predicate.
4. Implement insertion.
5. Implement tick.
6. Prove no early wake.
7. Prove expired wake.
8. Add sleep/tick example.

## Acceptance criteria

- A task can sleep and be woken by logical time.
- Timer behavior is model-level and Lean-only.

## Implementation note (v0.1.0)

TimerEntry uses field `deadline` (`at` is a Lean keyword). Sorted queue with insertSorted; proven tick_no_early_wake, tick_wakes_expired, tick_enqueues_woken, step/run_preserves_sorted.
