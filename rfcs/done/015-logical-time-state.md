---
rfc: 15
title: Logical Time State
status: Implemented
implemented_in: v0.2.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC-HENRET-015: Logical Time State

## Motivation

`tick now` was described as "advancing logical time", but `RuntimeState`
stored no clock, so `tick 100` followed by `tick 3` was accepted (v0.1.0
review must-fix 5). Either the name was wrong or the state was missing. The
state was missing.

## Design

```lean
now : Nat   -- in RuntimeState, init 0
```

`tick t` is guarded: valid iff `s.now ≤ t`, in which case it wakes expired
sleeping tasks and sets `now := t`. Equal time is allowed (an idempotent tick
wakes nothing new because prior expired entries are already gone). A
backwards tick returns `.invalid` and, per RFC 016, provably changes nothing.

`sleep t d` intentionally does not constrain `d` against `now`: a
past-deadline sleep simply wakes at the next valid tick.

## Theorems

- `tick_advances_clock` — a valid tick sets `now` exactly.
- `tick_backwards_invalid` — a backwards tick is invalid and a no-op.
- `step_clock_monotone` — no operation decreases the clock.

## Acceptance criteria

- [x] Clock stored; ticks monotone by construction.
- [x] All three theorems kernel-checked.
- [x] Existing timer theorems re-proved under the validity guard
      (`hle : s.now ≤ now` hypotheses).
- [x] Demo regression checks (scenario 6); example 05 updated.

## Implementation note (v0.2.0)

`Henret/Scheduler/Model.lean` (field + guard), `Henret/Proofs/Timers.lean`
(guarded re-proofs + the three new theorems).
