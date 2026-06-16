---
rfc: 87
title: Resource Drain Discipline (RFC 057 Tier 2)
status: Implemented
implemented_in: v0.23.0
supersedes: []
superseded_by: []
depends_on: [57]
blocks: []
category: model-semantics
---

# RFC 087 — Resource Drain Discipline (RFC 057 Tier 2)

## Status

Implemented (v0.23.0). Safety/possibility slice; the breaking global
`stopped → Drained` invariant, actor-owned resources, and wall-clock liveness
remain deferred to later Tier-2 slices.

## Summary

The first slice of RFC 057 Tier 2: make resource *draining* a first-class,
provable part of the model. Two guarantees — (1) **drain progress**: from any
reachable state every `closing` resource can be finalized in one step, so a full
drain is always available; and (2) **drain-before-stop**: an additive
`stopWhenDrained` operation that reaches `stopped` only when the runtime is both
quiescent and fully drained, so a drained stop never leaves a resource leaked.

Both are ordinary safety / possibility facts in the existing `step`/`run`
paradigm. This RFC makes **no** wall-clock or timeliness claim.

## Motivation

RFC 057 Tier 1 gives the resource ledger (`allocated → closing → released`),
proves terminal task transitions mark owned resources `closing`
(`complete/cancel/fail/cancelTree_marks_owned_resource_closing`), and proves
`finalize` releases a `closing` resource. What it does *not* address is the
interaction with shutdown: `stopWhenIdle` transitions to `stopped` when
`running = none ∧ readyQ = [] ∧ timers = []` — a check that **ignores the
resource ledger**. A runtime can therefore reach `stopped` with resources still
`allocated` or `closing`, i.e. leaked. Tier 2 closes that gap on the safety
axis and states the drain-progress guarantee that Tier 1 implied but never
named.

## Non-goals

- **No wall-clock liveness or timeliness.** This RFC does not claim a resource
  *will* be finalized, only that finalization is always *available* and that a
  *drained* stop is *possible*. Guaranteeing the scheduler actually drains
  requires a fairness policy, which (per RFC 059) Henret does not provide.
- **No breaking change to `stopWhenIdle`.** Strengthening its guard to forbid an
  un-drained stop would make a previously-valid transition invalid and would
  require a global `stopped → Drained` invariant entangled with every operation
  that can fire after `stopped`. That stronger, breaking variant is deferred.
- **No actor-owned (longer-lived) resources.** Resources remain task-owned, as
  in Tier 1. Actor-scoped lifetimes are a later Tier-2 slice.
- **No new resource state.** `allocated/closing/released` is unchanged.

## Design

### The `Drained` predicate

```lean
def Drained (s : RuntimeState) : Prop :=
  ∀ r rr, s.resources r = some rr → rr.state = .released
```

A state is drained when no resource is still `allocated` or `closing`.

### Drain progress (no new operation)

A `closing` resource is always immediately finalizable:

```lean
theorem closing_finalize_releases (s) (r) (o)
    (h : s.resources r = some ⟨o, .closing⟩) :
    (step s (.finalize r)).2 = .ok ∧
    (step s (.finalize r)).1.resources r = some ⟨o, .released⟩
```

Combined with the Tier-1 "terminal marks closing" theorems, this means the
drain path is always open: a terminal task's resources become `closing`, and any
`closing` resource can be finalized.

### Drain-before-stop (additive operation)

A new operation, parallel to `stopWhenIdle`, that additionally requires the
ledger to be drained:

```lean
| stopWhenDrained : RuntimeOp
```

```lean
| .stopWhenDrained =>
    if s.running = none ∧ s.readyQ = [] ∧ s.timers = [] ∧
       (∀ r rr, s.resources r = some rr → rr.state = .released)
    then ({ s with runtimeStatus := .stopped }, .ok)
    else (s, .invalid)
```

It only ever changes `runtimeStatus`, so it preserves every `WellFormed` field
exactly as `stopWhenIdle` does. `stopWhenIdle` is left untouched.

## Proof obligations

- `closing_finalize_releases` (drain step always available) and a `reachable`
  packaging.
- `preserves_wf_stopWhenDrained` and its entry in the `reachable_wf` dispatcher
  (all 33 `WellFormed` fields).
- `stopWhenDrained_stops_drained`: if `stopWhenDrained` transitions to
  `.stopped`, then `Drained` held in the pre-state (the stop is drain-gated).
- Per-branch behaviour: `stopWhenDrained_stops` (quiescent ∧ drained → stops),
  `stopWhenDrained_noop` (otherwise a no-op / `.invalid`).
- No theorem asserts a resource is *eventually* finalized.

## Tests and examples

- Conformance: drain-then-`stopWhenDrained` succeeds; `stopWhenDrained` with a
  live (allocated/closing) resource is a no-op (`.invalid`).
- Demo: acquire → terminal (marks closing) → finalize (drains) → `stopWhenDrained`
  (stops), versus the same without finalize (stop refused).

## Documentation updates

- New `docs/resource-drain.md`: the two guarantees, the explicit non-liveness
  caveat, and the relationship to Tier 1.
- Proof matrix: drain-progress and drain-before-stop ordering/safety claims only.
- Migration note for the new operation.

## Acceptance criteria

- `Drained` defined; drain progress proven.
- `stopWhenDrained` added, preserves `WellFormed`, and is proven drain-gated.
- No wall-clock/liveness overclaim in docs.
- All `check.sh --fast` gates green; zero `sorry`; zero new axiom kinds.

## Risks and review questions

- Should `stopWhenIdle` eventually be strengthened (breaking) so that
  `stopped → Drained` holds globally, or should the drained stop stay opt-in?
- Should `Drained` be exposed as a `WellFormed`-adjacent reachable predicate, or
  remain a standalone definition used only by the stop guard and theorems?
- Is per-resource finalize the right drain primitive, or should a batch
  `drainAll` operation exist (deferred unless a theorem needs it)?
