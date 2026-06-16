---
rfc: 92
title: Clean-Stop Predicate (stopped → Drained resolution)
status: Implemented
implemented_in: v0.28.0
supersedes: []
superseded_by: []
depends_on: [55, 57, 87, 90, 91]
blocks: []
category: model-semantics
---

# RFC 092 — Clean-Stop Predicate (stopped → Drained resolution)

## Status

**Implemented in v0.28.0.** Resolves the last deferred item of the RFC 057
Tier 2 *safety* thread — whether `runtimeStatus = .stopped` should globally imply
`Drained`. Per the architect's review, the ruling is **Option B**: keep the two
stop operations distinct and expose a named clean-stop predicate; do **not**
introduce a global invariant or strengthen `stopWhenIdle`. Additive, non-breaking,
zero `sorry`, no new axiom kinds.

## Problem

`stopWhenIdle` transitions to `.stopped` on scheduler quiescence
(`running = none ∧ readyQ = [] ∧ timers = []`) but does **not** consult the
resource ledger. So `.stopped` can be reached with a live resource — e.g. a
parked `waiting` task or an actor-owned resource (RFC 091) still `allocated`.
`stopWhenDrained` (RFC 087) additionally requires `resourceDrained = true`. Thus
the meaning of `.stopped` is path-dependent: clean only when reached via
`stopWhenDrained`.

Making `stopped → Drained` a global invariant would force `stopWhenIdle` to also
require drainedness, collapsing `stopWhenIdle ≡ stopWhenDrained` — a breaking
change to `stopWhenIdle` that contradicts RFC 087's deliberately additive design.

## Decision (Option B)

Keep `stopWhenIdle` (idle stop) and `stopWhenDrained` (clean stop) semantically
distinct. Do not add a global `stopped → Drained` invariant. Expose named
predicates as the contract-level handle for "clean shutdown", so downstream
bridge/adapter/replay/observability/API RFCs reason against a precise predicate
rather than bare `.stopped`.

## What shipped

`Henret/Proofs/CleanStop.lean`:

- `Stopped s := runtimeStatus = .stopped` — status only, no ledger claim.
- `StoppedDrained s := Stopped s ∧ Drained s`.
- `CleanStopped s := Stopped s ∧ Frozen s` — the strongest; built on the RFC 090
  `Frozen` spine.
- Projections `cleanStopped_drained`, `cleanStopped_quiescent`,
  `cleanStopped_stoppedDrained`.
- Entry: `stopWhenDrained_enters_cleanStopped` (+ reachable form) — a successful
  `stopWhenDrained` lands in `CleanStopped`.
- Permanence at the `Frozen` level: `cleanStopped_step_stays_frozen`,
  `cleanStopped_run_stays_frozen`. `.stopped` is an *entry* fact only —
  `shutdown` relabels `.stopped → .shuttingDown` (both `≠ .running`), so durable
  content is `Frozen` (quiescent + drained), not the exact label.
- Contrast: `stopWhenIdle_can_stop_undrained` — a witness that `stopWhenIdle`
  reaches `.stopped` with a live resource, refuting any future claim that bare
  `.stopped` is clean. Backed by the golden scenario
  `stopWhenIdle_stops_with_live_resource`.

Docs: `RuntimeStatus` / stop-op docstrings corrected; clean-stop section in
`docs/shutdown-semantics.md`; security reading in `docs/resource-drain.md`;
proof-index RFC 092 section; matrix claims 223–226.

## Not done (deliberately)

- Global `stopped → Drained` (Option C, breaking) — rejected.
- Strengthening `stopWhenIdle` — rejected.
- Liveness/timeliness — out of scope, separate track.

## Contract guidance (for RFC 070/072/061/060/066/074)

"Clean shutdown" is `CleanStopped` (or `StoppedDrained`), never bare `.stopped`.
Replay/observability should record which op produced a stop
(`stopWhenIdle` vs `stopWhenDrained`) and may surface `resourceDrained` /
`cleanStopped` as distinct bits.
