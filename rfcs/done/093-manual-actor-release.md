---
rfc: 93
title: Manual Actor-Resource Release
status: Implemented
implemented_in: v0.29.0
supersedes: []
superseded_by: []
depends_on: [57, 87, 91]
blocks: []
category: model-semantics
---

# RFC 093 — Manual Actor-Resource Release

## Status

**Implemented in v0.29.0.** Adds `releaseActor`, the voluntary-release
counterpart to RFC 091's `acquireActor`, completing the actor-resource lifecycle
symmetry. Additive, zero `sorry`, no new axiom kinds. First Wave 1 item of the
prioritized roadmap.

## Problem

RFC 091 (actor-owned resources) deliberately shipped **no manual actor release**
(Tier 1): an actor-owned `allocated` resource could only leave the live state via
`closeActor` (→ `closing`) then `finalize` (→ `released`). There was no way for an
actor to voluntarily release a resource it no longer needs while staying open.
`release t r` (the task release) is — and remains — invalid for actor-owned
resources.

## Decision: authorization model

`releaseActor a r` is a **control-plane, running-gated** operation, symmetric
with `acquireActor`:

```
releaseActor a r  succeeds iff
  runtimeStatus = .running  ∧  resources r = some ⟨.actor a, .allocated⟩
then  resources r := some ⟨.actor a, .released⟩
```

Rationale for the guard:

- **Symmetry with `acquireActor`** (also running-gated). The *voluntary*
  lifecycle ops (acquire/release) are running-gated; the *terminal* cleanup ops
  (`closeActor` / `finalize`) are not.
- **Ownership is the authorization.** Only the owning actor (`a`) may release its
  own resource; releasing the wrong actor's resource is invalid.
- A **closed** actor's resources are already `closing`, not `allocated`, so
  `releaseActor` never applies to a closed actor — the `closeActor` → `finalize`
  path remains the cleanup route for a closing actor. No separate
  `actorStatus`-open guard is needed (the `.allocated` match subsumes it).

## What shipped

- New op `releaseActor (a : ActorId) (r : ResourceId)` (RuntimeOp 28 → 29).
- `preserves_wf_releaseActor` — the flip discharges the `allocated_owner_live`
  obligation; the owner is unchanged so `resource_owner_valid` is preserved.
- `bridge_releaseActor` — queue-stable (`toQOps = []`).
- Drain/frozen spine unaffected: `releaseActor` writes only an already-`some
  allocated` slot (never `none`, never a `released` record) and is running-gated,
  so `step_resources_none_run_none`, `step_resources_eq_of_released`,
  `drained_step_drained`, and `step_preserves_frozen` carry it with no new
  hypotheses.
- Six conformance scenarios incl. `releaseActor_enables_drained_stop` (a drain
  route that does not require `closeActor` + `finalize`).
- Docs: resource-lifetime (manual-release section), proof-index RFC 093, matrix
  claims 227–229.

## Not done (deliberately)

- Cross-actor or environment release (only the owning actor may release).
- Releasing a `closing` actor resource via `releaseActor` (that is `finalize`'s
  job).
