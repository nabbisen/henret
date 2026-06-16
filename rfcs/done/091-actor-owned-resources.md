---
rfc: 91
title: Actor-Owned Resources (RFC 057 Tier 2)
status: Implemented
implemented_in: v0.27.0
supersedes: []
superseded_by: []
depends_on: [57, 87, 88, 89, 90]
blocks: []
category: model-semantics
---

# RFC 091 — Actor-Owned Resources (RFC 057 Tier 2)

## Status

**Implemented in v0.27.0.** Shipped per the architect's review decision
(Option A — `ResourceOwner` sum type, unified `Drained`, new `acquireActor`
op, with the required deltas). All 9 `check.sh --fast` gates green, zero
`sorry`, no new axiom kinds. Tier 1 scope: actor-owned resources have no
manual release (`release t r` is invalid for them); they close on `closeActor`
and finalize as usual. A future RFC may add `releaseActor`.

## Motivation

Today every resource is owned by a **task** (`ResourceRecord.owner : TaskId`).
Its lifecycle is tied to that task: an `allocated` resource is held by a
non-terminal task, a task's termination (`complete`/`cancel`/`fail`/`cancelTree`)
marks its resources `closing`, and `finalize` releases them.

Some resources naturally outlive any single task and belong to an **actor** —
e.g. a connection or buffer shared across the tasks an actor spawns, released
only when the actor itself closes. RFC 091 adds that ownership dimension.

## What the feature needs

1. A way to allocate a resource owned by an actor `a` rather than a task.
2. Lifecycle keyed on actor status: an actor-owned `allocated` resource is held
   by a **non-closed** actor; `closeActor a` marks that actor's `allocated`
   resources `closing`; `finalize` releases them (unchanged).
3. Well-formedness analogues of the task invariants, keyed on `actorStatus`
   instead of `taskState`:
   - `actor_allocated_owner_open` — an actor-owned `allocated` resource's actor
     is not `.closed`.
   - `actor_closing_owner_closed` — an actor-owned `closing` resource's actor is
     `.closed`.

## The representation fork (architect decision #1)

`ResourceRecord.owner` is a `TaskId`, read at ~60 sites across 11 files, and the
four resource well-formedness fields are intrinsically task-keyed. Three ways to
add actor ownership:

**Option A — sum-type owner.**
`owner : ResourceOwner` with `ResourceOwner := task TaskId | actor ActorId`.
Cleanest model, single ledger, and `Drained` (keyed on `state`, not owner) is
untouched. But it rewrites all ~60 `.owner` reads, the four resource WF fields,
their preservation in `Preservation/Resource.lean`, and `markClosingIf`'s
predicate type — and `markClosingIf` is what the RFC 087–090 drain spine builds
on (`DrainedPersistence.lean` references it directly). So Option A re-opens the
just-sealed Tier-2 drain proofs.

**Option B — parallel actor-resource ledger.**
Leave the task ledger and all its proofs byte-identical; add a second map
`actorResources : ResourceId → Option ActorResourceRecord` with its own
invariants and its own `markClosingIf`-analogue. Maximally additive (RFC 057 and
87–90 stay sealed), but duplicates the resource machinery — two ledgers, two
drain notions — which cuts against "keep it simple."

**Option C — ownership discriminant.**
Keep `owner : Nat`, add `ownerKind : OwnerKind`. Smaller diff than A (owner stays
`Nat`) but every owner-reading invariant must branch on `ownerKind`, and it is
the least type-safe of the three.

My recommendation: **Option A** if the architect accepts re-touching the resource
preservation/drain proofs (the model stays clean and single-ledger, which is the
project's stated preference for long-term simplicity); **Option B** only if
keeping RFC 087–090 sealed is judged more important than avoiding a second
ledger. I lean A, but this is a balance call the architect owns.

## The `Drained` fork (architect decision #2)

RFC 087–090 established a clean safety spine — drain progress, single-step
persistence, sleeping-timer coherence, multi-step permanence — on the single
predicate `Drained s := ∀ r rr, resources r = some rr → rr.state = .released`.
Actor-owned resources force a choice:

- **Unified `Drained`.** Actor-owned resources participate in the same
  `Drained`. `closeActor` becomes a resource-marking operation, so RFC 087's
  `step_resources_none_run_none`, RFC 088's `drained_step_drained`, and RFC
  090's `step_preserves_frozen` each gain/adjust a `closeActor` case. The payoff:
  "stopped ⟹ fully drained" keeps covering *all* resources, and the permanence
  theorems still mean what they say. Cost: re-opening recently-shipped proofs.
- **Separate `ActorDrained`.** A second predicate over the actor ledger, leaving
  the task `Drained` spine untouched. Additive, but now there are two drain
  concepts and `stopWhenDrained` must decide whether it requires both.

These two forks interact: Option B + separate `ActorDrained` is the maximally
additive corner; Option A + unified `Drained` is the cleanest-model corner that
re-opens 087–090. The mixed corners are possible but awkward.

## Non-goals

The breaking global `stopped → Drained` invariant (covering `stopWhenIdle`) and
wall-clock liveness remain deferred regardless of the choices above.

## Open questions for the architect

1. **Representation** (§ representation fork): Option A (sum-type owner, clean
   single ledger, re-opens resource preservation + drain proofs) vs Option B
   (parallel actor ledger, fully additive, duplicative) vs Option C
   (discriminant). Which weighting — model simplicity vs keeping RFC 087–090
   sealed — should win?
2. **`Drained` scope** (§ Drained fork): should actor-owned resources join the
   existing `Drained` (and thus `stopWhenDrained`'s guarantee), re-opening the
   Tier-2 drain proofs, or get a separate `ActorDrained` notion? Should
   `stopWhenDrained` require actor-owned resources released too?
3. **Allocation surface**: a new `acquireActor a` operation (RuntimeOp 27 → 28,
   one-op cascade), or overload `acquire` with an owner argument (touches every
   existing `acquire` proof)? The additive instinct favours a new op.

Once 1–3 are decided, the implementation is a known quantity (a new op + the
chosen ledger representation + the actor-keyed invariants + whichever drain
adjustments follow), and can proceed as a normal versioned slice.
