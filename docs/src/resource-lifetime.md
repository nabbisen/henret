# Resource lifetime & finalization ledger (RFC 057, Tier 1)

This is the canonical reference for the resource-lifetime model. For the
upgrade path from v0.18 see [`migration/v0.18-to-v0.19.md`](migration/v0.18-to-v0.19.md).

## Model

`Henret/Resource/Ledger.lean` adds:

- `ResourceId := Nat` — a monotonically-allocated handle.
- `ResourceState` — `allocated` | `closing` | `released`.
- `ResourceRecord` — `{ owner : TaskId, state : ResourceState }`. Every
  resource is **task-owned**.
- `markClosingIf (p : TaskId → Bool) (res)` — flips every `allocated` record
  whose owner satisfies `p` to `closing`, leaving `closing`/`released`/absent
  records untouched.

`RuntimeState` carries `resources : ResourceId → Option ResourceRecord` (init
empty) and `nextResourceId : Nat` (init `0`).

## Operations

| Op | Guard | Effect | Result |
|----|-------|--------|--------|
| `acquire t` | `t` running, `taskState t = running` | new id `nextResourceId` ↦ `⟨t, allocated⟩`; counter `+1` | `.acquired <old id>` |
| `acquire t` | otherwise | none | `.invalid` |
| `release t r` | `t` running & `running`, `resources r = ⟨t, allocated⟩` | `r` ↦ `⟨t, released⟩` | `.ok` |
| `release t r` | non-owner / not `allocated` | none | `.invalid` |
| `finalize r` | `resources r = ⟨o, closing⟩` (no running guard) | `r` ↦ `⟨o, released⟩` | `.ok` |
| `finalize r` | not `closing` | none | `.invalid` |

In addition, every terminal transition (`complete`, `cancel`, `fail`, and a
`cancelTree` that reaches the owner) applies `markClosingIf` so the owner's
`allocated` resources become `closing`.

## Invariants (`WellFormed` fields 30–33)

| Field | Meaning |
|-------|---------|
| `resource_fresh` | every id `≥ nextResourceId` is unallocated |
| `resource_owner_valid` | every resource's owner (task or actor) exists |
| `allocated_owner_live` | an `allocated` resource's owner can still hold a live handle |
| `closing_owner_closed` | a `closing` resource's owner can no longer act |

Jointly: a **live** task never owns a `closing` resource, and a **terminal**
task never owns an `allocated` one. All four are vacuous on a program that
never calls `acquire`.

## Headline theorems

`preserves_wf_acquire` / `_release` / `_finalize` (all 33 fields preserved);
the four `reachable_resource_*` projections; `nextResourceId_monotone_step` /
`_run` (ids never reused); and the four terminal-coupling theorems
`{complete,cancel,fail}_marks_owned_resource_closing` and
`cancelTree_marks_descendant_resource_closing`. `released` is a terminal ledger
state — a released resource stays released under every operation and in every
reachable future (`released_resource_never_live_step` / `_run`,
`reachable_released_resource_never_live`). Per-branch behaviour is pinned
by `Henret/Proofs/ResourceBranch.lean`; end-to-end behaviour by the ten
`resource_*` conformance scenarios.

## Trust & scope

The **native finalizer is a trust boundary**: Tier 1 proves the ledger
state-machine well-formed but does not model the FFI that performs physical
reclamation. `finalize` is the typed seam that boundary reasons against.

Out of scope for Tier 1: any liveness/timeliness guarantee (a `closing`
resource need never be finalized); resource transfer across `restartOne` (the
replacement starts fresh — Option 1); and manual release of actor-owned
resources (`releaseActor`, a possible future RFC).

## Actor-owned resources (RFC 091)

RFC 091 generalizes the owner from a task to a `ResourceOwner` sum type:

```text
ResourceOwner = task (t : TaskId) | actor (a : ActorId)
```

One ledger, one `Drained` predicate, and one finalization discipline cover
both owner kinds; there is no parallel actor-resource ledger. The owner
invariants are stated owner-generically and read through `OwnerValid` /
`OwnerLive` / `OwnerClosed` (the task projections recover the original RFC 057
statements via `WellFormed.allocated_owner_nonterminal` /
`closing_owner_terminal`).

* **Allocation.** `acquireActor a` is a *control-plane* op: it allocates a fresh
  actor-owned resource only when the runtime is running, the actor is open, and
  the actor **exists**. Existence is witnessed by a mailbox (`ActorExists`), not
  by `actorStatus` alone — `actorStatus` is total and defaults to active, so a
  status check would let `acquireActor 999999` allocate for a never-created
  actor (`preserves_wf_acquireActor`).
* **Lifetime.** An actor-owned resource **outlives any single task**: a task
  going terminal (`complete`/`cancel`/`fail`) never closes it. It closes only
  when its owning actor closes: `closeActor a` marks actor-`a`-owned `allocated`
  resources `closing` (`closeActor_marks_actor_resources_closing`), and
  `finalize` reclaims them as usual.
* **Manual release (RFC 093).** `releaseActor a r` is a control-plane,
  running-gated op (symmetric with `acquireActor`): while the runtime is
  running, actor `a` voluntarily flips its own `allocated` resource to
  `released`. `release t r` (the *task* release) remains invalid for actor-owned
  resources — the guard requires owner `= .task t`. A closed actor's resources
  are `closing`, not `allocated`, so `releaseActor` only ever applies to a live
  actor's handle; the `closeActor` → `finalize` path remains the cleanup route
  for a closing actor.
* **Unified drain.** `Drained` quantifies all resources, so `stopWhenDrained`
  is blocked while an actor-owned resource is `allocated` or `closing`, and
  succeeds once it is released (via `releaseActor`) or finalized.
