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
| `resource_owner_spawned` | every resource is owned by a spawned task |
| `allocated_owner_nonterminal` | an `allocated` resource's owner is live |
| `closing_owner_terminal` | a `closing` resource's owner is terminal |

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
resource need never be finalized); a drain-before-stop discipline (`stopped` ≠
resource-drained); actor-owned resources; and resource transfer across
`restartOne` (the replacement starts fresh — Option 1).
