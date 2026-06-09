# RFC 043 — Multi-Worker Bridge Model Extension

**Status.** Proposed  
**Target version.** v0.12.0 or later  
**Priority.** After RFC 036 only  
**Track.** Bridge/refinement layer  
**Depends on.** RFC 036 single-worker bridge completion  
**Touches.** `Henret/Bridge/*`, possible bridge-only worker placement state, docs

## Summary

Extend the bridge from a single-worker queue projection to a multi-worker queue projection suitable for comparison with `lean-runtime-workspace` work-stealing semantics.

This RFC must not be started until the single-worker bridge is complete.

## Motivation

Henret's semantic kernel has a single logical `readyQ`. The concrete runtime has worker-indexed queues and work stealing. A bridge is needed to explain how the single semantic ready set/list corresponds to a distributed scheduler representation.

The critical design question is where worker assignment belongs.

## Design decision

Do **not** add worker placement directly to `RuntimeState` unless a semantic theorem requires it.

Henret's kernel should remain actor/task semantic. Worker placement is an implementation/refinement concern.

Introduce bridge-level placement state:

```lean
structure Placement where
  taskWorker : TaskId → Option WorkerIdx
```

or a relation over queues:

```lean
structure MultiBridgeState (s : RuntimeState) (wqs : WorkerQueues) : Prop where
  ready_partition : ...
  no_extra_tasks  : ...
  nodup_global    : ...
```

## Relation options

### Option A — exact concatenation

```lean
s.readyQ = concatWorkers wqs
```

Pros:

- simple;
- preserves order if a canonical worker order exists.

Cons:

- too strong for work stealing;
- worker movement changes ordering without changing semantic readiness.

### Option B — multiset/set equality

```lean
∀ t, t ∈ s.readyQ ↔ ∃ w, t ∈ wqs w
```

plus global no-dup across workers.

Pros:

- robust to stealing and worker movement;
- matches scheduler implementation better.

Cons:

- loses queue order information;
- weaker than single-worker exact bridge.

### Recommendation

Use **Option B** for multi-worker. Keep single-worker exact-list bridge as a stronger special case.

## Proposed relation

```lean
structure MultiBridgeState (s : RuntimeState) (wqs : WorkerQueues) : Prop where
  sound : ∀ t w, t ∈ wqs w → t ∈ s.readyQ
  complete : ∀ t, t ∈ s.readyQ → ∃ w, t ∈ wqs w
  worker_nodup : ∀ w, (wqs w).Nodup
  global_unique : ∀ t w1 w2,
    t ∈ wqs w1 → t ∈ wqs w2 → w1 = w2
```

If `readyQ` order matters for Henret semantics, document that multi-worker bridge preserves membership, not order.

## QOp semantics

Multi-worker operations should include:

```lean
| Push   : WorkerIdx → TaskId → QOp
| Pop    : WorkerIdx → QOp
| Steal  : thief : WorkerIdx → victim : WorkerIdx → QOp
| Filter : WorkerIdx → TaskId → QOp
| Move   : from : WorkerIdx → to : WorkerIdx → TaskId → QOp -- optional
```

`Steal` preserves global membership but moves/removes according to runtime scheduling.

## Wake placement policy

Before proving wake bridge, define policy:

1. wake to original worker;
2. wake to current worker;
3. wake to worker 0;
4. wake to global injector.

Recommendation for bridge first version:

```text
Wake to worker 0.
```

Reason: deterministic and compatible with current single-worker projection. Later RFC can add placement.

## Theorems

```lean
single_bridge_implies_multi_bridge :
  BridgeState s wqs → MultiBridgeState s wqs
```

```lean
multi_bridge_push : ...
multi_bridge_pop : ...
multi_bridge_steal_preserves_membership : ...
multi_bridge_filter : ...
```

```lean
multi_bridge_run_tracks : ...
```

The exact theorem should reflect membership preservation, not list equality.

## Interaction with `lean-runtime`

The multi-worker bridge should align with `lean-runtime`'s worker-indexed queue model and Chase-Lev semantics. However, it still lives at the model level. It does not prove C race-freedom.

## Acceptance criteria

- `MultiBridgeState` exists.
- It explicitly states membership soundness, completeness, and global uniqueness.
- Work stealing preserves the relation.
- Single-worker bridge is shown as a special case.
- Wake placement policy is documented.
- No worker-placement field is added to `RuntimeState` unless separately justified.

## Risks

### Losing order may weaken claims

This is acceptable if clearly documented. Work-stealing schedulers do not preserve a single global ready order anyway.

### Premature runtime coupling

Do not import C/FFI assumptions into Henret's pure model. Keep multi-worker bridge at the abstract queue level.

## Non-goals

- Native thread scheduling proof.
- Fairness/liveness.
- C Chase-Lev proof.
- OS worker management.
