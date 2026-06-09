# RFC 035 — Lean-Runtime Bridge: Connecting the Henret Model to the Work-Stealing Runtime

**Status.** Implemented (v0.8.0)
**Tracks.** Cross-project semantic bridge between `henret` and `lean-runtime-workspace`.
**Touches.** `henret` model semantics, `lean-runtime-workspace/lean-runtime` refinement layer, new `Henret/Bridge/` module, documentation.

## Summary

`henret` is a kernel-proven actor/task model with 19-field `WellFormed`, full
invariant preservation across all 12 operations, and globally unique occurrence
identity. `lean-runtime-workspace` is a separately-developed work-stealing async
runtime with a dual-interpreter architecture (`TaskOp` grammar → pure model →
machine → differential tests) and typed FFI axioms over a C Chase-Lev deque.

Both projects are now in a stable, fully-built state. This RFC defines how to
**formally connect them**: show that the `lean-runtime`'s `ModelSchedulerState`
and `TaskOp` grammar is a *refinement* of henret's `RuntimeState` and
`RuntimeOp` grammar, so that every kernel-proven henret guarantee is also a
guarantee about the lean-runtime's model layer.

## Why this matters

henret's `reachable_wf` certifies 19 invariant fields in every reachable state.
lean-runtime's `qRun_tracks` certifies that the machine tracks the model under
any sequence of queue operations. Bridging the two creates a **layered
verification stack**:

```
henret kernel proofs          (19 WellFormed fields, provably)
        ↓  RFC 035 bridge
lean-runtime model layer      (push/steal/pop/wake, model theorems)
        ↓  Refinement.lean
lean-runtime machine layer    (DequeModel parametric refinement)
        ↓  FFISpec.lean axioms
C Chase-Lev deque             (trusted, differentially tested)
```

Without the bridge, the two projects share an architecture (TaskId, ActorId,
queue semantics) but no formal connection. A bug in the mapping from
`RuntimeOp.send` to `QOp.Push` could go undetected.

## Scope

### In scope

1. **Grammar correspondence** — define a mapping function
   `RuntimeOp → Option (List QOp)` (some ops have no queue effect; `send`
   maps to push-plus-optional-wake; `receive` maps to pop).

2. **State correspondence** — define a relation
   `BridgeState : RuntimeState → ModelSchedulerState → Prop` that connects
   the full scheduler state to the queue-centric worker state.

3. **Preservation bridge** — prove that for every `op : RuntimeOp`, if
   `BridgeState s m` then `BridgeState (step s op).1 (applyQOps m (toQOps op))`,
   where `applyQOps` applies the mapped `QOp` list to the model.

4. **Occurrence identity lift** — prove that `lean-runtime`'s task-id
   discipline (`nextId` monotone) corresponds to henret's `nextMsgId`
   monotonicity; both are instances of the same counter-allocation pattern.

5. **Documentation** — a `docs/bridge-architecture.md` explaining the three
   assurance layers (kernel / model / machine), where each claim lives, and
   what remains in the trusted boundary.

### Out of scope

- Concurrent race-freedom (requires Iris; explicitly deferred per FFISpec.lean).
- epoll / timer-wheel integration (lean-runtime Phase 1 is a separate track).
- Full iotakt integration (deferred to a follow-on RFC; henret's handoff doc
  already covers the shape of that interface).

## Proposed module layout

```
henret/
  Henret/
    Bridge/
      Grammar.lean     -- RuntimeOp → List QOp translation
      State.lean       -- BridgeState relation definition
      Preservation.lean -- bridge preservation theorem
      OccurrenceId.lean -- nextMsgId ↔ nextId correspondence
  docs/bridge-architecture.md
```

The bridge lives in `henret` (not in `lean-runtime-workspace`) because `henret`
is the upstream model authority.

## Key theorems (acceptance criteria)

| Theorem | Statement |
|---|---|
| `toQOps_send_effect` | `toQOps (.send t b m) = [.Push w t']` for the owning worker `w` of task `t` |
| `toQOps_receive_effect` | `toQOps (.receive t) = [.Pop w]` when `t` has owner-mailbox items |
| `bridge_step` | `BridgeState s m → BridgeState (step s op).1 (applyQOps m (toQOps op))` |
| `reachable_bridge_wf` | `BridgeState (run init ops) m → WellFormed (run init ops)` (inherited) |
| `nextMsgId_eq_nextId` | `nextMsgId` and `nextId` are both allocated by the same counter-monotonicity pattern |

## Dependencies

- henret v0.7.0 (RFC 033 complete — `Envelope`, `nextMsgId`, 19-field WellFormed)
- lean-runtime-workspace (all 37 targets build, `runtimeTests` exit 0)
- No new C code required

## Assurance-layer placement

| Layer | Claim class | File |
|---|---|---|
| Kernel | WellFormed invariant (19 fields) | `Henret/Proofs/` |
| Kernel | Occurrence uniqueness | `Henret/Proofs/Occurrence.lean` |
| **Bridge** | **Grammar correspondence** | **`Henret/Bridge/Grammar.lean`** |
| **Bridge** | **State correspondence** | **`Henret/Bridge/State.lean`** |
| Trusted | C race-freedom | `lean-runtime/FFISpec.lean` (axioms) |
| Tested | Machine tracks model | `lean-runtime/Refinement.lean` + `runtimeTests` |

## Open questions

1. Should `BridgeState` track **task → worker** assignment (which queue holds
   which task), or only track queue **length** invariants? The weaker form
   is easier to prove; the stronger form is more useful for end-to-end claims.

2. The `lean-runtime` uses `ModelSchedulerState` (worker-indexed queues of
   `TaskId`) while henret uses `RuntimeState` (actor-indexed mailboxes of
   `Envelope`). The bridge must handle the translation from actor-mailbox
   semantics to per-worker deque semantics. Is there a clean intermediate
   representation, or should the bridge be directional (henret → lean-runtime
   projection, not a full bijection)?

3. The `lean-runtime`'s `Inject` operation adds tasks from an external source
   without an owning worker. Does this correspond to henret's `inject` (actor
   delivery) or to `spawn` (new task creation)? Both create entities from
   outside the scheduler. The RFC should resolve this mapping explicitly.

## Adoption guidance

The bridge is a **new module** (`Henret/Bridge/`), not a modification of
existing henret or lean-runtime files. Both projects remain independently
buildable. The bridge imports from both; it is the formal glue layer.

If the open questions above lead to a design decision that changes either
project's types or semantics, that change should be its own RFC rather than
absorbed into this one.
