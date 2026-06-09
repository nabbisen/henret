# RFC 057 — Resource Lifetime and Finalization Ledger

## Status

Proposed.

## Summary

Add a pure model for resource acquire/use/release/finalization so Henret can express runtime cleanup obligations.

## Motivation

Execution management is not only tasks and messages. Real runtimes manage resources: file descriptors, reactor registrations, timers, handles, and native objects. Henret should model resource lifetime in a pure way before connecting to concrete FFI cleanup.

## Non-goals

- Do not model OS-specific file descriptors.
- Do not prove C finalizers correct.
- Do not add linear types to Lean; use state-machine invariants.
- Do not require every task to own resources in the core profile.

## Design

Add resource identifiers and state:

```lean
abbrev ResourceId := Nat

inductive ResourceState where
  | allocated
  | closing
  | released

structure ResourceRecord where
  owner : Option TaskId
  state : ResourceState

resources : ResourceId → Option ResourceRecord
nextResourceId : Nat
```

Add operations:

```lean
| acquire (t : TaskId)
| release (t : TaskId) (r : ResourceId)
| finalize (r : ResourceId)
```

Semantics:

- Only running tasks may acquire/release.\n- Released resources cannot be used.\n- Finalize is legal only for closing/released depending on chosen policy.\n- Cancelled tasks trigger a model-level transition that marks owned resources closing, but does not prove finalization runs.

## Formal model changes

- Extend `RuntimeState` with resource ledger only under the resource profile.
- Define `ResourceOwnedBy`, `ResourceLive`, `ResourceClosed`.
- Decide whether `cancel` updates resource states immediately.

## Proof obligations

- `resource_owner_spawned`
- `released_resource_never_live`
- `cancel_marks_resources_closing` if adopted.
- `finalized_resource_not_reacquired`
- `reachable_resource_ids_fresh`
- Preservation of resource ledger WellFormed fields.

## Tests and examples

- Demo: acquire, release, finalize.
- Demo: use-after-release invalid.
- Demo: cancel with owned resource transitions to closing.
- Golden trace for resource cleanup.

## Documentation updates

- Add resource lifetime profile.
- Add trust-boundary note: resource model is pure; native cleanup remains trusted/tested outside Henret.

## Acceptance criteria

- Resources have unique ids.
- Released/finalized resources cannot be used.
- Cancellation/resource behavior is explicit.
- No claim is made that finalizers run under unfair scheduling.

## Risks and review questions

- Should finalization be a task operation, environment operation, or runtime operation?
- Should resources be actor-owned or task-owned?
- Should resource cleanup participate in shutdown idle detection?
