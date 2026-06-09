# RFC 038 — Parent and Owner Exactness Invariants

**Status.** Implemented (v0.9.1)  
**Target version.** v0.9.1  
**Priority.** Medium-high  
**Track.** Semantic kernel exactness  
**Depends on.** RFC 037; can run before or after RFC 036  
**Touches.** `RuntimeState`, `WellFormed`, `Ownership.lean`, `Parenthood.lean`, preservation proofs, docs

## Summary

Strengthen Henret's state-shape contract around ownership and parenthood. The current model proves that spawned tasks have owners and parent chains decrease, but it does not yet expose exact converse facts as part of the public invariant story.

This RFC adds or derives:

```lean
owner_spawned
parent_child_spawned
```

and fixes theorem signatures around `spawnChild` so cross-actor child spawning is represented precisely.

## Motivation

Henret now supports actor-scoped child spawning and parent-chain acyclicity. The next supervision features will rely on parent and owner relations being self-describing.

Current useful facts:

- every spawned task has an owner;
- parent id is less than child id;
- parent exists/spawned;
- parent chains terminate.

Missing exactness facts:

- every owned task is spawned;
- every task with a parent is itself spawned;
- child owner theorem should support cross-actor child spawning rather than only same-actor spawning.

Without these, later cascade-cancel proofs will repeatedly need operational reasoning instead of projecting from `WellFormed`.

## Proposed invariant additions

### Option A — add fields to `WellFormed`

```lean
owner_spawned :
  ∀ t a, s.taskOwner t = some a → ∃ st, s.taskState t = some st

parent_child_spawned :
  ∀ t p, s.taskParent t = some p → ∃ st, s.taskState t = some st
```

This would bring `WellFormed` from 19 to 21 fields.

### Option B — derived reachable theorems only

```lean
theorem reachable_owner_spawned (ops) :
  ∀ t a, (run init ops).taskOwner t = some a →
    ∃ st, (run init ops).taskState t = some st

theorem reachable_parent_child_spawned (ops) :
  ∀ t p, (run init ops).taskParent t = some p →
    ∃ st, (run init ops).taskState t = some st
```

Option B avoids more preservation fields but makes the public state-shape contract less complete.

## Recommendation

Use **Option A** if proof cost is acceptable. Henret has already chosen `WellFormed` as the master state-shape contract. Owner/parent exactness belongs there.

If the preservation cost is high, implement Option B in v0.9.1 and schedule Option A later.

## Fix `spawnChild_sets_owner`

The theorem must separate the parent's actor from the child's actor.

Recommended statement:

```lean
theorem spawnChild_sets_owner
    {s : RuntimeState} {t : TaskId} {parentOwner childActor : ActorId}
    (hrt : s.running = some t)
    (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some parentOwner)
    (hmb : ∃ mb, s.mailboxes childActor = some mb)
    (hfresh : s.taskState s.nextId = none) :
    ((step s (.spawnChild t childActor)).1).taskOwner s.nextId = some childActor
```

If `spawnChild` creates the child actor mailbox when absent, replace `hmb` with the actual guard condition. The theorem should match `step` exactly.

Also generalize:

```lean
spawnChild_sets_parent
spawnChild_queues_child
spawnChild_child_spawned
```

so no theorem accidentally conflates parent owner and child actor.

## Preservation obligations

If fields are added to `WellFormed`, update all preservation operation families:

- Lifecycle: spawn, spawnChild, schedule, yield, complete, cancel.
- Messaging: send, receive, inject.
- Time: sleep, tick, wake.

Expected proof pattern:

- Most operations pass through `taskOwner` and `taskParent` unchanged.
- `spawn` writes `taskOwner` and `taskState` together.
- `spawnChild` writes `taskOwner`, `taskParent`, and `taskState` together.
- No operation should leave an owner/parent pointer pointing to an unspawned task.

## New theorems

```lean
theorem reachable_owner_spawned (ops : List RuntimeOp) : ...
theorem reachable_parent_child_spawned (ops : List RuntimeOp) : ...
```

If implemented as `WellFormed` fields, these should be simple projections from `reachable_wf`.

## Documentation updates

Update:

- `docs/proof-index.md`
- `docs/proof-trust-test-matrix.md`
- `docs/guided-tour.md`
- `docs/handoff-henret-for-iotakt.md` if it refers to parenthood

Explain:

```text
Parenthood is now exact: parent pointers only exist on spawned children,
and parent references point to spawned parents.
```

## Acceptance criteria

- Cross-actor child spawning theorem is generalized.
- `owner_spawned` is available as either a WF field or reachable theorem.
- `parent_child_spawned` is available as either a WF field or reachable theorem.
- Parent/owner theorem names are included in doc-symbol check.
- Axiom audit remains clean.
- No semantics of `spawnChild` are silently changed.

## Non-goals

- Cascade cancel.
- Restart policies.
- Supervision tree policies.
- Parent actor identity constraints.

This RFC strengthens the substrate; RFC 039 uses it.
