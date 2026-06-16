---
rfc: 49
title: Supervision Restart Policies
status: Implemented
implemented_in: v0.15.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC 049 — Supervision Restart Policies

## Status

Implemented (v0.15.0).

## Summary

Extend Henret's parenthood and cascade-cancel groundwork with minimal restart
semantics. The first restart policy should be one-for-one restart: when a child
fails, the supervisor may spawn a replacement child with a new task id while
preserving a traceable parent relationship.

## Motivation

Actor systems become operationally useful when failure is part of the model.
Henret already has parenthood groundwork and proposed cascade cancel. The next
step is not a large Erlang/OTP clone, but a small semantic nucleus for restart:

- failure is distinct from ordinary completion and cancellation;
- a parent/supervisor can restart a failed child;
- the restarted task has a fresh id;
- parent chains remain acyclic;
- restart history is auditable.

## Non-goals

This RFC does not:

- implement production supervision trees;
- add one-for-all restart initially;
- add restart intensity windows initially;
- model process links/monitors beyond parenthood;
- guarantee liveness of restart unless a policy operation is issued.

## Proposed design

### New task state or result

Add either:

```lean
| failed : TaskState
```

or represent failure as cancelled with reason. Prefer a distinct `.failed` state
because restart policies should distinguish failure from intentional cancel.

### New operations

```lean
| fail        (t : TaskId)
| restartOne  (parent failedChild : TaskId) (actor : ActorId)
```

`fail t` moves a running or spawned non-terminal task to `.failed`, clears any
ready/waiting/timer ownership locations, and records no replacement.

`restartOne parent failedChild actor` requires:

- `parent` is running or otherwise authorized as supervisor;
- `taskParent failedChild = some parent`;
- `failedChild` is `.failed`;
- `actor` has or receives a mailbox according to existing spawn rules.

It creates a new child with fresh `nextId`, parent `parent`, owner `actor`, and
initial task state consistent with spawn semantics.

### Restart relation

Add:

```lean
restartOf : TaskId → Option TaskId
```

Meaning: `restartOf newChild = some failedChild`.

### Invariants

Add WellFormed fields if accepted:

```lean
restart_parent_consistent :
  restartOf new = some old →
  ∃ p, parentOf new = some p ∧ parentOf old = some p

restart_old_failed :
  restartOf new = some old → taskState old = some .failed

restart_fresh :
  restartOf new = some old → old < new
```

Keep this small. Do not add restart trees unless needed.

### Theorems

Headline:

```lean
theorem reachable_restart_fresh : ...
```

```lean
theorem restart_preserves_parent_acyclicity : ...
```

```lean
theorem restarted_task_has_owner : ...
```

## Implementation tasks

1. Decide `.failed` vs reason-tagged terminal state.
2. Add `fail` operation.
3. Add `restartOne` operation.
4. Add `restartOf` field if restart provenance is desired.
5. Update `RuntimeState.init`.
6. Update `step`.
7. Update `WellFormed` if new fields are accepted.
8. Update all preservation proofs.
9. Add trace events via RFC 045: `.failed`, `.restarted`.
10. Add demo: parent spawns child → child fails → parent restarts child.
11. Document non-goals: no restart intensity, no one-for-all yet.

## Acceptance criteria

- Failure and cancellation are semantically distinct.
- Restart creates a fresh task id.
- Parent acyclicity remains proven.
- Restart provenance is inspectable.
- No liveness claim is made without a policy operation.

## Risks

Restart semantics can become large quickly. Keep v1 small: one-for-one only,
explicit operation only, no automatic restart policy yet.
