# RFC 039 — Supervision Semantics: Cascade Cancel

**Status.** Proposed  
**Target version.** v0.10.0  
**Priority.** Medium  
**Track.** Actor/task supervision semantics  
**Depends on.** RFC 038 strongly recommended  
**Touches.** `RuntimeOp`, `RuntimeState` helper functions, preservation proofs, parenthood proofs, examples, docs

## Summary

Add the first real supervision operation: cascade cancellation of a task subtree.

This RFC does **not** add restart policies, failure escalation, monitors, or links. It introduces only the safest supervision primitive:

```lean
RuntimeOp.cancelTree (root : TaskId)
```

or, if naming consistency is preferred:

```lean
RuntimeOp.cancelSubtree (root : TaskId)
```

The operation cancels the root task and every descendant according to `taskParent`.

## Motivation

Henret now models parenthood and proves parent chains terminate. A parent relation becomes semantically meaningful only when some operation uses it. Cascade cancel is the simplest meaningful supervision feature because it is a safety operation, not a recovery policy.

Restart policies would require specifying actor initialization, mailbox retention, occurrence identity across restarts, and failure reasons. Cascade cancel avoids those topics while establishing the key tree traversal machinery.

## Design choices

### Operation name

Recommended:

```lean
| cancelTree (root : TaskId)
```

Reason: common supervision terminology; clearer than `cancelSubtree` in theorem names.

### Descendant relation

Define a pure relation:

```lean
def IsChildOf (s : RuntimeState) (child parent : TaskId) : Prop :=
  s.taskParent child = some parent

inductive DescendantOf (s : RuntimeState) : TaskId → TaskId → Prop
  | direct : s.taskParent child = some parent → DescendantOf s child parent
  | trans  : DescendantOf s mid parent → s.taskParent child = some mid → DescendantOf s child parent
```

Because parent ids decrease (`parent_lt`), descendant traversal is finite.

Alternative: define a computable descendant collector using `TaskId < nextId` fuel.

### Computable cancellation set

For executable `step`, use a computable function:

```lean
def descendantsOf (s : RuntimeState) (root : TaskId) : List TaskId
```

Recommended implementation:

- scan ids from `0` to `s.nextId - 1`;
- include `t` if repeated parent lookup reaches `root`;
- include `root` itself if spawned.

Avoid recursion over arbitrary parent maps unless termination is obvious from `parent_lt`.

### State effects

For each task in the cancellation set:

- `taskState t := some .cancelled` if task exists and is not already terminal;
- remove `t` from `readyQ`;
- if `running = some t`, clear `running`;
- remove `t` from timers;
- remove `t` from all `mailboxWaiters`;
- do not delete mailbox contents;
- do not delete `taskOwner` or `taskParent` pointers.

Keeping owner/parent metadata after cancellation is recommended because it preserves auditability of the supervision tree.

### Step result

Add one of:

```lean
| cancelledTree (root : TaskId) (count : Nat)
```

or reuse `.ok`.

Recommendation: start with `.ok` to reduce result-surface churn, unless demos need the count.

## Required theorems

### Termination / boundedness

```lean
theorem descendantsOf_subset_spawned :
  t ∈ descendantsOf s root → t < s.nextId
```

```lean
theorem descendantsOf_includes_root :
  spawned s root → root ∈ descendantsOf s root
```

### Correct cancellation

```lean
theorem cancelTree_cancels_root :
  spawned s root →
  ((step s (.cancelTree root)).1).taskState root = some .cancelled
```

```lean
theorem cancelTree_cancels_descendants :
  DescendantOf s t root →
  spawned s t →
  ((step s (.cancelTree root)).1).taskState t = some .cancelled
```

### Non-descendant preservation

```lean
theorem cancelTree_preserves_non_descendants :
  ¬ DescendantOf s t root → t ≠ root →
  ((step s (.cancelTree root)).1).taskState t = s.taskState t
```

This theorem may require restrictions for tasks affected by unrelated side structures. At minimum, prove task-state preservation.

### Queue/timer/waiter cleanup

```lean
theorem cancelTree_removes_from_readyQ :
  t ∈ descendantsOf s root →
  t ∉ ((step s (.cancelTree root)).1).readyQ
```

```lean
theorem cancelTree_removes_from_timers : ...
theorem cancelTree_removes_from_waiters : ...
```

### WellFormed preservation

Extend `step_preserves_wf` with the `cancelTree` branch.

This branch will be the main proof cost because it changes multiple side structures at once.

## Bridge implications

RFC 036 should have introduced `QOp.Filter`. For cascade cancel, either:

1. emit one `Filter 0 t` per cancelled task, or
2. defer bridge coverage for `cancelTree`.

Recommended for first implementation: include `toQOps cancelTree` only after the semantic operation is stable. It may be acceptable to mark bridge coverage for `cancelTree` as deferred in this RFC.

## Examples

Add a demo scenario:

```text
spawn root
schedule root
spawnChild root actorA
spawnChild root actorB
cancelTree root
assert root and children are cancelled
assert readyQ has no cancelled child
assert unrelated task remains runnable
```

## Documentation

Update:

- guided tour supervision section;
- proof matrix;
- proof index;
- examples README.

Clearly state:

```text
Cascade cancel is supervision groundwork. Restart policies are not modeled.
```

## Acceptance criteria

- `RuntimeOp.cancelTree` or `cancelSubtree` exists.
- Computable descendant collection is total.
- Root and descendants are cancelled.
- Non-descendant task state is preserved.
- readyQ/timers/waiters are cleaned.
- `reachable_wf` still holds.
- Demo scenario covers root, child, and unrelated task.
- Bridge coverage is either implemented or explicitly OUTSCOPE/deferred.

## Risks

### Descendant traversal proof complexity

A computable list-based implementation may be easier to prove than an elegant inductive relation. Use both: executable list for `step`, inductive relation for theorem statements, bridged by lemmas.

### Metadata retention controversy

Cancelling without deleting ownership/parent pointers is deliberate. It preserves audit history and avoids invalidating parent-chain theorems.

## Non-goals

- Restart.
- Failure reason propagation.
- Actor links/monitors.
- Supervisor strategies.
- Mailbox deletion.
