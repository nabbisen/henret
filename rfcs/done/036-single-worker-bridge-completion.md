# RFC 036 — Bridge Claim Repair and Single-Worker Bridge Completion

**Status.** Implemented (v0.9.0)  
**Target version.** v0.9.0  
**Priority.** Highest after RFC 037  
**Track.** Bridge/refinement layer  
**Depends on.** RFC 037, RFC 035 skeleton  
**Touches.** `Henret/Bridge/*`, `docs/bridge-architecture.md`, proof index, proof/trust/test matrix, axiom audit

## Summary

Complete the single-worker bridge between Henret's actor/task semantic model and the queue model used by `lean-runtime-workspace`.

RFC 035 introduced the right module boundary but shipped as a skeleton. RFC 036 makes the bridge honest and useful by repairing `toQOps`, defining queue effects for all ready-queue-changing operations, adding missing preservation theorems, and replacing the weak existential bridge headline with a trace-based bridge theorem.

## Motivation

Henret's semantic kernel is strong, but the bridge is currently the least mature layer. The review found these bridge issues:

1. `reachable_bridge` is too weak because a matching queue witness can be constructed for any state.
2. `toQOps` is documented as validity-aware but is not guard-compatible for all operations.
3. `toQOps .tick` uses `s.now` instead of the tick argument.
4. `QOp.Wake` is emitted by translation but interpreted as a no-op by `applyQOp`.
5. Bridge coverage is missing for `schedule`, `cancel`, `send`, `inject`, and `tick` cases.

The next advancement should close the single-worker bridge before multi-worker semantics are attempted.

## Design principles

1. **Queue projection, not full runtime refinement.** The bridge relates Henret's `readyQ` to a single worker queue. It does not claim fairness, native execution, or actor semantics in the queue model.
2. **Guard-compatible translation.** If `step s op` is invalid, bridge translation must not emit queue effects.
3. **Ready-queue effect completeness.** Every operation that changes `readyQ` must have a queue operation translation.
4. **Trace preservation.** The headline theorem should say that applying translated queue operations tracks Henret's queue projection through a run, not merely that a witness exists.

## Proposed QOp grammar

Extend or normalize the bridge queue grammar:

```lean
inductive QOp where
  | Push   : WorkerIdx → TaskId → QOp
  | Pop    : WorkerIdx → QOp
  | Filter : WorkerIdx → TaskId → QOp
```

Recommended: do **not** use `Wake` in the single-worker bridge. Waking is a Henret semantic event; the queue effect is simply `Push 0 t`.

If `Wake` is kept for future worker-aware policy, define it as an alias at the bridge layer:

```lean
| Wake t => push 0 t
```

but this RFC recommends eliminating it from `toQOps` for v0.9.0.

## `applyQOp` semantics

```lean
def applyQOp (wqs : WorkerQueues) : QOp → WorkerQueues
  | .Push w t   => update worker w by appending t
  | .Pop w      => update worker w by removing the head/front corresponding to `schedule`
  | .Filter w t => update worker w by removing all occurrences of t
```

Because `WellFormed.readyQ_nodup` holds for reachable states, `Filter` should remove at most one task in the intended states. The implementation may use `List.filter` for simplicity.

## Correct `toQOps`

`toQOps` must be state-dependent and guard-compatible.

### Spawn

```lean
.spawn a
```

If valid, emits:

```lean
[.Push 0 s.nextId]
```

### SpawnChild

```lean
.spawnChild t a
```

If valid, emits:

```lean
[.Push 0 s.nextId]
```

### Schedule

If `s.readyQ = q :: qs`, emits:

```lean
[.Pop 0]
```

Otherwise emits `[]` and step should return `.invalid` or the current schedule result.

### Yield

If valid, emits:

```lean
[.Push 0 t]
```

### Wake

If valid and the target is sleeping, emits:

```lean
[.Push 0 t]
```

### Cancel

If valid, emits:

```lean
[.Filter 0 t]
```

This matches readyQ filtering.

### Send / Inject

If valid and target mailbox waiters are nonempty:

```lean
[.Push 0 w]
```

where `w` is the waiter head being woken.

If valid and there are no waiters:

```lean
[]
```

If invalid:

```lean
[]
```

The translation must check the same guards as `step`, especially:

- sender task is running for `send`;
- sender task is in `.running` state;
- sender task has an owner;
- target actor mailbox exists;
- `inject` target actor mailbox exists.

### Receive

`receive` has no ready-queue effect in either successful dequeue or parking branch:

```lean
[]
```

If the operation parks the running task, it clears `running` and changes `taskState`, but it does not append to or remove from `readyQ` because the task was already running and `running_not_in_readyQ` holds.

### Sleep

No ready-queue effect if applied to the running task, because the task is not in readyQ.

```lean
[]
```

### Tick

Use the tick argument, not `s.now`:

```lean
.tick t =>
  if s.now ≤ t then
    (Timer.expired s.timers t).filterMap fun e =>
      if s.taskState e.task == some .sleeping then some (.Push 0 e.task) else none
  else []
```

If `step` rejects backward ticks, `toQOps` must emit `[]` for backward ticks.

### Complete

No ready-queue effect when completing the running task.

```lean
[]
```

## Required theorems

### Translation validity

```lean
theorem toQOps_invalid_empty
    (h : (step s op).2 = .invalid) :
    toQOps s op = []
```

If this is too hard globally, prove per-operation versions and document any exception. The preferred acceptance target is the global theorem.

### Per-operation bridge preservation

At minimum:

```lean
bridge_spawn
bridge_spawnChild
bridge_schedule
bridge_yield
bridge_wake
bridge_cancel
bridge_send
bridge_inject
bridge_receive
bridge_sleep
bridge_tick
bridge_complete
```

Each theorem should have the form:

```lean
theorem bridge_op
    (hbs : BridgeState s wqs)
    (hwf : WellFormed s) :
    BridgeState (step s op).1 (applyQOps wqs (toQOps s op))
```

Use `WellFormed` because cases such as `cancel`, `receive`, and `sleep` rely on running/queue disjointness.

### Single-step bridge theorem

```lean
theorem bridge_step_single_worker
    (hbs : BridgeState s wqs)
    (hwf : WellFormed s) :
    BridgeState (step s op).1 (applyQOps wqs (toQOps s op))
```

### Trace theorem

The important headline:

```lean
theorem bridge_run_tracks_single_worker
    (ops : List RuntimeOp) :
    BridgeState
      (run RuntimeState.init ops)
      (applyQOpsList WorkerQueues.init (toQOpsTrace RuntimeState.init ops))
```

where `toQOpsTrace` threads the Henret state because `toQOps` is state-dependent:

```lean
def toQOpsTrace : RuntimeState → List RuntimeOp → List QOp
```

## Documentation updates

Create or update:

```text
docs/bridge-architecture.md
```

It must state:

- the bridge is single-worker;
- it relates `readyQ` only;
- it does not prove fairness or native execution;
- it does not model C race-freedom;
- multi-worker placement is deferred to RFC 043.

## Audit updates

Add bridge theorems to `scripts/axiom_audit.py` allowlist. Core bridge theorems should depend only on standard Lean axioms already allowed for the pure model.

## Acceptance criteria

- `toQOps .tick` uses the tick argument.
- `toQOps` is guard-compatible with `step` for all operations.
- No translated queue effect is emitted for invalid operations.
- All readyQ-changing operations have bridge preservation theorems.
- `bridge_schedule` exists.
- `bridge_step_single_worker` exists.
- `bridge_run_tracks_single_worker` exists or an explicitly equivalent trace theorem exists.
- Bridge theorem names are included in proof index and axiom audit.
- RFC 035 is documented as skeleton, RFC 036 as completion.

## Risks

### Exact-list `BridgeState` may be brittle

Exact list equality is strong and clean but sensitive to ordering. This is acceptable for single-worker semantics because Henret's `readyQ` is ordered. Do not weaken to set membership unless a concrete theorem becomes impossible.

### `Filter` may not exist in lean-runtime grammar

The bridge may introduce a Henret-local `QOp.Filter` even if the runtime model does not yet have it. That is acceptable for a semantic bridge, but documentation must say whether `Filter` is a bridge-only operation or a proposed lean-runtime operation.

## Non-goals

- Multi-worker bridge.
- Worker placement policy.
- Native deque verification.
- Fairness/liveness.
