# Bridge Architecture

**RFC 035** introduced the bridge skeleton. **RFC 036** completed the single-worker bridge.
This document describes what the bridge is, what it proves, and what it deliberately does not claim.

---

## What the bridge is

The bridge is a **queue projection**: it formally connects Henret's actor/task scheduler
state (`RuntimeState`) to the per-worker queue model used by `lean-runtime-workspace`.

`BridgeState s wqs` holds when Henret's `readyQ` equals worker 0's queue:

```lean
structure BridgeState (s : RuntimeState) (wqs : WorkerQueues) : Prop where
  queue_eq    : s.readyQ = wqs 0
  other_empty : ∀ w : WorkerIdx, w ≠ 0 → wqs w = []
```

This is a **single-worker projection**. All other workers are empty. Multi-worker extension
is deferred to RFC 043.

---

## The QOp grammar

`QOp` is the bridge queue-operation grammar. It mirrors the lean-runtime grammar and adds
`Filter` for cancellation semantics:

| QOp | Meaning | Used by single-worker `toQOps` |
|-----|---------|-------------------------------|
| `Push w t` | Append task `t` to worker `w`'s queue | ✓ |
| `Pop w` | Remove the head of worker `w`'s queue | ✓ |
| `Filter w t` | Remove all occurrences of `t` from worker `w`'s queue | ✓ |
| `Steal s d` | Move a task between workers | — (no-op; multi-worker only) |
| `Wake t` | Lean-runtime wake signal | — (not emitted; `applyQOp .Wake` is a no-op) |
| `Inject t` | Lean-runtime inject signal | — (not emitted by single-worker bridge) |

The single-worker `toQOps` translation only ever emits `Push 0 t`, `Pop 0`, and `Filter 0 t`.

---

## The translation: `toQOps`

`toQOps : RuntimeState → RuntimeOp → List QOp` translates each scheduler operation to its
queue effects. It is **guard-compatible**: if `step s op` returns `.invalid`, then
`toQOps s op = []`.

| RuntimeOp | Queue effect (valid) | Queue effect (invalid) |
|-----------|---------------------|----------------------|
| `spawn a` | `[Push 0 nextId]` | `[]` |
| `spawnChild t a` | `[Push 0 nextId]` | `[]` |
| `schedule` | `[Pop 0]` | `[]` |
| `yield t` | `[Push 0 t]` | `[]` |
| `wake t` | `[Push 0 t]` (if sleeping) | `[]` |
| `cancel t` | `[Filter 0 t]` (if non-terminal) | `[]` |
| `send t b m` | `[Push 0 w]` (if has waiter `w`) or `[]` | `[]` |
| `inject a m` | `[Push 0 w]` (if has waiter `w`) or `[]` | `[]` |
| `tick t` | `[Push 0 u₁, Push 0 u₂, ...]` (expired sleeping tasks) | `[]` (if `t < s.now`) |
| `complete t` | `[]` | `[]` |
| `receive t` | `[]` | `[]` |
| `sleep t d` | `[]` | `[]` |

**Tick**: uses the tick argument `t`, not `s.now`.

**Send/inject**: `toQOps` checks the same guards as `step` (running task, `.running` state,
owner, mailbox existence) before emitting any queue effect.

---

## Headline bridge theorems (RFC 036)

### Single-step bridge

```lean
theorem bridge_step_single_worker (s : RuntimeState) (op : RuntimeOp) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s op).1 (applyQOps wqs (toQOps s op))
```

For any `RuntimeOp`, if `BridgeState` holds before the step, it holds after, with the
translated queue effects applied. This is total over `RuntimeOp` — every
operation in the grammar is covered (most are queue-stable; the
ready-queue-affecting ones carry their `Push`/`Filter` translation).

### Trace bridge

```lean
theorem bridge_run_tracks_single_worker (ops : List RuntimeOp) :
    BridgeState
      (run RuntimeState.init ops)
      (applyQOps WorkerQueues.init (toQOpsTrace RuntimeState.init ops))
```

Running any sequence of operations from the initial state keeps `BridgeState`, with the
initial (empty) worker queues updated by all translated queue effects.
`toQOpsTrace` threads the state through the sequence because `toQOps` is state-dependent.

### General trace bridge

```lean
theorem bridge_run_general (s : RuntimeState) (wqs : WorkerQueues)
    (ops : List RuntimeOp) (hbs : BridgeState s wqs) :
    BridgeState (run s ops) (applyQOps wqs (toQOpsTrace s ops))
```

The trace theorem holds from any starting state that satisfies `BridgeState`, not just `init`.

---

## What the bridge proves

- Every scheduler operation (spawn, schedule, yield, complete, cancel, send, receive, inject,
  sleep, tick, wake, spawnChild) has a corresponding queue-operation translation.
- Applying the translated operations to the queue model tracks Henret's `readyQ` at every step.
- The queue projection is maintained through any sequence of operations from any reachable state.
- The `Filter` QOp (new in RFC 036) correctly models cancellation's `readyQ.filter` effect.

---

## What the bridge does not prove

**Not claimed:**

- **Fairness or liveness.** The bridge is a safety projection. It does not prove that tasks
  are eventually scheduled. Liveness reasoning requires additional policy assumptions (RFC 046).

- **Native execution correctness.** The bridge connects Henret's pure model to the queue
  model. It does not verify the C Chase-Lev deque implementation. That is a trusted layer
  with explicit axioms in `FFISpec.lean` and `Assumptions.lean`.

- **C11 data-race freedom.** RC discipline and memory-model safety of the C deque are outside
  the reach of Lean's logic. They are trusted design claims supported by differential/
  linearizability testing.

- **Actor semantics in the queue model.** The bridge relates only `readyQ`. Mailboxes,
  waiting state, timers, occurrence identity, and parenthood are not reflected in the
  `WorkerQueues` model.

- **Multi-worker correctness.** The current bridge is single-worker (`wqs 0` only). Task-to-
  worker assignment and work-stealing are not modeled here. See RFC 043.

---

## Relationship to the lean-runtime workspace

The `lean-runtime-workspace` package has its own `ModelSchedulerState`, `QOp` grammar, and
`qRun_tracks` parametric refinement theorem. The Henret bridge and the lean-runtime model are
**separate packages** (different Lake packages). The bridge is self-contained and does not
`import` the lean-runtime package.

The design intention is that the Henret bridge provides the semantic contract
(`BridgeState`, `bridge_step_single_worker`, `bridge_run_tracks_single_worker`) and the
lean-runtime package provides the machine-level execution (Chase-Lev deque, work-stealing,
C FFI) that claims to implement that contract. The formal connection between the two is the
next frontier (RFC 043, RFC 044).

---

## Source locations

| Concept | File |
|---------|------|
| `QOp`, `toQOps`, direct-effect lemmas | `Henret/Bridge/Grammar.lean` |
| `BridgeState`, `WorkerQueues`, `applyQOps`, `toQOpsTrace` | `Henret/Bridge/State.lean` |
| `bridge_step_single_worker`, `bridge_run_tracks_single_worker`, per-op theorems | `Henret/Bridge/Preservation.lean` |
| Bridge claims in proof/trust/test matrix | `docs/proof-trust-test-matrix.md` |
| Bridge theorems in proof index | `docs/proof-index.md` |
