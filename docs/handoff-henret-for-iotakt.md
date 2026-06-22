# Henret → iotakt Integration Handoff

> ⚠️ **HISTORICAL SNAPSHOT — do not treat as current.** This handoff was written
> against Henret **v0.6.0** (when `RuntimeOp` had 12 constructors and
> `RuntimeState` 10 fields). The model has since grown to 29 ops and a 33-field
> `WellFormed` invariant. The **live, authoritative sources** are the generated
> reference tables ([`runtime-op-table`](src/generated/runtime-op-table.md),
> [`wellformed-field-table`](src/generated/wellformed-field-table.md)) and the
> stable [integration contract](src/integration-contract.md). Use this document
> only as a record of the original iotakt bring-up, not as an API reference.

**Henret version:** v0.6.0  
**Lean toolchain:** `leanprover/lean4:v4.15.0`  
**Package name:** `henret`  
**Date:** 2026-06-08  
**Audience:** iotakt developer  
**Status of planned items:** sections marked `[PLANNED]` describe intended future work, not current behavior. Do not implement iotakt against planned items until the corresponding Henret RFC ships.

---

## Contents

1. Version and Compatibility Sheet
2. Public API Table
3. Runtime Operation Grammar
4. Runtime State Model
5. Message, Mailbox, Send, Receive, and Inject Semantics
6. Driver-Loop Integration Contract
7. Timer and Logical-Time Contract
8. Blocked-State and Wait-Queue Note
9. Actor/Task Ownership Rules
10. Proof Index for iotakt
11. Proof/Trust/Test Matrix for iotakt
12. Import and Module Stability Map
13. Test Fixtures and Executable Examples
14. Native Boundary Interaction Note
15. Known Gaps and Future Dependencies
16. Change-Control and Compatibility Policy

---

## 1. Version and Compatibility Sheet

| Item | Value |
|---|---|
| Henret version | v0.6.0 |
| Lean toolchain | `leanprover/lean4:v4.15.0` |
| Lake package name | `henret` |
| Supported build mode | Lean-only core; optional native boundary (`Henret.Native.*`). iotakt should depend only on the Lean-only core. |
| Minimum iotakt import | `import Henret` |
| Public stable modules | `Henret`, `Henret.Scheduler.Op`, `Henret.Scheduler.Model`, `Henret.Scheduler.Driver` |
| Provisional modules | `Henret.Proofs.*`, `Henret.Refinement.*` (stable as theorems, names subject to minor revision) |
| Internal modules — do not import | `Henret.Proofs.Preservation.*`, `Henret.Proofs.StepProjections`, `Henret.Core.*`, `Henret.Actor.*`, any file under `Henret/Proofs/Preservation/` |
| Breaking-change policy | Operation grammar changes, message type changes, and public theorem renames require a CHANGELOG entry and a minor version bump. See §16. |
| License | Apache-2.0. Author: nabbisen. NOTICE file included in release archive. |

---

## 2. Public API Table

All symbols below are stable in v0.6.0 unless marked `[PROVISIONAL]` or `[PLANNED]`.

### Core types

| Module | Symbol | Kind | Signature | Stability | iotakt Use | Semantics |
|---|---|---|---|---|---|---|
| `Henret.Core.Id` | `ActorId` | abbrev | `Nat` | Stable | Key for mailbox delivery and ownership lookup | Opaque identity; allocation is external to iotakt |
| `Henret.Core.Id` | `TaskId` | abbrev | `Nat` | Stable | Correlate I/O task with scheduler task | Monotone; assigned by `step (.spawn _)` |
| `Henret.Actor.Mailbox` | `Message` | structure | `{ id : Nat, payload : Nat }` | Provisional | Wrap I/O readiness payloads | Fixed two-`Nat` envelope. See §5 for iotakt adaptation pattern. |
| `Henret.Actor.Mailbox` | `Mailbox` | type | opaque | Stable | Read mailbox state in assertions | FIFO queue of `Message`; use `dequeue`/`enqueue` |
| `Henret.Scheduler.Op` | `RuntimeOp` | inductive | 12 constructors — see §3 | Stable | Construct step commands | Each constructor maps to one scheduler action |
| `Henret.Scheduler.Model` | `TaskState` | inductive | `.new \| .ready \| .running \| .yielded \| .sleeping \| .completed \| .cancelled \| .waiting` | Stable | Observe task lifecycle in tests/assertions | Monotone; terminal states `.completed`/`.cancelled` cannot regress |
| `Henret.Scheduler.Model` | `StepResult` | inductive | `.ok \| .spawned t \| .scheduled t \| .received m \| .blocked \| .woke ts \| .invalid` | Stable | Detect blocking, inject-wakeup, and invalid outcomes | `.invalid` always means state is unchanged |
| `Henret.Scheduler.Model` | `RuntimeState` | structure | 10 fields — see §4 | Stable | Read state for driver logic | Immutable pure value; never mutate fields directly |
| `Henret.Scheduler.Model` | `TimerEntry` | structure | `{ deadline : Nat, task : TaskId }` | Stable | Compute next epoll timeout | `s.timers` is a sorted list of pending sleep entries |

### Core functions

| Module | Symbol | Signature | Stability | iotakt Use | Semantics |
|---|---|---|---|---|---|
| `Henret.Scheduler.Model` | `step` | `RuntimeState → RuntimeOp → RuntimeState × StepResult` | Stable | Execute one operation | Total, pure. Returns new state and result. Invalid input → unchanged state + `.invalid`. |
| `Henret.Scheduler.Model` | `run` | `RuntimeState → List RuntimeOp → RuntimeState` | Stable | Execute a batch of operations | `foldl step`. Result state only; results discarded. |
| `Henret.Scheduler.Model` | `RuntimeState.init` | `RuntimeState` | Stable | Initial state for a fresh runtime | All fields empty/zero. |
| `Henret.Scheduler.Driver` | `drain` | `RuntimeState → RuntimeState` | Stable | Run all ready tasks to completion | Runs scheduler until `readyQ` is empty. Returns drained state. See §6. |
| `Henret.Scheduler.Driver` | `driveOps` | `Nat → RuntimeState → RuntimeState` | Stable | Fuel-bounded scheduler round-robin | Applies schedule/yield/complete loop up to `n` rounds. |
| `Mailbox` | `Mailbox.dequeue` | `Mailbox → Option (Message × Mailbox)` | Stable | Inspect head message in tests | Returns `none` if empty |
| `Mailbox` | `Mailbox.enqueue` | `Mailbox → Message → Mailbox` | Stable | Build test states | Appends to tail |

### Key predicates

| Module | Symbol | Signature | Stability | iotakt Use |
|---|---|---|---|---|
| `Henret.Proofs.Invariants` | `WellFormed` | `RuntimeState → Prop` | Stable | Assert invariant holds in constructed states; required to invoke `step_preserves_*` theorems |
| `Henret.Proofs.Invariants` | `wf_init` | `WellFormed RuntimeState.init` | Stable | Initial state satisfies invariants |
| `Henret.Proofs.InvariantsPreservation` | `reachable_wf` | `∀ ops, WellFormed (run init ops)` | Stable | All reachable states satisfy invariants; iotakt may rely on this unconditionally |
| `Henret.Scheduler.Driver` | `Drainable` | `TaskState → Prop` | Stable | `.new ∨ .ready ∨ .yielded ∨ .completed` — states that drain will consume |

---

## 3. Runtime Operation Grammar

`step s op` is total for all `s : RuntimeState` and all `op : RuntimeOp`. An invalid precondition always returns `(s, .invalid)` — the state is unchanged. Proved by `step_invalid_unchanged`.

| `RuntimeOp` | Parameters | Preconditions (else `.invalid`) | State Mutation | `StepResult` | iotakt Relevance |
|---|---|---|---|---|---|
| `spawn a` | `a : ActorId` | none | allocates `t = s.nextId` with `.new` state, `taskOwner t = a`, increments `nextId`; creates mailbox if `a` has none | `.spawned t` | iotakt spawns one task per managed connection/fd; maps `FdKey → TaskId` |
| `schedule` | — | `s.running = none ∧ s.readyQ` nonempty ∧ head is `.new`/`.ready`/`.yielded` | pops `readyQ` head → `.running`; sets `s.running` | `.scheduled t` | driver calls between inject and receive |
| `yield t` | `t : TaskId` | `s.running = some t ∧ taskState t = .running` | `t → .ready`, re-enqueues, clears running slot | `.ok` | not directly issued by iotakt |
| `complete t` | `t : TaskId` | `s.running = some t ∧ taskState t = .running` | `t → .completed`, clears running, removes timer | `.ok` | signals task finished; iotakt observes completion to reclaim fd |
| `cancel t` | `t : TaskId` | `taskState t ≠ none ∧ not terminal` | `t → .cancelled`, removed from readyQ, timer dropped | `.ok` | iotakt may cancel on connection close |
| **`send t b m`** | `t : TaskId`, `b : ActorId`, `m : Message` | `s.running = some t ∧ taskState t = .running ∧ taskOwner t ≠ none` | appends `m` to `mailboxes b`; if `mailboxWaiters b` nonempty, wakes head waiter → `.ready`, prepends to readyQ | `.ok` | task-to-actor delivery; requires caller to be running. **Not for external I/O delivery — use `inject`.** |
| **`receive t`** | `t : TaskId` | `s.running = some t ∧ taskState t = .running ∧ taskOwner t ≠ none` | if mailbox nonempty: dequeues head message, state unchanged. If mailbox empty: `t → .waiting`, clears running, appends `t` to `mailboxWaiters a`. | `.received m` or `.blocked` | task-side consume; iotakt does not issue this directly |
| **`inject a m`** | `a : ActorId`, `m : Message` | none — always valid if `a` exists in `mailboxes` | appends `m` to `mailboxes a`; if `mailboxWaiters a` nonempty, wakes head waiter → `.ready`, prepends to readyQ. If `a` has no mailbox: creates empty mailbox first, then appends. | `.ok` or `.woke [t, ...]` | **Primary external delivery path.** iotakt issues `inject a ioMsg` for each I/O readiness event. No precondition on task state. |
| `sleep t d` | `t : TaskId`, `d : Nat` | `s.running = some t ∧ taskState t = .running ∧ t ∉ timer tasks` | `t → .sleeping`; inserts `TimerEntry { deadline := d, task := t }` sorted into `s.timers`; clears running | `.ok` | I/O timeout pattern: task issues `sleep t deadline` then blocks on inject-readiness |
| `tick now` | `now : Nat` | `s.now ≤ now` (else `.invalid` + no-op) | advances `s.now := now`; all tasks with `deadline ≤ now → .ready`, prepended to readyQ; expired timers removed | `.woke [...]` | iotakt calls after `epoll_wait` returns; pass `now` = current monotonic ms |
| `wake t` | `t : TaskId` | `taskState t = .sleeping` | `t → .ready`, appended to readyQ, timer removed | `.ok` | manual wakeup; iotakt uses `tick` for timer-driven wakeup |
| `spawnChild t a` | `t : TaskId`, `a : ActorId` | `s.running = some t ∧ taskState t = .running ∧ taskOwner t ≠ none ∧ taskState nextId = none` | allocates child `nextId` as `.new`, sets `taskParent`, `taskOwner := a`, appends to readyQ | `.spawned nextId` | supervision tree; `[PLANNED]` — not yet used in iotakt v0.1 |

### Answers to iotakt-specific questions

**Does `send` schedule or wake a blocked task?** Yes — if `mailboxWaiters b` is nonempty, `send` wakes the head waiter and prepends it to `readyQ`. It does not require a separate `tick` or `wake` call.

**Does `inject` bypass actor ownership checks?** Yes. `inject a m` requires no running task and no ownership relationship. It is the correct primitive for external event delivery.

**Does `inject` append, create a task, or mark runnable?** It appends one message to `mailboxes a`. If a waiter exists it also wakes one task to `.ready`. It never creates a new task.

**What if the target actor has no mailbox (`s.mailboxes a = none`)?** `inject` creates an empty mailbox for `a` before appending. The inject always succeeds. See `inject_appends`.

**What if the target actor's task is cancelled or completed?** `inject` still succeeds — the message is placed in the mailbox. No waiter will be woken (terminal tasks are not in `mailboxWaiters`). The message sits unread. iotakt should guard against injecting to actors with no live tasks.

**Is blocked receive a no-op?** No. Since v0.5.0 (RFC 031), a receive on an empty own mailbox is a **parking transition**: the task enters `TaskState.waiting`, is appended to `mailboxWaiters a`, and the running slot is cleared. See §8 for the full current behavior.

---

## 4. Runtime State Model

`RuntimeState` is a pure immutable Lean structure. `step` returns a new value; it never mutates in place.

| Field | Type | Semantics | iotakt Access Pattern |
|---|---|---|---|
| `taskState` | `TaskId → Option TaskState` | Lifecycle state of each task. `none` = not yet allocated. | Read to detect `.waiting` → deliver inject |
| `taskOwner` | `TaskId → Option ActorId` | Owning actor of each task. Set at spawn, immutable forever. | Read to map `TaskId → ActorId` for inject target |
| `readyQ` | `List TaskId` | FIFO queue of runnable tasks. Nodup invariant holds. | Read to detect "no work"; empty → poll I/O |
| `running` | `Option TaskId` | At most one running task at a time. `none` = idle. | Read to detect idle slot before schedule |
| `timers` | `List TimerEntry` | Sorted ascending by `deadline`. Tasks with `taskState = .sleeping`. | Read to compute next epoll timeout (see §7) |
| `mailboxes` | `ActorId → Option Mailbox` | Per-actor FIFO message queue. `none` = actor has no mailbox yet. | inject target check |
| `mailboxWaiters` | `ActorId → List TaskId` | Tasks parked waiting on `a`'s mailbox. Nodup; all have `taskState = .waiting`. | Read to detect whether inject will wake a waiter |
| `now` | `Nat` | Logical time. Monotone. Updated only by `tick`. | Read to compute elapsed time for timeout |
| `taskParent` | `TaskId → Option TaskId` | Supervision parent. `none` = root task. | Ignore in iotakt v0.1 |
| `nextId` | `TaskId` | Next free `TaskId`. Never decreases. | Do not use directly; read `StepResult.spawned t` instead |

### iotakt-specific answers

**Can iotakt detect a drained runtime?** Yes: `s.readyQ.isEmpty ∧ s.running = none` means no runnable work. The `drain` function brings any state to this condition.

**Public drain API?** `drain : RuntimeState → RuntimeState` (proved total and correct by `drain_completes`, `drain_empties`). Alternatively, call `step s .schedule` in a loop until `.invalid` is returned.

**How should iotakt detect when to poll I/O?** When `s.readyQ.isEmpty ∧ s.running = none` after draining. Then compute timeout from `s.timers` (see §7) and call `epoll_wait`.

**Can iotakt query the next timer deadline?** There is no `nextDeadline` function on `RuntimeState`. iotakt should compute `s.timers.head?.map (·.deadline)` directly — the list is sorted ascending, so head is earliest. This access pattern is stable. A convenience helper may be added in a future Henret RFC.

---

## 5. Message, Mailbox, Send, Receive, and Inject Semantics

### Mailbox ownership

Each actor `a : ActorId` has at most one mailbox: `s.mailboxes a : Option Mailbox`. Mailboxes are per-actor, not per-task. A task receives from its owning actor's mailbox only (`receive_only_own`).

### Message type

```lean
structure Message where
  id      : Nat
  payload : Nat
```

The `Message` type is fixed to two `Nat` fields. **This is a known gap for iotakt.** iotakt must encode I/O readiness as a `Message`. Recommended encoding:

```lean
-- iotakt convention (not a Henret typedef):
-- id      = fd or connection handle (cast to Nat)
-- payload = event kind bitmask (e.g. 1=readable, 2=writable, 4=error, 8=hangup)
```

Alternatively, define a wrapper and a codec:

```lean
structure IoMessage where
  fd      : Nat     -- FdKey cast to Nat
  interest : Nat    -- readiness bitmask

def IoMessage.toMessage (io : IoMessage) : Message :=
  { id := io.fd, payload := io.interest }
```

Henret RFC 033 (`rfcs/proposed/033-message-envelope-occurrence-identity.md`) proposes a more expressive message envelope. iotakt should not depend on the current two-`Nat` layout being permanent.

### Message ordering

Mailboxes are strict FIFO. `send` and `inject` append to tail; `receive` dequeues head. This is proved by `send_appends`, `inject_appends`, `receive_consumes_one`.

### Send vs inject

| | `send t b m` | `inject a m` |
|---|---|---|
| Who calls it | The running task `t` | The external driver (iotakt) |
| Requires running task | Yes (`s.running = some t`) | No |
| Target identified by | Actor `b` (any actor) | Actor `a` directly |
| Owns the message | Task `t`'s execution context | External I/O event |
| Use in iotakt | Never | Always |

**Rule: iotakt always uses `inject`, never `send`.**

### Receive semantics

`receive t`:
- If `mailboxes (taskOwner t)` is nonempty: dequeues head, returns `StepResult.received m`, all other state unchanged.
- If mailbox is empty: parks `t` as `TaskState.waiting`, appends to `mailboxWaiters (taskOwner t)`, clears running slot, returns `StepResult.blocked`. No message consumed.
- If `t` is not running or has no owner: returns `StepResult.invalid`, state unchanged.

**Mesa-semantics note**: when `inject` wakes a waiting task, the task transitions to `.ready` but the message remains in the mailbox. The task must re-issue `receive` after being scheduled to consume the message. There is no direct handoff.

### Inject semantics (full)

`inject a m`:
1. If `s.mailboxes a = none`: creates `Mailbox.empty` for `a`.
2. Appends `m` to `mailboxes a`.
3. If `mailboxWaiters a` is nonempty: wakes the head waiter `t`, sets `t → .ready`, prepends `t` to `readyQ`, removes `t` from `mailboxWaiters a`. Result: `StepResult.woke [t]`.
4. If `mailboxWaiters a` is empty: result `StepResult.ok`.

State of target task has no effect on inject. If `a`'s only task is `.completed` or `.cancelled`, the inject succeeds but no waiter is woken.

### Invalid target behavior

- `inject` with `a` never fails. It always creates a mailbox if needed and appends.
- `send` with a non-running sender: `.invalid`, state unchanged.
- `receive` on a non-running task: `.invalid`, state unchanged.

### Cancellation and completion interaction

- Messages accumulate in `mailboxes a` even if `a`'s task is terminal.
- Mailboxes are not garbage-collected by `cancel` or `complete`.
- iotakt should track whether a task is terminal before injecting if it wishes to avoid orphan messages.

---

## 6. Driver-Loop Integration Contract

The intended iotakt driver loop is compatible with Henret v0.6.0 semantics:

```
loop:
  s ← drain s                       -- run all ready work to completion
  if s.readyQ.isEmpty ∧ s.running = none:
    timeout ← nextDeadline s        -- s.timers.head?.map (·.deadline)
    events ← epoll_wait(fds, timeout)
    for each event:
      s ← step s (.inject (fdToActor event.fd) (encodeEvent event))
    if timerExpired:
      s ← step s (.tick currentMonotonicMs)
```

**Drain call**: Use `drain s` for the first stage. It is proved by `drain_completes`/`drain_empties` to run all tasks with drainable states to completion and empty `readyQ`. Alternatively call `step s .schedule` in a loop until `.invalid`.

**Single-threaded requirement**: Henret state is a pure value. There are no background threads. The driver loop must be the sole writer. No locking is needed or meaningful.

**No-runnable-task handling**: `step s .schedule` returns `(s, .invalid)` when `s.readyQ` is empty. The driver should check `s.readyQ.isEmpty` before calling schedule, or treat `.invalid` from schedule as the idle signal.

**Timer-only wakeups**: After `epoll_wait` returns due to timeout (no I/O events), call `tick currentMonotonicMs` to wake sleeping tasks whose deadlines have passed.

**Deterministic traces**: A sequence of `RuntimeOp` values fully describes a Henret execution. For replay/testing, record the list of ops issued by the driver loop. `run RuntimeState.init ops` replays exactly.

**How to represent external events deterministically**: Use `inject a (IoMessage.toMessage event)` as the canonical trace representation. The `ActorId → FdKey` mapping is iotakt's responsibility; Henret does not see it.

**`run` vs step-by-step**: For driver logic, step-by-step with the result gives the most information (`.woke`, `.blocked`, etc.). `run` discards results; use it only for bulk setup or testing.

---

## 7. Timer and Logical-Time Contract

| Topic | Detail |
|---|---|
| Time representation | `Nat` (logical, monotone). Proved monotone by `step_clock_monotone`. |
| `tick now` semantics | Sets `s.now := now` if `now ≥ s.now`; wakes all tasks with `deadline ≤ now`. Returns `.woke [tasks]`. |
| Backward tick | `tick now` with `now < s.now` returns `(s, .invalid)` and leaves state unchanged. Proved by `tick_backwards_invalid`. |
| Timer sortedness | `s.timers` is sorted ascending by `deadline`. Invariant held by all operations. Proved by `reachable_timers_sorted`. |
| Next deadline access | No public API function. Read `s.timers.head?.map (·.deadline)` directly. Returns `none` if no sleeping tasks. |
| Wall-clock relation | Undefined in Henret. iotakt must define its own mapping from OS monotonic time to Nat. Recommended: milliseconds since driver start, cast to Nat. |
| Timeout calculation for epoll | `nextDeadline = s.timers.head?.map (fun e => e.deadline - s.now)`. If `none`, epoll may block indefinitely until I/O events arrive. |
| No-early-wake guarantee | A sleeping task is never woken before its deadline. Proved by `tick_no_early_wake`. |
| Wakes-expired guarantee | A sleeping task with `deadline ≤ now` is always woken by `tick now`. Proved by `tick_wakes_expired`. |

**iotakt timeout policy**: `epoll_wait` timeout = `nextDeadline s`. When timeout fires: call `tick (s.now + elapsed_ms)`. Henret will wake all expired tasks.

---

## 8. Blocked-State and Wait-Queue Note

**This section is critical. Read it before designing the iotakt receive flow.**

### Current state (v0.6.0, RFC 031 complete)

A blocked receive is **not a no-op**. Since v0.5.0, empty-mailbox receive is a **parking transition**:

- `receive t` on empty mailbox → `t` enters `TaskState.waiting`, appended to `mailboxWaiters (taskOwner t)`, running slot cleared, result `.blocked`.
- When any subsequent `inject a m` or `send _ a m` finds `mailboxWaiters a` nonempty, it wakes the head waiter → `.ready`, prepends to `readyQ`.
- The woken task must re-issue `receive` after being scheduled (Mesa semantics — no direct handoff).

This is proved by `receive_empty_parks`, `receive_blocked_parks`, `reachable_waiters_exact`, `reachable_waiter_actor_unique`.

### What iotakt should assume in v0.1

iotakt v0.1 should use the following pattern:

```
1. spawn actor/task for each connection (FdKey → ActorId → TaskId)
2. task issues receive → if mailbox empty: parks in .waiting
3. iotakt driver: epoll readiness event arrives
4. iotakt driver: inject a (encodeReadiness event)
   → inject wakes waiting task → .ready → driver drains → task issues receive → consumes message
```

This is the correct and complete integration pattern. No special iotakt handling of `.waiting` state is needed; `inject` does the wakeup automatically.

### What iotakt must NOT assume

- Do not assume `.blocked` means the task is still running. It is not; the task has been parked.
- Do not assume `inject` is needed only when a task is `.waiting`. `inject` may be issued at any time; if no waiter exists, the message queues for the next `receive`.
- Do not assume the wait queue is LIFO. It is FIFO (head is woken).

### Future changes `[PLANNED]`

Selective receive, multi-actor waiting, and priority queues are out of scope for Henret v0.6.x. If added, they will be introduced under a new RFC and will not break the single-actor-wait discipline.

---

## 9. Actor/Task Ownership Rules

| Question | Answer |
|---|---|
| Does every task have exactly one owning actor? | Yes. Every allocated task has `taskOwner t = some a` from the moment `spawn a` runs. Proved by `reachable_spawned_has_owner`. |
| Can ownership change after spawn? | No. `taskOwner` is immutable after assignment. Proved by `run_preserves_owner` (via `WellFormed.spawned_has_owner` + `reachable_wf`). |
| Is ownership in public state? | Yes: `s.taskOwner : TaskId → Option ActorId`. |
| Can a message be delivered to an actor with no runnable task? | Yes. `inject a m` always succeeds. The message queues in `mailboxes a`. |
| What happens if the owner actor has no live task? | The message queues indefinitely. Henret does not garbage-collect mailboxes. |
| What happens to mailboxes on cancel/complete? | Mailboxes are not cleared. The actor retains its mailbox. Messages sent to a dead task's actor are not delivered but are not dropped either. |
| Is actor identity stable? | Yes. `ActorId = Nat`. Once assigned via `spawn a`, `a` names the same mailbox forever within a runtime instance. |

### iotakt FdKey → ActorId mapping

iotakt should maintain a table:

```
FdKey → ActorId
```

This mapping is iotakt's responsibility. Henret does not see `FdKey`. Recommended: use the file-descriptor integer directly as `ActorId`, or allocate `ActorId` from a monotone counter that iotakt owns.

The mapping is sound because:
1. `ActorId` is immutable once assigned.
2. `taskOwner` never changes after spawn.
3. `inject a m` always succeeds (even if `a` has no live tasks).

---

## 10. Proof Index for iotakt

All theorems below are in `import Henret` and stable in v0.6.0.

| Theorem | Module | Statement (abbreviated) | iotakt Relevance |
|---|---|---|---|
| `step_invalid_unchanged` | `Henret.Proofs.Ownership` | `step s op = (_, .invalid) → step s op = (s, _)` | Stale or invalid inject is a safe no-op |
| `reachable_wf` | `Henret.Proofs.InvariantsPreservation` | `WellFormed (run init ops)` | All driver-loop states satisfy invariants |
| `receive_only_own` | `Henret.Proofs.Messaging` | A successful receive dequeues from `taskOwner t`'s mailbox only | iotakt delivers to owning actor, never another |
| `send_appends` | `Henret.Proofs.Messaging` | `send t b m` appends exactly `m` to `mailboxes b` | Send does not reorder or duplicate |
| `receive_consumes_one` | `Henret.Proofs.Messaging` | Non-empty receive removes exactly the head message | No message loss or duplication |
| `inject_appends` | `Henret.Proofs.Messaging` | `inject a m` appends `m` to `mailboxes a` | External delivery appends; safe at all times |
| `inject_preserves_other` | `Henret.Proofs.Messaging` | `inject a m` does not touch `mailboxes b` for `b ≠ a` | Inject does not cross actor boundaries |
| `receive_empty_parks` | `Henret.Proofs.Messaging` | Empty receive → task enters `.waiting`, appended to `mailboxWaiters` | iotakt driver relies on this for the inject-wakeup loop |
| `receive_blocked_parks` | `Henret.Proofs.Messaging` | Result-driven form: `.blocked` result ↔ full parking transition | Guards the Mesa-wakeup pattern |
| `tick_no_early_wake` | `Henret.Proofs.Timers` | `tick now` does not wake tasks with `deadline > now` | epoll timeout calculation is safe |
| `tick_wakes_expired` | `Henret.Proofs.Timers` | All tasks with `deadline ≤ now` are woken by `tick now` | Timer-driven I/O wakeup is complete |
| `tick_backwards_invalid` | `Henret.Proofs.Timers` | `tick now` with `now < s.now` is a no-op | Stale OS timestamp is safe |
| `step_clock_monotone` | `Henret.Proofs.Timers` | `s.now ≤ (step s op).1.now` for all ops | Logical time never decreases |
| `WellFormed.readyQ_nodup` | `Henret.Proofs.Invariants` | `readyQ` contains no duplicates | Ready queue can be safely scanned |
| `reachable_runnable_is_queued` | `Henret.Proofs.InvariantsPreservation` | Every runnable task appears in `readyQ` | No task is runnable but invisible |
| `reachable_queue_exact` | `Henret.Proofs.InvariantsPreservation` | `readyQ` contains exactly the runnable tasks | `readyQ.isEmpty` is a sound idle check |
| `reachable_spawned_has_owner` | `Henret.Proofs.InvariantsPreservation` | Every allocated task has `taskOwner t = some a` | FdKey → ActorId → TaskId mapping is sound |
| `step_preserves_cancelled` | `Henret.Proofs.Ownership` | Cancelled tasks stay cancelled through all operations | Cancel is safe and final |
| `step_preserves_completed` | `Henret.Proofs.Ownership` | Completed tasks stay completed | Completion is terminal |
| `drain_completes` | `Henret.Scheduler.Driver` | `drain s` completes all `Drainable` tasks in `readyQ` | Driver loop terminates correctly |
| `drain_empties` | `Henret.Scheduler.Driver` | `(drain s).readyQ = []` | After drain, poll I/O |
| `reachable_waiters_exact` | `Henret.Proofs.InvariantsPreservation` | `mailboxWaiters a` contains exactly the `.waiting` tasks for `a` | Wait queue reflects real waiting tasks |

---

## 11. Proof/Trust/Test Matrix for iotakt Integration

| Claim | Status | Evidence | iotakt Impact |
|---|---|---|---|
| `step` is total and pure | PROVEN | Type signature; `step : RuntimeState → RuntimeOp → RuntimeState × StepResult` | iotakt may use deterministic traces unconditionally |
| Invalid operation is a state no-op | PROVEN | `step_invalid_unchanged` | Stale or mis-timed inject/tick is safe |
| Inject always succeeds (mailbox created if absent) | PROVEN | `inject_appends`; `preserves_wf_inject` | iotakt does not need to guard inject calls |
| Empty receive parks the task | PROVEN | `receive_empty_parks`, `receive_blocked_parks` | iotakt Mesa-wakeup pattern is sound |
| Inject wakes at most one waiter (head of queue) | PROVEN | `reachable_waiters_exact`, `preserves_wf_inject` | No unintended multi-wakeup |
| Timer: no early wake | PROVEN | `tick_no_early_wake` | epoll timeout computation is safe |
| Timer: all expired tasks woken | PROVEN | `tick_wakes_expired` | Timer-driven completion is correct |
| Clock monotonicity | PROVEN | `step_clock_monotone`, `tick_backwards_invalid` | Stale OS timestamp is a safe no-op |
| Ownership immutability | PROVEN | `reachable_spawned_has_owner`, `WellFormed.spawned_has_owner` | FdKey → ActorId mapping is stable |
| Message ordering (FIFO) | PROVEN | `send_appends`, `inject_appends`, `receive_consumes_one` | No message reordering |
| Actor-local receive discipline | PROVEN | `receive_only_own` | iotakt cannot accidentally cross actor boundaries |
| Ready queue uniqueness | PROVEN | `WellFormed.readyQ_nodup` | Scheduler state is consistent |
| All reachable states well-formed | PROVEN | `reachable_wf` | Driver loop may rely on all invariants without checking |
| Native deque model (optional boundary) | ASSUMED + TESTED | `Henret.Native.Assumptions`; `FFISpec` axioms | iotakt must not inherit these assumptions; maintain own boundary |
| OS timer accuracy | OUT OF SCOPE | N/A — Henret is a logical-time model | iotakt owns wall-clock → logical-time mapping |
| epoll correctness | OUT OF SCOPE | N/A | iotakt owns OS interface |
| Message payload semantics | OUT OF SCOPE | `Message.id`/`Message.payload` are plain `Nat` | iotakt owns `FdKey`/event encoding; Henret does not interpret payload |
| GC of cancelled/completed mailboxes | NOT PROVEN — no GC exists | State accumulates | iotakt must track live actors externally if memory matters |

---

## 12. Import and Module Stability Map

### Stable public modules (iotakt may import)

```
Henret                                  -- umbrella: Op + Model + Proofs + Refinement
Henret.Model                            -- lighter umbrella: Op + Model only (no proofs)
Henret.Scheduler.Op                     -- RuntimeOp type only
Henret.Scheduler.Model                  -- RuntimeState, step, run, init, TaskState, StepResult
Henret.Scheduler.Driver                 -- drain, driveOps, Drainable
Henret.Proofs.InvariantsPreservation    -- reachable_wf and key reachable_* theorems
```

### Provisional modules (names stable, minor signature changes possible)

```
Henret.Proofs.Messaging                 -- send/receive/inject theorems
Henret.Proofs.Timers                    -- tick/sleep/wake theorems
Henret.Proofs.Ownership                 -- step_preserves_*, step_invalid_unchanged
Henret.Proofs.Invariants                -- WellFormed definition and field names
```

### Internal — do not import

```
Henret.Proofs.Preservation.*            -- internal preservation machinery
Henret.Proofs.StepProjections           -- internal projection helpers
Henret.Core.*                           -- primitive type definitions, imported transitively
Henret.Actor.*                          -- mailbox internals, imported transitively
Henret.Refinement.*                     -- backend contract; not needed by iotakt v0.1
Henret.Native.*                         -- optional native boundary; see §14
Henret.Examples.*                       -- demo only; not for production import
```

### Recommended minimum import

```lean
-- In iotakt source:
import Henret.Model    -- RuntimeState, step, run, TaskState, StepResult, RuntimeOp
```

If theorem names are needed for iotakt proofs:

```lean
import Henret          -- adds all proof modules
```

---

## 13. Test Fixtures and Executable Examples

All fixtures are in `Henret/Examples/Basic.lean` and `Main.lean`. They are verified by `native_decide` or the demo binary (`lake exe henret-demo`), which exits non-zero on failure.

| # | Fixture | Source | Expected Result | CI | iotakt may vendor |
|---|---|---|---|---|---|
| 1 | Spawn actor, schedule, complete | `Main.lean` scenario 1 | `taskState 0 = .completed` | Yes (demo) | Yes |
| 2 | Send message, receive message | `Main.lean` scenario 2 | message consumed from mailbox | Yes | Yes |
| 3 | Sleep, tick wakes exactly expired tasks | `Main.lean` scenario 3 | `taskState 1 = .ready` at `tick 7` with `deadline 5` | Yes | Yes |
| 4 | Cancel, verify terminal | `Main.lean` scenario 4 | `taskState 0 = .cancelled` forever | Yes | Yes |
| 5 | Drain all spawned tasks | `Main.lean` scenario 5 | all `readyQ` tasks → `.completed` | Yes | Yes |
| 6 | Ownership immutable; backwards tick no-op; stale timer safe | `Main.lean` scenario 6 | see inline checks | Yes | Yes |
| 7 | Blocked receive → inject → wake → re-receive → consume (Mesa) | `Main.lean` scenario 7 | full parking round-trip; 12 checks | Yes | **Recommended — this is the core iotakt pattern** |
| 8 | `spawnChild` parent chain | `Main.lean` scenario 8 | `taskParent 1 = some 0` | Yes | Optional |

### Recommended iotakt bootstrap trace

Copy/adapt scenario 7 as the starting point for iotakt's integration test:

```lean
-- Spawn a task owned by actor 7 (represents a socket fd)
let s0 := run RuntimeState.init [.spawn 7, .schedule]
-- Task issues receive → parks (empty mailbox)
let (s1, r1) := step s0 (.receive 0)
-- r1 = .blocked; s1.taskState 0 = .waiting
-- OS readiness event arrives: inject I/O message into actor 7's mailbox
let (s2, r2) := step s1 (.inject 7 { id := 42, payload := 1 })
-- r2 = .woke [0]; task 0 re-queued as .ready
-- Driver drains: schedules task 0, task re-issues receive and consumes
let s3 := run s2 [.schedule]
let (s4, r4) := step s3 (.receive 0)
-- r4 = .received { id := 42, payload := 1 }
```

---

## 14. Native Boundary Interaction Note

### iotakt v0.1 policy

**iotakt should depend only on `Henret.Model` (Lean-only core). Do not import `Henret.Native.*`.**

### What `Henret.Native` is

`Henret.Native.DequeModel` and `Henret.Native.Assumptions` define the FFI boundary between the Lean model and C-level native implementations (work-stealing deque, epoll reactor). They use four `axiom`-declared `FFISpec` assumptions that are not kernel-proven.

### Why iotakt must not depend on it

1. `Henret.Native` axioms are ASSUMED, not PROVEN. iotakt inheriting them without review would make iotakt's own safety claims weaker than they should be.
2. iotakt will define its own native boundary (epoll FFI, socket lifecycle). Those assumptions belong in iotakt's own `FFISpec`, not inherited from Henret.
3. Native boundary integration requires an explicit RFC that jointly defines the interface.

### Future integration `[PLANNED]`

A future RFC may define a joint native boundary between `Henret.Native` and iotakt's epoll layer. Until that RFC ships, iotakt maintains a strictly separate native boundary.

---

## 15. Known Gaps and Future Dependencies

| Gap | Current Status | iotakt Impact | Workaround | Future RFC |
|---|---|---|---|---|
| Message type is `{ id: Nat, payload: Nat }` | Fixed in v0.6.0 | iotakt cannot directly express `FdKey + IoInterest` without encoding | Encode `fd` as `id`, `event bitmask` as `payload`. Define `IoMessage.toMessage` codec. | RFC 033 (proposed): message envelope / occurrence identity |
| No `nextDeadline` public helper | Absent | iotakt must compute `s.timers.head?.map (·.deadline)` inline | Direct field access is stable | Future minor RFC (convenience helper) |
| No public drain driver API beyond `drain` | `drain` exists but runs all tasks to completion | Cannot partial-drain (e.g. yield after N tasks) | Use `drain` for simple loops; use `step .schedule` loop for more control | TBD |
| `spawnChild` / supervision tree | Implemented in v0.6.0 | iotakt may use `spawnChild` for connection-scoped sub-tasks | Not needed in v0.1 | v0.6.0 complete; further supervision RFCs planned |
| Stable public import facade | Module structure stable but no single `Henret.Public` facade | iotakt import paths may need update on major version | Use `import Henret.Model` as minimum; pin Henret version exactly | Low priority; may be added in RFC 036+ |
| Mailbox GC / actor cleanup | No GC; mailboxes persist forever | Orphan messages after task cancel/complete accumulate | iotakt tracks live actors externally; cleans up by convention | TBD |
| `ActorId` allocation API | `ActorId = Nat`; iotakt chooses any `Nat` | Risk of collision if iotakt and Henret both allocate | Use `s.nextId` as a floor for iotakt ActorIds, or allocate from a disjoint range | TBD — may become an API requirement |
| Wall-clock to logical-time mapping | Undefined in Henret | iotakt must define its own policy | Milliseconds since epoch, cast to Nat | OUT OF SCOPE for Henret |

---

## 16. Change-Control and Compatibility Policy

### What triggers a Henret version bump

| Change type | Policy |
|---|---|
| `RuntimeOp` constructor added or removed | Minor version bump + CHANGELOG entry |
| `RuntimeState` field added | Minor version bump; iotakt must update struct usage |
| `Message` type changed | Minor version bump + migration note in CHANGELOG |
| Public theorem renamed | Minor version bump + old name alias for one version |
| Proof status downgraded (PROVEN → ASSUMED) | Minor version bump + explicit matrix update |
| `WellFormed` fields added | Minor version bump; `reachable_wf` still holds |
| Native boundary changes | Must not silently affect Lean-only semantics; if they do, major version bump |
| Internal module path renamed | No iotakt obligation (internal modules are excluded from iotakt's import set) |

### How changes are announced

1. CHANGELOG.md is updated with the version heading and change description before the archive is released.
2. Proof-trust-test-matrix entries are updated to reflect new or changed claims.
3. RFC documents in `rfcs/done/` are the authoritative design record.

### iotakt pinning recommendation

Pin Henret to an exact version in `lakefile.lean`:

```lean
require henret from git "https://github.com/nabbisen/henret" @ "v0.6.0"
```

Do not use branch-tracking dependencies (`@ "main"`) until iotakt has its own integration test suite that gates on Henret compatibility.

### Questions that require Henret review before iotakt proceeds

1. Confirm `ActorId` allocation strategy — will Henret provide a counter API?
2. Confirm RFC 033 (message envelope) timeline — iotakt's codec layer depends on it.
3. Confirm whether `Henret.Scheduler.Driver.drain` is the intended driver API or whether a separate `driveBounded` with a step limit is needed.

---

*Henret v0.6.0 — prepared for iotakt design phase — 2026-06-08*
