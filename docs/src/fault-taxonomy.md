# Fault & outcome taxonomy (RFC 064)

Henret distinguishes several notions that English collapses into "failure". A
formal reference must keep them apart. This document is the canonical vocabulary;
the `StepResult`-representable slice is machine-checked by
`Henret/Diagnostics/Taxonomy.lean` (`faultClass`).

**Rule of thumb.** Only **protocol invalidity** is a *fault* reportable by a pure
`StepResult`. Ordinary waiting, timeout, cancellation, and normal progress are
not faults. Task fault, adapter failure, and trusted-backend failure live
outside the pure result type.

## The eight classes

### 1. Protocol invalidity — *fault*

A requested operation violates Henret's semantic preconditions (non-running task
sends, unowned task receives, a cancelled task completes, …).

Representation: `StepResult.invalid`. Required property: the state is unchanged
(`step_invalid_unchanged`). Class: `FaultClass.protocolInvalid`.

### 2. Ordinary waiting — *not a fault*

A legal operation cannot proceed *now* because a resource is unavailable: an
empty mailbox parks the receiver; a full bounded mailbox rejects the delivery.

Representation: `StepResult.blocked` (park) and `StepResult.backpressured`
(capacity reject); states `TaskState.waiting` / `TaskState.waitingTimed`;
`mailboxWaiters`. Class: `FaultClass.waiting`. Distinguished from class 1 by
`blocked_not_invalid_class` and `backpressured_not_invalid_class`.

### 3. Cancellation — *not a fault*

A task is intentionally prevented from continuing (direct `cancel`, cascade
`cancelTree`, shutdown). Representation: `TaskState.cancelled` (terminal,
`isTerminal_cancelled`). A cancelled task is not schedulable; only an explicit
restart policy may create a new task identity. This is a **state** class, not a
`StepResult` outcome (the `cancel` op itself returns `.ok`).

### 4. Timeout — *not a fault*

A waiting condition expires by time rather than by delivery. Representation:
`StepResult.timedOut`; the woken task becomes `TaskState.ready`. Class:
`FaultClass.timeout`. Exact state changes are owned by RFC 040 (`receiveUntil`).

### 5. Task fault — *state present, payload reserved*

A task computation fails according to modeled task semantics. Representation
today: `TaskState.failed` (terminal, `isTerminal_failed`), produced by `fail` /
consumed by `restartOne` (RFC 049). A richer `FaultKind` payload and a
`StepResult.failed` outcome are **reserved**, deferred until task computation is
modeled more richly (RFC 064 non-goal: no failure payloads yet).

### 6. Supervisor fault signal — *reserved*

A fault observed by a parent/supervisor (`SupervisorEvent.childFailed …`). Belongs
with restart policies, **not** the base model. Reserved.

### 7. Runtime adapter failure — *out of model*

A concrete runtime violates the Henret contract (schedules a cancelled task,
duplicates an occurrence id, reads the wrong mailbox). Represented as a
**conformance test failure**, never as reachable Henret state — Henret models the
intended semantics, not broken implementations.

### 8. Trusted backend failure — *out of pure Lean scope*

The C/FFI implementation violates its stated assumptions. Recorded in the
assumption index and exercised by the differential/linearizability suites; it is
a trust-boundary concern, not a Lean theorem.

## `StepResult` → class (machine-checked)

This table mirrors `faultClass` in `Henret/Diagnostics/Taxonomy.lean` and is
kept in sync by `scripts/fault_taxonomy_check.py`.

| StepResult | FaultClass | Fault? |
|---|---|---|
| `ok` | `progress` | no |
| `spawned` | `progress` | no |
| `scheduled` | `progress` | no |
| `received` | `progress` | no |
| `woke` | `progress` | no |
| `acquired` | `progress` | no |
| `blocked` | `waiting` | no |
| `backpressured` | `waiting` | no |
| `timedOut` | `timeout` | no |
| `invalid` | `protocolInvalid` | yes |

## `TaskState` → class

| TaskState | Class | Notes |
|---|---|---|
| `new`, `ready`, `running`, `yielded` | progress | runnable / live |
| `sleeping`, `waiting`, `waitingTimed` | ordinary waiting (2) | parked / timed |
| `cancelled` | cancellation (3) | terminal |
| `failed` | task fault (5) | terminal; payload reserved |
| `completed` | progress | terminal-success |

## Terminology gate

`scripts/fault_taxonomy_check.py` verifies that (a) all eight classes appear in
this document, (b) the `StepResult`→class table here matches the Lean
`faultClass` definition exactly, and (c) live docstrings do not use bare
"failure"/"fault" for class 1–4 outcomes (which have precise terms). Use the
precise class name; reserve "fault" for classes 1 and 5, "failure" for classes
5, 7, and 8.
