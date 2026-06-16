---
rfc: 64
title: Fault Model and Failure Taxonomy
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: theory
---

# RFC 064 — Fault Model and Failure Taxonomy

## Status

Proposed strategic RFC.

## Summary

Define Henret's vocabulary for failure, invalidity, blocking, cancellation, timeout, runtime-adapter fault, and externally trusted failure. The goal is to prevent semantic ambiguity as Henret grows from a safety-invariant model into a richer actor/task execution reference.

## Motivation

Henret already distinguishes `.invalid`, `.blocked`, `.cancelled`, timer expiration, and external bridge/runtime assumptions. As supervision, bounded mailboxes, receive timeouts, and adapter contracts are added, the project needs a stable taxonomy.

Without a taxonomy, later RFCs may accidentally conflate:

- a protocol error;
- ordinary waiting;
- cancellation requested by a supervisor;
- task failure;
- timeout;
- runtime implementation bug;
- trusted C/FFI assumption failure.

A formal project should not use one word, such as "failure", to mean all of these.

## Goals

- Define a public taxonomy of execution outcomes and fault classes.
- Decide which classes are represented in `StepResult`, which are state fields, and which are documentation/test-only categories.
- Clarify which classes are model-internal and which belong to external runtime adapters.
- Prepare terminology for supervision and restart policies.

## Non-goals

- Do not implement restart policies in this RFC.
- Do not introduce exceptions or arbitrary task failure payloads yet.
- Do not model OS or C runtime failures inside the pure Henret state machine.
- Do not change existing proven semantics unless a terminology mismatch is discovered.

## Proposed taxonomy

### 1. Protocol invalidity

A requested operation violates Henret's semantic preconditions.

Examples:

- non-running task attempts `send`;
- unowned task attempts `receive`;
- backward tick if monotonic time is required;
- cancelled task attempts to complete.

Representation:

```lean
StepResult.invalid
```

Required property:

```lean
theorem step_invalid_unchanged ...
```

### 2. Ordinary waiting

A legal operation cannot currently proceed because the requested resource is unavailable.

Examples:

- actor-local `receive` on empty mailbox;
- future bounded mailbox `send` to full mailbox;
- future timeout-wait registration.

Representation:

```lean
StepResult.blocked
TaskState.waiting
mailboxWaiters
```

Required property:

Blocked waiting is not a fault. It is a normal transition.

### 3. Cancellation

A task is intentionally prevented from continuing.

Examples:

- direct cancel;
- future cascade cancel;
- shutdown cancel.

Representation:

```lean
TaskState.cancelled
```

Required property:

Cancelled tasks are terminal or semiterminal according to the chosen profile. They must not be schedulable unless an explicit restart policy creates a new task identity.

### 4. Timeout

A waiting condition expires by time rather than message delivery.

Representation options:

```lean
StepResult.timedOut
TaskState.ready
TimeoutEvent
```

This RFC only reserves the taxonomy. RFC 040 or a successor should define exact state changes.

### 5. Task fault

A task computation fails according to modeled task semantics.

Representation options:

```lean
TaskState.failed FaultKind
StepResult.failed FaultKind
```

This should be deferred until Henret models task computations more richly.

### 6. Supervisor fault signal

A fault observed by a parent/supervisor.

Representation options:

```lean
SupervisorEvent.childFailed parent child reason
```

This belongs with restart policies, not the base model.

### 7. Runtime adapter failure

A concrete runtime violates the Henret semantic contract.

Examples:

- adapter schedules a cancelled task;
- duplicate occurrence id appears;
- external runtime consumes the wrong mailbox.

Representation:

Conformance test failure, not Henret `StepResult`.

### 8. Trusted backend failure

The C/FFI implementation violates its stated assumptions.

Representation:

Out of pure Lean scope; recorded in the assumption index and conformance suite.

## Design note

The taxonomy should avoid turning Henret into a failure-heavy runtime API. Henret is a semantic reference. It only needs enough fault vocabulary to make formal claims unambiguous.

## Concerns

- Adding too many `StepResult` variants too early can destabilize examples and proof scripts.
- Some categories, especially task fault and supervision fault, are better introduced only when task computation semantics become richer.
- External runtime failure should not be represented as reachable Henret state; otherwise the model starts modeling broken implementations instead of the intended semantics.

## Implementation tasks

1. Add `docs/fault-taxonomy.md`.
2. Update glossary and guided tour.
3. Add a table mapping `StepResult` and `TaskState` constructors to taxonomy entries.
4. Mark future categories as reserved, not implemented.
5. Add proof/trust/test matrix rows for each category.
6. Add negative examples that distinguish `.invalid` from `.blocked`.
7. Add release gate phrase checks for ambiguous uses such as "failure" where the taxonomy requires a more precise term.

## Acceptance criteria

- Live docs consistently distinguish invalidity, blocking, cancellation, timeout, task fault, adapter failure, and trusted backend failure.
- Existing theorem names and semantics remain unchanged unless explicitly migrated.
- The taxonomy appears in README or guided tour in a concise form.
- No new axioms are introduced.
