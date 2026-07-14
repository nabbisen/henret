---
rfc: 73
title: Runtime Adapter Negative Tests
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [60, 61]
blocks: []
category: integration
---

# RFC 073 — Runtime Adapter Negative Tests

## Status

Proposed strategic RFC.

## Summary

Define a negative conformance suite for external runtime adapters. Positive tests show that valid scenarios work; negative tests prove that invalid, unsafe, or semantically forbidden scenarios are rejected or produce the correct no-op behavior.

## Motivation

A runtime can pass happy-path tests while still violating Henret's security and execution-management semantics. Examples:

- unowned receive succeeds;
- non-running send delivers a message;
- cancelled task runs;
- duplicate occurrence id is accepted;
- stale timer wakes a non-sleeping task;
- actor receives from another actor's mailbox.

Negative tests are essential for a semantic reference model.

## Goals

- Define negative conformance cases for adapters.
- Make each case traceable to a Henret theorem or invariant.
- Distinguish model-level negative tests from native/FFI stress tests.
- Integrate with replay format and bridge certificates.

## Non-goals

- Do not test performance.
- Do not test OS-specific scheduling fairness.
- Do not treat C data-race freedom as proven by negative tests.

## Test categories

### Protocol invalidity

- non-running task attempts `send`;
- unowned task attempts `receive`;
- invalid backward tick;
- task attempts operation after cancellation.

Expected result:

```text
.invalid and unchanged state
```

### Blocking vs invalidity

- running owned task receives from empty own mailbox.

Expected result:

```text
.blocked and parked according to current semantics
```

### Actor locality

- task owned by actor A attempts receive; implementation must not receive from actor B.

Expected result:

```text
only actor A mailbox can be touched
```

### Occurrence identity

- adapter reports two envelopes with same occurrence id in different mailboxes.

Expected result:

```text
conformance failure
```

### Timer hardening

- stale timer for cancelled/non-sleeping task.

Expected result:

```text
no wake; no ready queue insertion
```

### Queue safety

- cancelled task still appears in ready queue.

Expected result:

```text
conformance failure
```

## Test format

Negative tests should be replay-compatible:

```toml
name = "non-running-send-invalid"
expectFailure = false

[[steps]]
op = { spawn = { actor = 1 } }
expect = { result = { spawned = 0 } }

[[steps]]
op = { send = { task = 0, to = 1, body = 10 } }
expect = { result = "invalid" }
expectState = "unchanged"
```

## Design note

Negative tests should be framed as semantic obligations, not adversarial fuzzing. Fuzzing belongs to a separate stress/conformance layer.

## Concerns

- Some negative tests require constructing arbitrary states, not just reachable traces.
- Runtime adapters may not expose full internal state, so some checks may require adapter-specific observation hooks.
- Test names must remain stable if used by external projects.

## Implementation tasks

1. Create `conformance/negative/`.
2. Add negative replay cases for each category.
3. Add a mapping from each negative test to theorem/invariant support.
4. Add adapter-contract section: required negative tests.
5. Add CI gate that all Henret model negative tests pass.
6. Add documentation explaining why negative tests are required.

## Acceptance criteria

- At least ten negative tests exist.
- Each test names the supported theorem or invariant.
- Invalid operations are tested separately from blocked legal operations.
- Negative tests are included in public conformance documentation.
