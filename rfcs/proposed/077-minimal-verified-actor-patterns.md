---
rfc: 77
title: Minimal Verified Actor Patterns
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: pedagogy
---

# RFC 077 — Minimal Verified Actor Patterns

## Status

Proposed strategic RFC.

## Summary

Add small verified actor/task patterns on top of Henret's core semantics. These patterns are not runtime features; they are pedagogical and reusable semantic examples showing how to reason with the model.

## Motivation

Henret will shine more if users can see familiar actor patterns expressed and verified. This makes the library useful not only for kernel proofs but also for learning and design review.

## Goals

- Provide small actor-pattern examples.
- Prove one or two meaningful safety properties per pattern.
- Keep patterns independent of external runtime implementation.
- Avoid overcomplicating the core model.

## Non-goals

- Do not implement a production actor framework.
- Do not introduce general task computation language unless needed.
- Do not claim liveness without a scheduling policy.

## Candidate patterns

### 1. Request/reply envelope pattern

A requester sends a message with a reply actor id.

Safety property:

- reply is received only by the requester actor's mailbox.
- occurrence ids remain unique.

### 2. One-shot worker

A worker receives one message and completes.

Safety property:

- completed worker is not queued or waiting.

### 3. Supervised child skeleton

A parent spawns a child and later cancels it.

Safety property:

- parent relation is acyclic.
- child owner/parent fields are coherent.

### 4. Timeout receive pattern

A task waits for message or deadline.

Safety property:

- timeout and receive do not both consume the same wait registration.

Only implement after RFC 040.

### 5. Bounded worker pool pattern

A fixed number of worker actors process messages.

Safety property:

- no task outside the pool consumes pool mailbox messages.

Only implement after bounded or selective receive semantics if needed.

## Module layout

```text
Henret/Patterns/
  RequestReply.lean
  OneShotWorker.lean
  SupervisedChild.lean
  TimeoutReceive.lean
```

## Design note

Patterns should be examples with proofs, not abstractions that alter core semantics. They should import public-stable theorem API wherever possible.

## Concerns

- Patterns can accidentally become a second API surface.
- Too much pattern machinery may hide the clarity of the core model.
- Some patterns need features not yet implemented; mark them pending.

## Implementation tasks

1. Add `Henret/Patterns/` namespace.
2. Implement at least two small patterns first: request/reply and one-shot worker.
3. Add scenario traces for each pattern.
4. Prove at least one safety theorem per implemented pattern.
5. Add `examples/09_patterns.lean`.
6. Add docs explaining that patterns are semantic examples, not runtime APIs.

## Acceptance criteria

- At least two verified patterns exist.
- Patterns use stable public theorem API where practical.
- Pattern docs clearly separate model reasoning from runtime implementation.
