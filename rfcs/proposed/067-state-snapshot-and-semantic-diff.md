---
rfc: 67
title: State Snapshot and Semantic Diff
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [66]
blocks: []
category: observability
---

# RFC 067 — State Snapshot and Semantic Diff

## Status

Proposed strategic RFC.

## Summary

Define state snapshots and semantic diffs for Henret runtime states. The goal is to make model evolution, replay debugging, examples, and adapter conformance easier to inspect.

## Motivation

As `RuntimeState` grows, raw state equality becomes difficult to inspect. A semantic diff tells users what changed in terms that matter:

- task lifecycle changed;
- ready queue changed;
- mailbox received envelope;
- waiter queue changed;
- timer expired;
- parent relation changed;
- occurrence counter advanced.

This is valuable for demos, test failures, documentation, and external runtime adapter debugging.

## Goals

- Define a stable snapshot view of `RuntimeState`.
- Define a semantic diff type.
- Provide examples and optional executable printer.
- Use diffs in replay failure reports.

## Non-goals

- Do not expose every internal field as public API.
- Do not replace proofs with diff tests.
- Do not promise binary-stable serialization yet.

## Proposed snapshot

```lean
structure StateSnapshot where
  now : Nat
  nextId : Nat
  nextMsgId : Nat
  running : Option TaskId
  readyQ : List TaskId
  taskStates : List (TaskId × TaskState)
  owners : List (TaskId × ActorId)
  parents : List (TaskId × TaskId)
  mailboxes : List (ActorId × List Envelope)
  waiters : List (ActorId × List TaskId)
  timers : List TimerEntry
```

Because current maps are function-like, snapshots need a finite domain. Use `nextId` and known mailbox domains to enumerate meaningful values.

## Proposed diff events

```lean
inductive StateDiff where
  | taskStateChanged : TaskId → Option TaskState → Option TaskState → StateDiff
  | runningChanged : Option TaskId → Option TaskId → StateDiff
  | readyQChanged : List TaskId → List TaskId → StateDiff
  | mailboxChanged : ActorId → List Envelope → List Envelope → StateDiff
  | waitersChanged : ActorId → List TaskId → List TaskId → StateDiff
  | timerChanged : List TimerEntry → List TimerEntry → StateDiff
  | parentChanged : TaskId → Option TaskId → Option TaskId → StateDiff
  | ownerChanged : TaskId → Option ActorId → Option ActorId → StateDiff
  | counterChanged : String → Nat → Nat → StateDiff
```

## Diff policy

A semantic diff should be stable and concise. It should avoid listing unchanged actors or tasks. It should sort output deterministically.

## Design note

This RFC is mostly engineering/product polish, but it also improves formal review. When a theorem says an operation touches only certain fields, a diff can illustrate that claim in examples.

## Concerns

- Function-valued fields require finite enumeration.
- Snapshot code can become stale when `RuntimeState` changes; use doc-generation or tests to catch drift.
- Diffs are diagnostic, not proof obligations.

## Implementation tasks

1. Add `Henret/Debug/Snapshot.lean`.
2. Add `Henret/Debug/Diff.lean`.
3. Add a finite-state snapshot helper for reachable states using `nextId`.
4. Add pretty-printing helpers.
5. Update demo to optionally print diffs.
6. Use diffs in replay-conformance failure output.
7. Add documentation examples.

## Acceptance criteria

- A small execution can be shown as operation → result → diff.
- Parking receive diff shows `running`, `taskState`, and `mailboxWaiters` changes.
- Message inject with waiter diff shows wake-one queue changes.
- No proof/trust/test claims are based solely on debug diff output.
