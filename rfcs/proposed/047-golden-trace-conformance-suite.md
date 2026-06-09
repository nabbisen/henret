# RFC 047 — Golden Trace Conformance Suite

## Status

Proposed.

## Summary

Create a golden trace suite that external runtimes can use to compare their
observable behavior against Henret. The suite uses RFC 045 trace events as the
canonical expected behavior and defines adapter responsibilities for concrete
runtimes.

## Motivation

Henret is a semantic reference. To be useful beyond proofs, it should export
small, stable conformance scenarios:

- spawn and schedule;
- yield and requeue;
- park on empty mailbox;
- send/inject wakes one waiter;
- Mesa re-receive consumes later;
- sleep and timer tick;
- cancel removes ready/waiting/sleeping presence;
- spawnChild records parent;
- occurrence ids are fresh and unique.

A runtime should be able to say: "we implement these Henret traces," or "we
intentionally differ here."

## Non-goals

This RFC does not:

- prove concrete runtime correctness;
- require a specific serialization format forever;
- replace the bridge theorems;
- require external runtimes to expose internal queues.

## Proposed design

### Scenario format

Define a Lean-native scenario structure first:

```lean
structure GoldenScenario where
  name        : String
  initial     : RuntimeState := RuntimeState.init
  ops         : List RuntimeOp
  expect      : List TraceEvent → Bool
  description : String
```

Later, export to JSON if needed.

### Golden scenario module

```text
Henret/Conformance/
  Scenario.lean
  Golden.lean
  Export.lean
```

### Required scenarios

1. `spawn_schedule_complete`
2. `yield_requeues`
3. `sleep_tick_wakes`
4. `empty_receive_parks`
5. `send_wakes_waiter_mesa`
6. `inject_wakes_waiter_mesa`
7. `cancel_ready_task`
8. `cancel_waiting_task`
9. `spawn_child_parent_lt`
10. `occurrence_unique_two_mailboxes`

### Adapter contract

External runtimes should provide:

```text
input:  GoldenScenario ops
output: observed event trace
check:  observed trace refines or equals Henret trace
```

The first version can use equality for simple scenarios and refinement for cases
where ordering may legitimately differ.

### Refinement relation

Define:

```lean
def TraceRefines (expected observed : List TraceEvent) : Prop := ...
```

Start with equality. Add relaxed variants only when a real integration needs it.

## Implementation tasks

1. Implement RFC 045.
2. Add `Henret.Conformance.Scenario`.
3. Add ten golden scenarios.
4. Add executable checker returning pass/fail with scenario name.
5. Add optional pretty-printer for expected events.
6. Add docs: `docs/conformance-suite.md`.
7. Add an adapter note for `lean-runtime-workspace`.
8. Add CI target for golden scenario evaluation.

## Acceptance criteria

- Golden scenarios run under `lake exe` or `#eval`.
- Each scenario has a human-readable purpose.
- Failures identify the first mismatching event.
- The suite is separate from examples; examples teach, conformance tests gate.

## Risks

Trace equality may be too strict for multi-worker runtimes. Use exact equality
for single-worker conformance and postpone relaxed matching until RFC 043-style
multi-worker bridge semantics are stable.
