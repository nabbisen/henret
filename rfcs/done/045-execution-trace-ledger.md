# RFC 045 — Execution Trace Ledger

## Status

Implemented (v0.13.0).

## Summary

Make execution traces first-class in Henret. The current model exposes `step`,
`run`, and selected scenario helpers. That is enough for final-state invariants,
but insufficient for conformance, replay, causality review, and conditional
liveness. This RFC introduces a structured `TraceEvent` ledger produced by each
operation and proves that trace replay agrees with the existing final-state
semantics.

## Motivation

Henret is becoming a semantic reference for external actor/task runtimes. A final
state theorem such as `reachable_wf` is necessary, but runtime implementers also
need to know *how* the state was reached:

- which task was scheduled;
- which actor's mailbox was touched;
- which message occurrence was delivered;
- which task parked;
- which waiter was woken;
- which timer expired;
- which child was spawned by which parent.

A first-class trace ledger lets Henret serve as a golden semantic source for
adapters and test harnesses. It also creates a substrate for RFC 046 fairness,
RFC 047 conformance, RFC 048 bounded exploration, and RFC 050 visualization.

## Non-goals

This RFC does not:

- change core step semantics;
- add concurrency;
- prove fairness;
- add logging to a concrete runtime;
- require trace events to be stable forever as public API before RFC 052.

## Proposed design

### New module layout

```text
Henret/Trace/
  Event.lean
  Run.lean
  Theorems.lean
```

### Trace event type

Introduce a compact event vocabulary:

```lean
inductive TraceEvent where
  | invalid        : RuntimeOp → TraceEvent
  | spawned        : task : TaskId → actor : ActorId → TraceEvent
  | spawnChild     : parent child : TaskId → actor : ActorId → TraceEvent
  | scheduled      : task : TaskId → TraceEvent
  | yielded        : task : TaskId → TraceEvent
  | completed      : task : TaskId → TraceEvent
  | cancelled      : task : TaskId → TraceEvent
  | slept          : task : TaskId → deadline : Nat → TraceEvent
  | timerWoke      : now : Nat → task : TaskId → TraceEvent
  | directWoke     : task : TaskId → TraceEvent
  | sent           : sender : TaskId → target : ActorId → occurrence : MessageId → TraceEvent
  | injected       : target : ActorId → occurrence : MessageId → TraceEvent
  | received       : task : TaskId → actor : ActorId → occurrence : MessageId → TraceEvent
  | parked         : task : TaskId → actor : ActorId → TraceEvent
  | waiterWoke     : actor : ActorId → task : TaskId → TraceEvent
  | noEffect       : RuntimeOp → StepResult → TraceEvent
```

Names can be refined during implementation, but each event should represent a
semantic observation, not a proof artifact.

### Step with trace

Add:

```lean
def stepTrace : RuntimeState → RuntimeOp → RuntimeState × StepResult × List TraceEvent
```

`stepTrace` must be definitionally or theorem-proven aligned with `step`:

```lean
theorem stepTrace_state_eq_step :
  (stepTrace s op).1 = (step s op).1

theorem stepTrace_result_eq_step :
  (stepTrace s op).2.1 = (step s op).2
```

Use whichever tuple shape is more ergonomic.

### Run with trace

Add:

```lean
def runTraceLedger : RuntimeState → List RuntimeOp → RuntimeState × List StepResult × List TraceEvent
```

Prove:

```lean
theorem runTraceLedger_state_eq_run :
  (runTraceLedger s ops).1 = run s ops
```

### Event soundness theorems

For each important event, prove a small soundness theorem. Examples:

```lean
theorem event_received_sound :
  e ∈ (stepTrace s (.receive t)).events →
  e = .received t a occ →
  ∃ mb env mb',
    s.taskOwner t = some a ∧
    s.mailboxes a = some mb ∧
    mb.dequeue = some (env, mb') ∧
    env.occurrence = occ
```

```lean
theorem event_parked_sound :
  .parked t a ∈ eventsOf (stepTrace s (.receive t)) →
  ((step s (.receive t)).1).taskState t = some .waiting ∧
  t ∈ ((step s (.receive t)).1).mailboxWaiters a
```

## Implementation tasks

1. Create `Henret.Trace.Event`.
2. Create `stepTrace` mirroring `step` branch-by-branch.
3. Create `runTraceLedger`.
4. Prove state/result equivalence with `step` and `run`.
5. Add event soundness theorem family.
6. Update examples to show traces for at least spawn/schedule/receive/park/tick.
7. Add docs: `docs/trace-ledger.md`.
8. Update proof/trust/test matrix.
9. Add a doc-symbol gate entry for all new headline theorems.

## Acceptance criteria

- `stepTrace` agrees with `step` on state and result.
- `runTraceLedger` agrees with `run` on final state.
- Trace events for receive, park, wake, timer, and spawnChild have soundness theorems.
- At least one example prints a readable trace.
- No existing public theorem is weakened.

## Risks

Trace events may become verbose and brittle. Keep them semantic, not low-level.
Avoid exposing every internal helper decision as an event.

## Future work

RFC 047 will use these events as the basis for golden conformance traces.
RFC 050 will render the same events into diagrams.
