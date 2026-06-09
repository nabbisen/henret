# RFC 050 — Observability and Pedagogical Visualization

## Status

Proposed.

## Summary

Add human-readable renderers for Henret states, traces, proof boundaries, and
actor/task relations. This RFC improves Henret's ecosystem character: formal
models are easier to trust and adopt when their behavior is inspectable.

## Motivation

Henret has become sophisticated. A new reader should not need to read thousands
of proof lines to understand a parking receive or a timer wake. Visualization is
not cosmetic; it is a formal-methods adoption tool.

Useful outputs:

- state table after each operation;
- actor mailbox diagram;
- ready/waiting/sleeping location map;
- parent tree;
- message occurrence ledger;
- bridge projection to worker queues;
- proof/trust/test matrix summary.

## Non-goals

This RFC does not:

- create a GUI;
- require external graph libraries;
- become part of the proof kernel;
- replace theorem statements.

## Proposed design

### Text renderers first

Add:

```lean
def RuntimeState.render : RuntimeState → String

def TraceEvent.render : TraceEvent → String

def renderTraceTable : List TraceEvent → String
```

### Mermaid output

Optionally add pure string output:

```lean
def renderParentTreeMermaid : RuntimeState → String

def renderMailboxMermaid : RuntimeState → String
```

No external dependency is needed. Users can paste the output into Markdown.

### Location map

Add a renderer that shows each task's location:

```text
Task 0: running, owner actor 7
Task 1: readyQ[0], owner actor 7
Task 2: waiting actor 8, mailboxWaiters[8][0]
Task 3: sleeping until 10
```

This is especially useful for explaining `WellFormed` fields.

### Example integration

Add:

```text
examples/09_trace_rendering.lean
examples/10_state_diagrams.lean
```

## Implementation tasks

1. Implement string renderers for ids, states, results, operations, events.
2. Implement state summary renderer.
3. Implement task location renderer.
4. Implement mailbox renderer.
5. Implement parent tree renderer.
6. Implement bridge worker-queue renderer.
7. Add examples.
8. Add screenshots or pasted output to docs.
9. Keep renderers outside proof-critical modules.

## Acceptance criteria

- A user can run one example and see a readable transition trace.
- Renderers cover ready/waiting/sleeping/running/completed/cancelled tasks.
- Mermaid output is valid enough for Markdown preview tools.
- Docs use rendered output to explain at least one non-trivial scenario.

## Risks

Renderers can create maintenance load if they are too elaborate. Keep them
simple and generated from current data structures.
