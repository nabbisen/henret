# Observability and Pedagogical Visualization (RFC 050)

Henret ships human-readable renderers for states, traces, and actor/task
relations. A new reader should be able to *see* a parking receive, a
timer wake, or a supervision restart without reading proof lines.

These are pure `String` functions in `Henret/Render/`, outside the
proof-critical path. They add **no theorems** and do not affect the axiom
budget. No external graph library is needed — Mermaid output is plain
text you paste into any Markdown preview.

## Trace rendering

`TraceEvent.render` renders one event; `Henret.Render.traceTable` renders
a numbered transition table. For the supervision scenario (spawn →
spawnChild → child fails → restart):

```text
step | event
-----+------------------------------------------------
   0 | spawned          task 0 (actor 7)
   1 | scheduled        task 0
   2 | spawnChild       task 0 → child 1 (actor 7)
   3 | yielded          task 0
   4 | scheduled        task 1
   5 | failed           task 1
   6 | scheduled        task 0
   7 | restarted        task 1 → fresh 2 by 0 (actor 7)
```

## State summary and location map

`RuntimeState.render` gives a one-screen summary; `locationMap` shows
where each task lives. This is the most direct way to *explain* the
`WellFormed` location invariants — every task is in exactly one place:

```text
RuntimeState  now=0  nextId=3  nextMsgId=0
  running=0  readyQ=[2]
Tasks:
  task 0: running, running, owner actor 7
  task 1: failed, failed, owner actor 7
  task 2: new, readyQ[0], owner actor 7
Mailboxes:
  actor 7: msgs=[(empty)]
```

The replacement task 2 sits in `readyQ[0]`, the failed task 1 is
off-queue in `failed`, and the supervisor task 0 is `running` — exactly
the invariants `runnable_queued`, terminal-state monotonicity, and
`running_runs` describe.

## Mermaid diagrams

`parentTreeMermaid` renders the parent relation, annotating restart
provenance:

```text
graph TD
  T0["task 0"]
  T1["task 1"]
  T2["task 2 (restart of 1)"]
  T0 --> T1
  T0 --> T2
```

`mailboxMermaid` renders actors with mailbox depth and waiter counts.

## Bridge projection

`bridgeWorkerQueues` shows the single-worker projection that
`BridgeState` relates `readyQ` to (worker 0 = `readyQ`, others empty),
the executable companion to `bridge_run_tracks_single_worker`.

## Examples

- `examples/13_trace_rendering.lean` — a parking/wake/timer scenario as a
  trace table and state summary.
- `examples/14_state_diagrams.lean` — a supervision tree as a location
  map, Mermaid parent tree, mailbox diagram, and bridge projection.

## Scope

Renderers are deliberately simple and generated directly from the current
data structures, so they stay correct as the model evolves without
becoming a maintenance burden. They are not a GUI and never enter the
proof kernel.
