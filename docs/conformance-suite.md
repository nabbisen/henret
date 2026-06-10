# Golden Trace Conformance Suite (RFC 047)

Henret exports a small, stable set of conformance scenarios that external
runtimes can use to compare their observable behavior against the
reference model. Each scenario pairs an operation sequence with the
canonical `TraceEvent` trace Henret produces (see
`docs/trace-ledger.md`). A runtime can then state precisely: *"we
implement these Henret traces,"* or *"we intentionally differ here."*

## What it is (and is not)

The suite **gates observable behavior**, distinct from the examples
(which **teach**). It does not prove concrete-runtime correctness, does
not fix a serialization format forever, and does not replace the bridge
theorems. It is a behavioral reference, checked in and kernel-verified.

## The scenario structure

```lean
structure GoldenScenario where
  name        : String
  description : String
  ops         : List RuntimeOp
  expected    : List TraceEvent
  initial     : RuntimeState := RuntimeState.init
```

`observe sc` runs `runTraceLedger sc.initial sc.ops` and returns the event
trace. `checkScenario sc` is `observe sc == sc.expected`.

## The ten required scenarios

| # | Name | Purpose |
|---|---|---|
| 1 | `spawn_schedule_complete` | basic task lifecycle |
| 2 | `yield_requeues` | a yielded task returns to the ready queue |
| 3 | `sleep_tick_wakes` | a timer tick wakes a sleeper |
| 4 | `empty_receive_parks` | receive on an empty mailbox parks |
| 5 | `send_wakes_waiter_mesa` | send wakes exactly one waiter |
| 6 | `inject_wakes_waiter_mesa` | inject wakes exactly one waiter |
| 7 | `cancel_ready_task` | cancel removes a queued task |
| 8 | `cancel_waiting_task` | cancel removes a parked task |
| 9 | `spawn_child_parent_lt` | spawnChild records the parent |
| 10 | `occurrence_unique_two_mailboxes` | sends get distinct fresh occurrence ids |

## The refinement relation

```lean
def TraceRefines (expected observed : List TraceEvent) : Prop :=
  expected = observed
```

The first version is **exact equality**, which is correct for
single-worker conformance. Relaxed variants (permitting legitimate
reorderings on a multi-worker runtime, per the RFC 043 membership
bridge) can be added when a real integration needs them — not before.

## Running the suite

As an executable:

```bash
lake exe henret-conformance
```

prints a per-scenario PASS/FAIL report and exits non-zero on any failure.

Or interactively:

```lean
open Henret.Conformance
#eval allPass          -- true
#eval IO.println suiteReport
```

## The regression gate

```lean
theorem conformance_suite_passes : allPass = true := by decide
```

This is kernel-checked (`decide`, not `native_decide`, so no extra
axioms). Any change to `step` or `traceEvents` that alters the observable
behavior of any scenario breaks this proof — the golden traces cannot
silently drift from the semantics.

## Adapter contract for external runtimes

An adapter for a concrete runtime (e.g. `lean-runtime-workspace`) should:

```text
input:  a GoldenScenario's ops
output: the runtime's observed event trace, mapped into TraceEvent
check:  TraceRefines expected observed   (exact equality, v1)
```

The runtime is **not** required to expose internal queues — only the
observable event stream (spawned, scheduled, received, parked,
waiterWoke, timerWoke, etc.). Where a runtime intentionally differs
(e.g. a multi-worker scheduling order), it should document the divergence
rather than claim conformance.

## Scope and risks

Exact trace equality may be too strict for multi-worker runtimes, where
scheduling order legitimately varies. The suite therefore uses exact
equality for single-worker conformance and defers relaxed matching until
the multi-worker bridge semantics (RFC 043) are exercised by a real
adapter.
