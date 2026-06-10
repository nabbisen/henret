# Execution Trace Ledger (RFC 045)

Henret makes execution traces first-class. Alongside the ordinary
`(state, result)` effect of an operation, the trace layer emits a list of
semantic `TraceEvent`s — which task was scheduled, which envelope was
delivered, which task parked, which timer fired, which child was spawned
by which parent.

The ledger is the substrate for golden-trace conformance (RFC 047) and
trace visualization (RFC 050). It does **not** change core `step`
semantics.

## Module layout

```text
Henret/Trace/
  Event.lean      -- the TraceEvent vocabulary
  Run.lean        -- traceEvents, stepTrace, runTraceLedger + agreement theorems
  Theorems.lean   -- event soundness
Henret/Trace.lean -- aggregator
```

## The event vocabulary

`TraceEvent` has one constructor per meaningful runtime observation:
`invalid`, `spawned`, `spawnChild`, `scheduled`, `yielded`, `completed`,
`cancelled`, `slept`, `timerWoke`, `directWoke`, `sent`, `injected`,
`received`, `parked`, `waiterWoke`, and `noEffect`. Each records a
*semantic* observation, not a low-level proof artifact.

## Agreement by construction

`stepTrace` is defined to reuse `step` for its state and result, adding
only a separate `traceEvents` computation:

```text
stepTrace s op = (step s op).1, (step s op).2, traceEvents s op
```

As a result the agreement theorems are definitional:

| Theorem | Statement |
|---|---|
| `stepTrace_state_eq_step` | `(stepTrace s op).1 = (step s op).1` (by `rfl`) |
| `stepTrace_result_eq_step` | `(stepTrace s op).2.1 = (step s op).2` (by `rfl`) |
| `runTraceLedger_state_eq_run` | `(runTraceLedger s ops).1 = run s ops` (by induction) |
| `runTraceLedger_results_eq_runTrace` | `(runTraceLedger s ops).2.1 = (runTrace s ops).2` |

This is the key design choice: by never letting `stepTrace` recompute the
state, there is no risk of the ledger drifting from the semantics.

## Event soundness

Each headline event, when present in `stepTrace`'s ledger, certifies the
corresponding semantic fact. Because `traceEvents` mirrors `step`'s guard
structure exactly, each soundness proof is a guard-case analysis.

| Theorem | Guarantee |
|---|---|
| `event_received_sound` | a `received t a occ` event ⇒ `t` running, owns `a`, `a`'s mailbox head dequeued with occurrence `occ` |
| `event_parked_sound` | a `parked t a` event ⇒ `t` is now `.waiting` and in `a`'s waiter list |
| `event_directWoke_sound` | a `directWoke t` event ⇒ `t` was `.sleeping` |
| `event_timerWoke_sound` | a `timerWoke now t` event ⇒ `now` not in the past and `t`'s timer expired by `now` |
| `event_spawnChild_sound` | a `spawnChild parent child a` event ⇒ `parent` running, `child = nextId` fresh |
| `event_scheduled_sound` | a `scheduled t` event ⇒ nothing running, `t` was `readyQ` head and runnable |
| `event_waiterWoke_send_sound` | a `waiterWoke a w` event from `send` ⇒ `w` is the head of `a`'s regular or timed waiter list |

## Usage

See `examples/11_trace_ledger.lean` for a runnable scenario that prints a
readable trace and discharges the agreement and soundness theorems.

```lean
open Henret Henret.Trace
#eval (runTraceLedger RuntimeState.init
  [.spawn 7, .schedule, .inject 7 ⟨0, 100⟩, .receive 0, .receive 0]).2.2
-- [spawned 0 7, scheduled 0, injected 7 0, received 0 7 0, parked 0 7]
```

## Scope

The ledger is a model-level observation layer. It does not add
concurrency, prove fairness, or log to a concrete runtime. Trace events
are not yet frozen as stable public API (that is deferred to RFC 052);
the names may be refined as conformance (RFC 047) and visualization
(RFC 050) consume them.
