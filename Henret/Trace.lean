import Henret.Trace.Event
import Henret.Trace.Run
import Henret.Trace.Theorems
/-!
# Henret.Trace  (RFC 045)

First-class execution traces.  Each operation, in addition to its
`(state, result)` effect, emits a list of semantic `TraceEvent`s.

## Exports

- `Henret.Trace.TraceEvent` — the semantic event vocabulary.
- `Henret.Trace.stepTrace` — one step with its event ledger; agrees with
  `step` on state and result by construction.
- `Henret.Trace.runTraceLedger` — run a sequence, accumulating results and
  events.
- `Henret.Trace.stepTrace_state_eq_step`,
  `Henret.Trace.stepTrace_result_eq_step`,
  `Henret.Trace.runTraceLedger_state_eq_run` — agreement with `step`/`run`.
- Event soundness: `event_received_sound`, `event_parked_sound`,
  `event_directWoke_sound`, `event_timerWoke_sound`,
  `event_spawnChild_sound`, `event_scheduled_sound`,
  `event_waiterWoke_send_sound`.

The ledger is the substrate for RFC 047 (golden conformance traces) and
RFC 050 (trace visualization).  It does not change core `step` semantics.

See `docs/trace-ledger.md` for the full design.
-/
