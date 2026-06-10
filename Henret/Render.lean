import Henret.Render.Trace
import Henret.Render.State
import Henret.Render.Diagram
/-!
# Henret.Render  (RFC 050)

Human-readable renderers for states, traces, and actor/task relations.
Pure `String` functions — no proofs, no axioms, outside the
proof-critical path.  Visualization is a formal-methods adoption tool: a
new reader should be able to *see* a parking receive or a timer wake
without reading proof lines.

## Exports

- `RuntimeState.render` — full one-screen state summary.
- `Henret.Render.locationMap` / `taskLocation` — per-task location map
  (explains the `WellFormed` location invariants).
- `Henret.Render.mailboxView` — actor/mailbox contents and waiters.
- `TraceEvent.render` / `Henret.Render.traceTable` — event and trace
  rendering.
- `Henret.Render.parentTreeMermaid` / `mailboxMermaid` — Mermaid diagrams
  (paste into any Markdown preview).
- `Henret.Render.bridgeWorkerQueues` — single-worker bridge projection.

See `docs/observability.md` for rendered examples.
-/
