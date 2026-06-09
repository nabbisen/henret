import Henret.Bridge.Grammar
import Henret.Bridge.State
import Henret.Bridge.Preservation
/-!
# Henret.Bridge

Formal connection between the henret model and the lean-runtime work-stealing
scheduler (RFC 035).

Exports:
- `Henret.Bridge.QOp` — the queue-operation grammar mirrored from lean-runtime.
- `Henret.Bridge.toQOps` — translation from `RuntimeOp` to `List QOp`.
- `Henret.Bridge.BridgeState` — relation connecting `RuntimeState` to `WorkerQueues`.
- `Henret.Bridge.bridge_step` — headline: every henret step has a corresponding
  queue-effect that preserves `BridgeState`.
- `Henret.Bridge.reachable_bridge` — every reachable state can be bridged.
-/
