import Henret.Bridge.Grammar
import Henret.Bridge.State
import Henret.Bridge.Preservation
/-!
# Henret.Bridge  (RFC 035 skeleton → RFC 036 complete single-worker bridge)

Formal connection between the Henret actor/task semantic model and the
lean-runtime work-stealing queue model.

This is a **queue projection bridge**: it relates Henret's `readyQ` to
worker 0's queue in a `WorkerQueues` map.  It does not claim fairness,
native execution correctness, or actor-semantics equivalence.

## Exports

- `Henret.Bridge.QOp` — bridge queue-operation grammar (Push, Pop, Filter;
  Steal/Wake/Inject mirrored from lean-runtime but not emitted by single-worker bridge).
- `Henret.Bridge.toQOps` — guard-compatible translation from `RuntimeOp` to `List QOp`.
- `Henret.Bridge.toQOpsTrace` — state-threading trace translation.
- `Henret.Bridge.BridgeState` — queue projection relation.
- `Henret.Bridge.bridge_step_single_worker` — single-step bridge for all 12 `RuntimeOp`s.
- `Henret.Bridge.bridge_run_tracks_single_worker` — headline trace theorem.
- `Henret.Bridge.bridge_run_general` — trace theorem from any starting `BridgeState`.
- `Henret.Bridge.reachable_bridge` — backward-compatible existential form.

See `docs/bridge-architecture.md` for the full design and scope description.
-/
