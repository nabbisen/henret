import Henret
/-!
# Example 14 — State Diagrams (RFC 050)

Render a runtime state as a per-task location map, a Mermaid parent tree,
and the single-worker bridge projection.  Paste the Mermaid output into
any Markdown preview that supports it.

Run with:  `lake env lean examples/14_state_diagrams.lean`
-/
open Henret Henret.Render

/-- A supervision tree: task 0 spawns two children; one fails and is restarted. -/
def tree : List RuntimeOp :=
  [ .spawn 7, .schedule,
    .spawnChild 0 7,     -- task 1
    .spawnChild 0 8,     -- task 2 (different actor)
    .yield 0, .schedule, -- run task 1
    .fail 1,             -- task 1 fails
    .schedule,           -- run task 0
    .restartOne 0 1 7 ]  -- restart task 1 as fresh task 3

def st := run RuntimeState.init tree

-- Per-task location map (explains the `WellFormed` location invariants).
#eval IO.println (locationMap st)

-- The actor/mailbox view.
#eval IO.println (mailboxView st)

-- Mermaid parent tree (restart provenance annotated).
#eval IO.println (parentTreeMermaid st)

-- Mermaid mailbox diagram.
#eval IO.println (mailboxMermaid st)

-- The single-worker bridge projection.
#eval IO.println (bridgeWorkerQueues st)
