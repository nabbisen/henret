import Henret
/-!
# Example 13 — Trace Rendering (RFC 050)

Render a runtime scenario as a readable transition trace and state
summary.  These are pure `String` functions outside the proof kernel —
visualization as a formal-methods adoption tool.

Run with:  `lake env lean examples/13_trace_rendering.lean`
-/
open Henret Henret.Trace Henret.Render

/-- A scenario that exercises parking, waking, and a timer. -/
def scenario : List RuntimeOp :=
  [ .spawn 7,            -- task 0 (actor 7)
    .schedule,           -- run task 0
    .spawnChild 0 7,     -- task 0 spawns child task 1 (same actor)
    .receive 0,          -- task 0 receives → empty mailbox → parks
    .schedule,           -- run task 1
    .send 1 7 ⟨0, 100⟩,  -- task 1 sends to actor 7 → wakes parked task 0
    .sleep 1 5,          -- task 1 sleeps until 5
    .tick 10 ]           -- advance to 10 → wakes task 1

-- The readable trace table.
#eval IO.println (traceTable (runTraceLedger RuntimeState.init scenario).2.2)

-- The state summary after the scenario.
#eval IO.println (run RuntimeState.init scenario).render

-- A single event renders on its own too.
#eval IO.println (TraceEvent.parked 0 7).render
