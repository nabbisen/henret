import Henret
/-!
# Example 12 — Supervision Restart (RFC 049)

A supervisor (`parent`) spawns a child, the child *fails* (distinct from
an intentional cancel), and the supervisor *restarts* it: a fresh
replacement task is created with restart provenance, while parent
acyclicity and ownership invariants are preserved.

Run with:  `lake env lean examples/12_supervision_restart.lean`
-/
open Henret Henret.Trace

/-! ## The scenario

  task 0 (actor 7) is the supervisor; it spawns child task 1, which runs
  and fails; the supervisor then restarts it as fresh task 2. -/

def supervision : List RuntimeOp :=
  [ .spawn 7,            -- task 0 (supervisor) for actor 7
    .schedule,           -- run task 0
    .spawnChild 0 7,     -- task 0 spawns child task 1
    .yield 0,            -- task 0 yields so the child can run
    .schedule,           -- run task 1
    .fail 1,             -- task 1 fails (abnormal termination)
    .schedule,           -- run task 0 again
    .restartOne 0 1 7 ]  -- supervisor restarts failed child 1 as fresh task 2

-- The trace makes the lifecycle legible:
#eval (runTraceLedger RuntimeState.init supervision).2.2
-- [spawned 0 7, scheduled 0, spawnChild 0 1 7, yielded 0,
--  scheduled 1, failed 1, scheduled 0, restarted 0 1 2 7]

-- The failed task is `.failed` (not `.cancelled`):
#eval (run RuntimeState.init supervision).taskState 1   -- some failed
-- The replacement records its provenance:
#eval (run RuntimeState.init supervision).restartOf 2   -- some 1
-- and shares the supervisor as parent:
#eval (run RuntimeState.init supervision).taskParent 2  -- some 0

/-! ## The invariants hold (RFC 049) -/

-- PROVEN: the replacement's id strictly exceeds the failed task's (acyclic).
example {new old : TaskId}
    (h : (run RuntimeState.init supervision).restartOf new = some old) : old < new :=
  reachable_restart_fresh supervision h

-- PROVEN: the task a restart replaces is failed.
example {new old : TaskId}
    (h : (run RuntimeState.init supervision).restartOf new = some old) :
    (run RuntimeState.init supervision).taskState old = some .failed :=
  reachable_restart_old_failed supervision h

-- PROVEN: a restart replacement and the failed task share a supervisor.
example {new old : TaskId}
    (h : (run RuntimeState.init supervision).restartOf new = some old) :
    ∃ p, (run RuntimeState.init supervision).taskParent new = some p ∧
         (run RuntimeState.init supervision).taskParent old = some p :=
  reachable_restart_parent_consistent supervision h

-- PROVEN: a restarted task has an owner.
example {new old : TaskId}
    (h : (run RuntimeState.init supervision).restartOf new = some old) :
    ∃ a, (run RuntimeState.init supervision).taskOwner new = some a :=
  restarted_task_has_owner supervision h

-- PROVEN: parent acyclicity is preserved across restart.
example {t p : TaskId}
    (h : (run RuntimeState.init supervision).taskParent t = some p) : p < t :=
  restart_preserves_parent_acyclicity supervision h

#check @reachable_restart_fresh
#check @restarted_task_has_owner
