import Henret
/-!
# Example 06 — Cancel

Concept: `cancelled` is a **terminal** state.

`cancel t` moves task `t` to `cancelled` regardless of its current lifecycle
state (ready, running, sleeping, yielded), removes it from the ready queue and
the timer queue, and clears the running slot if `t` was running.

After cancellation no operation can change `t`'s state.  This is not a
convention — it is a **theorem**.

Run with:  `lake env lean examples/06_cancel_task.lean`
-/
open Henret

-- Cancel a ready task.
def s := run RuntimeState.init [.spawn 0]
#eval s.taskState 0
-- some new / enqueued as ready

def s1 := (step s (.cancel 0)).1
#eval s1.taskState 0
-- some cancelled
#eval s1.readyQ
-- []   (removed from the queue)

-- Every subsequent operation leaves it cancelled.
#eval (step s1 (.complete 0)).1.taskState 0
-- some cancelled   (complete is invalid; state unchanged)
#eval (step s1 (.wake 0)).1.taskState 0
-- some cancelled   (wake requires sleeping; invalid here)
#eval (step s1 (.spawn 1)).1.taskState 0
-- some cancelled   (spawn only creates task 1; task 0 untouched)

-- Cancel a sleeping task.
def boot := run RuntimeState.init [.spawn 0, .schedule, .sleep 0 100]
#eval boot.taskState 0
-- some sleeping

def s2 := (step boot (.cancel 0)).1
#eval s2.taskState 0
-- some cancelled
#eval s2.timers   -- timer entry for task 0 is removed
-- []

-- Proven: no step can move a cancelled task out of cancelled.
#check @Henret.step_preserves_cancelled
-- ∀ (s : RuntimeState) (u : TaskId),
--   s.taskState u = some .cancelled →
--   ∀ (op : RuntimeOp), ((step s op).1).taskState u = some .cancelled

-- Proven: the same guarantee extends to whole programs.
#check @Henret.run_preserves_cancelled
