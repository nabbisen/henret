import Henret
/-!
# Example 01 — Task Lifecycle

Concept: the task lifecycle state machine.

```
new ──▶ ready ──▶ running ──▶ yielded ──▶ (back to ready)
                    │
                    ├──▶ sleeping ──▶ (back to ready via tick/wake)
                    │
                    ├──▶ completed  (terminal)
                    └──▶ cancelled  (terminal)
```

Run with:  `lake env lean examples/01_task_lifecycle.lean`
-/
open Henret

-- Convenient alias for readability.
def ts (s : RuntimeState) (t : TaskId) : Option TaskState := s.taskState t

-- Step 0: empty runtime.
#eval ts RuntimeState.init 0
-- none   (task 0 has not been spawned)

-- Step 1: spawn a task for actor 0.  The fresh id is 0.
def s1 := (step RuntimeState.init (.spawn 0)).1
#eval ts s1 0
-- some new   (spawned, queued, never scheduled)

-- Step 2: schedule — pop from the ready queue and run it.
def s2 := (step s1 .schedule).1
#eval ts s2 0
-- some running

-- Step 3: yield — voluntarily give back the CPU; re-queue.
def s3 := (step s2 (.yield 0)).1
#eval ts s3 0
-- some yielded
#eval s3.readyQ
-- [0]   (back in the queue)

-- Step 4: schedule again to re-run the yielded task.
def s4 := (step s3 .schedule).1
#eval ts s4 0
-- some running

-- Step 5: complete — the task is done.
def s5 := (step s4 (.complete 0)).1
#eval ts s5 0
-- some completed

-- The theorem that guarantees step 5 can never be undone:
#check @Henret.step_preserves_completed
-- ∀ (s : RuntimeState) (u : TaskId), s.taskState u = some .completed →
--   ∀ (op : RuntimeOp), ((step s op).1).taskState u = some .completed
