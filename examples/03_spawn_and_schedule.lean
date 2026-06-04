import Henret
/-!
# Example 03 — Spawn and Schedule

Concept: the ready queue and the `schedule` operation.

`spawn` appends the fresh task id to the ready queue.  `schedule` pops the
head (FIFO), transitions it from `new`/`ready`/`yielded` to `running`, and
fills the `running` slot.  Only one task runs at a time.

Run with:  `lake env lean examples/03_spawn_and_schedule.lean`
-/
open Henret

-- Spawn three tasks for actor 0.
def s := run RuntimeState.init [.spawn 0, .spawn 0, .spawn 0]
#eval s.readyQ
-- [0, 1, 2]   (tasks enqueued in spawn order)
#eval s.running
-- none   (nobody scheduled yet)

-- Schedule: run the head (task 0).
def s1 := (step s .schedule).1
#eval s1.running
-- some 0
#eval s1.readyQ
-- [1, 2]   (0 is now running)
#eval s1.taskState 0
-- some running

-- Complete task 0 and schedule the next.
def s2 := (step s1 (.complete 0)).1
def s3 := (step s2 .schedule).1
#eval s3.running
-- some 1

-- Invalid: schedule while a task is already running.
#eval (step s3 .schedule).2
-- invalid   (the running slot is occupied)

-- Invalid: schedule when the ready queue is empty.
def s4 := run s3 [.complete 1, .schedule, .complete 2]
#eval (step s4 .schedule).2
-- invalid   (queue is empty)
