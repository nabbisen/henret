import Henret
/-!
# Example 05 — Sleep and Tick

Concept: logical-time timers.

`sleep t deadline` moves the *currently running* task `t` to `sleeping` and
registers a timer entry `⟨deadline, t⟩` in the sorted timer queue.

`tick now` fires expired timers: any entry with `deadline ≤ now` has its task
moved from `sleeping` to `ready` and appended to the ready queue.  Entries
with `deadline > now` are untouched.

Time is a pure `Nat` — no wall clock.

Run with:  `lake env lean examples/05_sleep_and_tick.lean`
-/
open Henret

-- Spawn two tasks and put them both to sleep with different deadlines.
def boot := run RuntimeState.init [.spawn 0, .spawn 0, .schedule, .sleep 0 10,
                                   .schedule, .sleep 1 5]
#eval boot.taskState 0
-- some sleeping  (deadline 10)
#eval boot.taskState 1
-- some sleeping  (deadline 5)
#eval boot.timers.map (fun e => (e.deadline, e.task))
-- [(5, 1), (10, 0)]   sorted by deadline

-- Tick at now=4: nothing expires.
def t4 := (step boot (.tick 4)).1
#eval t4.taskState 0
-- some sleeping
#eval t4.taskState 1
-- some sleeping

-- Tick at now=7: task 1 (deadline 5) expires; task 0 (deadline 10) does not.
def t7 := (step boot (.tick 7)).1
#eval t7.taskState 0
-- some sleeping
#eval t7.taskState 1
-- some ready
#eval t7.readyQ
-- [1]

-- Tick at now=10: task 0 now expires too.
def t10 := (step t7 (.tick 10)).1
#eval t10.taskState 0
-- some ready

-- Proven: tick never wakes a task whose deadline has not passed.
#check @Henret.tick_no_early_wake
-- s.timers contains entry with task t and deadline d → ¬ d ≤ now →
--   ((step s (.tick now)).1).taskState t = some .sleeping

-- Proven: the timer queue stays sorted across all operations.
#check @Henret.run_preserves_sorted

/-! ## Logical time is stored and monotone (v0.2.0, RFC 015) -/

#eval t10.now
-- 10   — the clock advanced with the tick

-- A backwards tick is invalid and leaves the state untouched.
#eval (step t10 (.tick 3)).2
-- invalid
#eval (step t10 (.tick 3)).1.now
-- 10

#check @Henret.tick_backwards_invalid
#check @Henret.step_clock_monotone
