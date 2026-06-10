import Henret.Progress.Policy
/-!
  # Henret.Progress.Examples  (RFC 046)

  Concrete fair and unfair operation sequences, with kernel-checked
  witnesses.  These make the honesty story explicit: fairness is a
  property of the *scheduler's choices* (the op sequence), not of the
  model — an op sequence that stops scheduling starves runnable tasks.
-/
namespace Henret.Progress

open Henret

/-! ## A fair schedule

    Two tasks, each scheduled and completed.  Both runnable tasks get a
    turn within the window. -/

/-- spawn two tasks, then schedule+complete each in turn. -/
def fairOps : List RuntimeOp :=
  [.spawn 7, .spawn 9, .schedule, .complete 0, .schedule, .complete 1]

/-- Task 0 (the readyQ head at step 2) is scheduled at step 2. -/
theorem fair_task0_scheduled : scheduledAtStep RuntimeState.init fairOps 2 0 := by decide

/-- Task 1 is scheduled at step 4 — it gets its turn after task 0 vacates. -/
theorem fair_task1_scheduled : scheduledAtStep RuntimeState.init fairOps 4 1 := by decide

/-! ## An unfair schedule

    Two tasks are spawned and only task 0 is ever scheduled.  Task 1 is
    runnable from step 2 onward but the op sequence never schedules it. -/

/-- spawn two tasks, schedule task 0 — and stop.  Task 1 starves. -/
def unfairOps : List RuntimeOp :=
  [.spawn 7, .spawn 9, .schedule]

/-- Task 1 is runnable after the third op (it sits in `readyQ`). -/
theorem unfair_task1_runnable : runnableAtStep RuntimeState.init unfairOps 3 1 := by decide

/-- Yet task 1 is never scheduled at any step of `unfairOps` — a
    representable starvation.  (The only `schedule` op, at index 2,
    selects the head task 0, not task 1.) -/
theorem unfair_task1_never_scheduled :
    ∀ i, i < unfairOps.length → ¬ scheduledAtStep RuntimeState.init unfairOps i 1 := by
  decide

/-- Consequently `unfairOps` does **not** satisfy bounded ready-fairness
    for any window that fits inside the trace: task 1 is runnable at
    step 3 but no schedule of it occurs.  (Stated here for `k = 0`; the
    same starvation holds for any `k` since there is no later schedule.) -/
theorem unfairOps_not_bounded_fair_0 :
    ¬ BoundedReadyFair 0 RuntimeState.init unfairOps := by
  intro hfair
  obtain ⟨j, hij, hjk, hsched⟩ := hfair 3 1 unfair_task1_runnable
  -- k = 0 forces j = 3, but step 3 is past the end of the op list (no schedule there)
  have : j = 3 := Nat.le_antisymm hjk hij
  subst this
  exact absurd hsched (by decide)

end Henret.Progress
