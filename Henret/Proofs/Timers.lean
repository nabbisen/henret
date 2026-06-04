import Henret.Scheduler.Model
import Henret.Proofs.Lifecycle

namespace Henret

/-- The tasks `tick now` wakes. -/
def tickWoken (s : RuntimeState) (now : Nat) : List TaskId :=
  (Timer.expired s.timers now).map TimerEntry.task

/-- A future entry survives the tick untouched. -/
theorem tick_keeps_future {s : RuntimeState} {now : Nat}
    {e : TimerEntry} (hmem : e ∈ s.timers) (hfut : now < e.deadline) :
    e ∈ ((step s (.tick now)).1).timers := by
  simp only [step]
  exact Timer.mem_remaining.mpr ⟨hmem, hfut⟩

/-- No early wake: a task not named by any expired entry keeps its
state across the tick. -/
theorem tick_no_early_wake {s : RuntimeState} {now : Nat} {t : TaskId}
    (h : t ∉ tickWoken s now) :
    ((step s (.tick now)).1).taskState t = s.taskState t := by
  simp only [step]
  exact wakeMany_preserves_other h

/-- Expired wake with exact identity: every sleeping task with a due
entry is ready after the tick. -/
theorem tick_wakes_expired {s : RuntimeState} {now : Nat}
    {e : TimerEntry} (hmem : e ∈ s.timers) (hdue : e.deadline ≤ now)
    (hsleep : s.taskState e.task = some .sleeping) :
    ((step s (.tick now)).1).taskState e.task = some .ready := by
  simp only [step]
  apply wakeMany_wakes _ hsleep
  exact List.mem_map_of_mem TimerEntry.task
    (Timer.mem_expired.mpr ⟨hmem, hdue⟩)

/-- Woken tasks are enqueued (in timer order) by the tick. -/
theorem tick_enqueues_woken (s : RuntimeState) (now : Nat) :
    ((step s (.tick now)).1).readyQ = s.readyQ ++ tickWoken s now := by
  simp only [step]; rfl

/-- Every operation preserves timer-queue sortedness. -/
theorem step_preserves_sorted {s : RuntimeState}
    (h : Timer.Sorted s.timers) (op : RuntimeOp) :
    Timer.Sorted ((step s op).1).timers := by
  cases op with
  | spawn a => simp only [step]; split <;> exact h
  | schedule =>
    simp only [step]
    split
    · split <;> exact h
    · exact h
  | yield t =>
    simp only [step]
    split
    · split <;> exact h
    · exact h
  | complete t =>
    simp only [step]
    split
    · split <;> exact h
    · exact h
  | cancel t =>
    simp only [step]
    split
    · split
      · exact h
      · exact Timer.sorted_filter _ h
    · exact h
  | send a m => simp only [step]; split <;> exact h
  | receive a =>
    simp only [step]
    split
    · split <;> exact h
    · exact h
  | sleep t d =>
    simp only [step]
    split
    · split
      · exact Timer.insertSorted_sorted h
      · exact h
    · exact h
  | tick now =>
    simp only [step]
    exact Timer.remaining_sorted h
  | wake t =>
    simp only [step]
    split
    · exact Timer.sorted_filter _ h
    · exact h

/-- Whole-program corollary: the queue is sorted in every reachable
state of any program starting from a sorted queue. -/
theorem run_preserves_sorted {s : RuntimeState}
    (h : Timer.Sorted s.timers) :
    ∀ ops : List RuntimeOp, Timer.Sorted (run s ops).timers := by
  intro ops
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih => exact ih (step_preserves_sorted h op)

end Henret

/-!
# Henret.Proofs.Timers

Timer theorems (RFC 007).

* `tick_no_early_wake` — `tick now` does not wake a task that has no
  expired timer; future entries stay in the queue.
* `tick_wakes_expired` — `tick now` wakes every sleeping task whose
  deadline is due, with exact identity.
* `step_preserves_sorted` — every operation preserves timer-queue
  sortedness; combined with `Timer.insertSorted_sorted`, the queue is
  sorted in every reachable state.
-/
