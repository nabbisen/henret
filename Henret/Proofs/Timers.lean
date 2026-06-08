import Henret.Scheduler.Model
import Henret.Proofs.Lifecycle
import Henret.Proofs.StepProjections

namespace Henret

/-- The tasks `tick now` wakes: expired timer tasks that are genuinely
sleeping. The filter keeps the ready queue clean even in arbitrary
(non-reachable) states; under `WellFormed` it is a no-op. -/
def tickWoken (s : RuntimeState) (now : Nat) : List TaskId :=
  ((Timer.expired s.timers now).map TimerEntry.task).filter
    (fun u => s.taskState u = some .sleeping)

/-- A future entry survives a valid tick untouched. -/
theorem tick_keeps_future {s : RuntimeState} {now : Nat}
    (hle : s.now ≤ now)
    {e : TimerEntry} (hmem : e ∈ s.timers) (hfut : now < e.deadline) :
    e ∈ ((step s (.tick now)).1).timers := by
  simp only [step, if_pos hle]
  exact Timer.mem_remaining.mpr ⟨hmem, hfut⟩

/-- No early wake: a task not in the woken set keeps its state across
a valid tick. In particular a task all of whose entries are in the
future is untouched. -/
theorem tick_no_early_wake {s : RuntimeState} {now : Nat} {t : TaskId}
    (hle : s.now ≤ now) (h : t ∉ tickWoken s now) :
    ((step s (.tick now)).1).taskState t = s.taskState t := by
  simp only [step, if_pos hle]
  exact wakeMany_preserves_other h

/-- Expired wake with exact identity: every sleeping task with a due
entry is ready after a valid tick. -/
theorem tick_wakes_expired {s : RuntimeState} {now : Nat}
    (hle : s.now ≤ now)
    {e : TimerEntry} (hmem : e ∈ s.timers) (hdue : e.deadline ≤ now)
    (hsleep : s.taskState e.task = some .sleeping) :
    ((step s (.tick now)).1).taskState e.task = some .ready := by
  simp only [step, if_pos hle]
  apply wakeMany_wakes _ hsleep
  refine List.mem_filter.mpr ⟨?_, by simp [hsleep]⟩
  exact List.mem_map_of_mem TimerEntry.task
    (Timer.mem_expired.mpr ⟨hmem, hdue⟩)

/-- Woken tasks are enqueued (in timer order) by a valid tick. -/
theorem tick_enqueues_woken (s : RuntimeState) {now : Nat}
    (hle : s.now ≤ now) :
    ((step s (.tick now)).1).readyQ = s.readyQ ++ tickWoken s now := by
  simp only [step, if_pos hle]; rfl

/-- A valid tick advances the logical clock to exactly `now`. -/
theorem tick_advances_clock (s : RuntimeState) {now : Nat}
    (hle : s.now ≤ now) :
    ((step s (.tick now)).1).now = now := by
  simp only [step, if_pos hle]

/-- A backwards tick is invalid and changes nothing: logical time is
monotone (RFC 015). -/
theorem tick_backwards_invalid (s : RuntimeState) {now : Nat}
    (hlt : now < s.now) :
    step s (.tick now) = (s, .invalid) := by
  have : ¬ s.now ≤ now := by omega
  simp only [step, if_neg this]

/-- No operation ever decreases the logical clock. -/
theorem step_clock_monotone (s : RuntimeState) (op : RuntimeOp) :
    s.now ≤ ((step s op).1).now := by
  cases op with
  | tick t =>
    by_cases hle : s.now ≤ t
    · simp only [step, if_pos hle]; exact hle
    · simp [step, hle]
  | spawn a => cases hts : s.taskState s.nextId <;> simp [step, hts]
  | spawnChild t a =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;> simp_all
  | schedule =>
    cases hr : s.running with
    | some _ => simp [step, hr]
    | none =>
      cases hq : s.readyQ with
      | nil => simp [step, hr, hq]
      | cons t q =>
        by_cases hrun : (s.taskState t).any TaskState.isRunnable = true
        · simp [step, hr, hq, hrun]
        · simp at hrun; simp [step, hr, hq, hrun]
  | yield t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st => cases st <;> simp [step, hrt, hts]
    · simp [step, hrt]
  | complete t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st => cases st <;> simp [step, hrt, hts]
    · simp [step, hrt]
  | cancel t =>
    cases hts : s.taskState t with
    | none => simp [step, hts]
    | some st => by_cases hterm : st.isTerminal <;> simp [step, hts, hterm]
  | send t b m => simp
  | receive t => simp
  | inject a m => simp
  | sleep t d =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st => cases st <;> simp [step, hrt, hts]
    · simp [step, hrt]
  | wake t =>
    cases hts : s.taskState t with
    | none => simp [step, hts]
    | some st => cases st <;> simp [step, hts]

/-- Every operation preserves timer-queue sortedness. -/
theorem step_preserves_sorted {s : RuntimeState}
    (h : Timer.Sorted s.timers) (op : RuntimeOp) :
    Timer.Sorted ((step s op).1).timers := by
  cases op with
  | spawn a => simp only [step]; split <;> exact h
  | spawnChild t a =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;> simp_all
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
  | send t b m => simpa using h
  | receive t => simpa using h
  | inject a m => simpa using h
  | sleep t d =>
    simp only [step]
    split
    · split
      · exact Timer.insertSorted_sorted h
      · exact h
    · exact h
  | tick now =>
    by_cases hle : s.now ≤ now
    · simp only [step, if_pos hle]
      exact Timer.remaining_sorted h
    · simp [step, hle, h]
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
