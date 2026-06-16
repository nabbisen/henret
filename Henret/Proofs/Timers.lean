import Henret.Scheduler.Model
import Henret.Proofs.Lifecycle
import Henret.Proofs.StepProjections

namespace Henret

/-- The sleeping tasks that `tick now` wakes. Under `WellFormed` all expired
timer tasks are sleeping; the filter keeps it clean in arbitrary states. -/
def tickWokenSleeping (s : RuntimeState) (now : Nat) : List TaskId :=
  ((Timer.expired s.timers now).map TimerEntry.task).filter
    (fun u => s.taskState u = some .sleeping)

/-- The timed-waiting tasks that `tick now` wakes (RFC 040). -/
def tickWokenTimed (s : RuntimeState) (now : Nat) : List TaskId :=
  ((Timer.expired s.timers now).map TimerEntry.task).filter
    (fun u => s.taskState u = some .waitingTimed)

/-- All tasks woken by a valid tick. -/
def tickWoken (s : RuntimeState) (now : Nat) : List TaskId :=
  tickWokenSleeping s now ++ tickWokenTimed s now

-- backward compat: tickWoken used to equal wokenSleeping only
theorem tickWoken_def (s : RuntimeState) (now : Nat) :
    tickWoken s now = tickWokenSleeping s now ++ tickWokenTimed s now := rfl

/-- A future entry survives a valid tick untouched. -/
theorem tick_keeps_future {s : RuntimeState} {now : Nat}
    (hle : s.now ≤ now)
    {e : TimerEntry} (hmem : e ∈ s.timers) (hfut : now < e.deadline) :
    e ∈ ((step s (.tick now)).1).timers := by
  simp only [step, if_pos hle]
  exact Timer.mem_remaining.mpr ⟨hmem, hfut⟩

/-- No early wake: a task not in the woken set keeps its state. -/
theorem tick_no_early_wake {s : RuntimeState} {now : Nat} {t : TaskId}
    (hle : s.now ≤ now) (h : t ∉ tickWoken s now) :
    ((step s (.tick now)).1).taskState t = s.taskState t := by
  simp only [step, if_pos hle, tickWoken, tickWokenSleeping, tickWokenTimed] at h ⊢
  exact wakeMany_preserves_other h

/-- Expired sleeping task wakes after a valid tick. -/
theorem tick_wakes_expired {s : RuntimeState} {now : Nat}
    (hle : s.now ≤ now)
    {e : TimerEntry} (hmem : e ∈ s.timers) (hdue : e.deadline ≤ now)
    (hsleep : s.taskState e.task = some .sleeping) :
    ((step s (.tick now)).1).taskState e.task = some .ready := by
  simp only [step, if_pos hle]
  apply wakeMany_wakes _ (Or.inl hsleep)
  simp only [tickWokenSleeping, List.mem_append, List.mem_filter, decide_eq_true_eq]
  exact Or.inl ⟨List.mem_map_of_mem TimerEntry.task (Timer.mem_expired.mpr ⟨hmem, hdue⟩), hsleep⟩

/-- Expired timed-waiting task wakes after a valid tick (RFC 040). -/
theorem tick_wakes_timed_expired {s : RuntimeState} {now : Nat}
    (hle : s.now ≤ now)
    {e : TimerEntry} (hmem : e ∈ s.timers) (hdue : e.deadline ≤ now)
    (htimed : s.taskState e.task = some .waitingTimed) :
    ((step s (.tick now)).1).taskState e.task = some .ready := by
  simp only [step, if_pos hle]
  apply wakeMany_wakes _ (Or.inr htimed)
  simp only [tickWokenTimed, List.mem_append, List.mem_filter, decide_eq_true_eq]
  exact Or.inr ⟨List.mem_map_of_mem TimerEntry.task (Timer.mem_expired.mpr ⟨hmem, hdue⟩), htimed⟩

/-- A valid tick enqueues all woken tasks. -/
theorem tick_enqueues_woken (s : RuntimeState) {now : Nat}
    (hle : s.now ≤ now) :
    ((step s (.tick now)).1).readyQ = s.readyQ ++ tickWoken s now := by
  simp only [step, if_pos hle, tickWoken, tickWokenSleeping, tickWokenTimed]

/-- A valid tick advances the logical clock to exactly `now`. -/
theorem tick_advances_clock (s : RuntimeState) {now : Nat}
    (hle : s.now ≤ now) :
    ((step s (.tick now)).1).now = now := by
  simp only [step, if_pos hle]

/-- A backwards tick is invalid and changes nothing. -/
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
  | spawn a =>
    simp only [step]; split <;> (try split) <;> exact Nat.le_refl _
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
  | send t b m =>
    simp only [step]
    (repeat' split) <;> simp_all
  | receive t =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> simp_all
  | inject a m =>
    simp only [step]
    (repeat' split) <;> simp_all
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
  | cancelTree _ => exact Nat.le_refl _
  | fail t =>
    simp only [step]; split <;> (try split) <;> (try split) <;> exact Nat.le_refl _
  | restartOne p c a =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> exact Nat.le_refl _
  | receiveUntil t deadline =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;> simp_all
  | receiveByOccurrence t occ =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;> simp_all
  | receiveFrom t src =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;> simp_all
  | closeActor a =>
    simp only [step] <;> (try split) <;> exact Nat.le_refl _
  | shutdown => exact Nat.le_refl _
  | stopWhenIdle =>
    simp only [step] <;> (try split) <;> exact Nat.le_refl _
  | stopWhenDrained =>
    simp only [step] <;> (try split) <;> exact Nat.le_refl _
  | acquire t =>
    simp only [step] <;> (repeat' split) <;> exact Nat.le_refl _
  | acquireActor a =>
    simp only [step] <;> (repeat' split) <;> exact Nat.le_refl _
  | release t r =>
    simp only [step] <;> (repeat' split) <;> exact Nat.le_refl _
  | finalize r =>
    simp only [step] <;> (repeat' split) <;> exact Nat.le_refl _
  | setPriority t p =>
    simp only [step] <;> (repeat' split) <;> exact Nat.le_refl _
  | setDeadline t d =>
    simp only [step] <;> (repeat' split) <;> exact Nat.le_refl _
/-- Every operation preserves timer-queue sortedness. -/
theorem step_preserves_sorted {s : RuntimeState}
    (h : Timer.Sorted s.timers) (op : RuntimeOp) :
    Timer.Sorted ((step s op).1).timers := by
  cases op with
  | spawn a => simp only [step]; split <;> (try split) <;> exact h
  | spawnChild t a =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;> simp_all
  | schedule =>
    simp only [step]; split
    · split <;> exact h
    · exact h
  | yield t =>
    simp only [step]; split
    · split <;> exact h
    · exact h
  | complete t =>
    simp only [step]; split
    · split <;> exact h
    · exact h
  | cancel t =>
    simp only [step]; split
    · split
      · exact h
      · exact Timer.sorted_filter _ h
    · exact h
  | send t b m =>
    simp only [step]
    (repeat' split) <;> simp_all [Timer.sorted_filter]
  | receive t => simpa using h
  | inject a m =>
    simp only [step]
    (repeat' split) <;> simp_all [Timer.sorted_filter]
  | sleep t d =>
    simp only [step]; split
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
    simp only [step]; split
    · exact Timer.sorted_filter _ h
    · exact h
  | cancelTree _ =>
    simp only [step]
    exact Timer.sorted_filter _ h
  | fail t =>
    simp only [step]
    split <;> (try split) <;> first | exact h | exact Timer.sorted_filter _ h
  | restartOne p c a =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> exact h
  | receiveUntil t deadline =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;> simp_all [Timer.insertSorted_sorted]
  | receiveByOccurrence t occ =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;> simp_all [Timer.insertSorted_sorted]
  | receiveFrom t src =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;> simp_all [Timer.insertSorted_sorted]
  | closeActor a => simp only [step] <;> (try split) <;> exact h
  | shutdown => exact h
  | stopWhenIdle => simp only [step] <;> (try split) <;> exact h
  | stopWhenDrained => simp only [step] <;> (try split) <;> exact h
  | acquire t => simp only [step] <;> (repeat' split) <;> exact h
  | acquireActor a => simp only [step] <;> (repeat' split) <;> exact h
  | release t r => simp only [step] <;> (repeat' split) <;> exact h
  | finalize r => simp only [step] <;> (repeat' split) <;> exact h
  | setPriority t p => simp only [step] <;> (repeat' split) <;> exact h
  | setDeadline t d => simp only [step] <;> (repeat' split) <;> exact h

/-- Whole-program corollary: the queue is sorted in every reachable state. -/
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

Timer theorems (RFC 007 / RFC 040).

* `tick_no_early_wake` — `tick now` does not wake a task not in the woken set.
* `tick_wakes_expired` — `tick now` wakes every sleeping task whose deadline is due.
* `tick_wakes_timed_expired` — same for `waitingTimed` tasks (RFC 040).
* `step_preserves_sorted` — every operation preserves timer-queue sortedness.
-/
