import Henret.Scheduler.Model

namespace Henret

/-! ## Wake helpers preserve everything except `sleeping → ready` -/

theorem wakeOne_preserves_of_ne_sleeping {ts : TaskMap} {u : TaskId}
    {st : TaskState} (h : ts u = some st) (hne : st ≠ .sleeping)
    (t : TaskId) : wakeOne ts t u = some st := by
  by_cases hu : u = t
  · subst hu
    unfold wakeOne
    rw [h]
    cases st <;> simp_all [upd]
  · unfold wakeOne
    cases hts : ts t with
    | none => exact h
    | some s' => cases s' <;> simp_all [upd, hu]

theorem wakeMany_preserves_of_ne_sleeping {ts : TaskMap} {u : TaskId}
    {st : TaskState} (h : ts u = some st) (hne : st ≠ .sleeping) :
    ∀ l : List TaskId, wakeMany ts l u = some st := by
  intro l
  induction l generalizing ts with
  | nil => exact h
  | cons t r ih =>
    exact ih (wakeOne_preserves_of_ne_sleeping h hne t)

theorem wakeOne_other {ts : TaskMap} {t u : TaskId} (h : u ≠ t) :
    wakeOne ts t u = ts u := by
  unfold wakeOne
  cases hts : ts t with
  | none => rfl
  | some s' => cases s' <;> simp [upd, h]

theorem wakeMany_preserves_other {ts : TaskMap} {u : TaskId} :
    ∀ {l : List TaskId}, u ∉ l → wakeMany ts l u = ts u := by
  intro l
  induction l generalizing ts with
  | nil => intro _; rfl
  | cons t r ih =>
    intro hmem
    have h1 : u ≠ t := fun h => hmem (h ▸ List.mem_cons_self t r)
    have h2 : u ∉ r := fun h => hmem (List.mem_cons_of_mem t h)
    show wakeMany (wakeOne ts t) r u = ts u
    rw [ih h2, wakeOne_other h1]

theorem wakeMany_wakes {ts : TaskMap} {t : TaskId} :
    ∀ {l : List TaskId}, t ∈ l → ts t = some .sleeping →
      wakeMany ts l t = some .ready := by
  intro l
  induction l generalizing ts with
  | nil => intro h; cases h
  | cons u r ih =>
    intro hmem hsleep
    by_cases hu : t = u
    · subst hu
      have hone : wakeOne ts t t = some .ready := by
        unfold wakeOne; rw [hsleep]; simp [upd]
      show wakeMany (wakeOne ts t) r t = some .ready
      exact wakeMany_preserves_of_ne_sleeping hone (by simp) r
    · cases hmem with
      | head => exact absurd rfl hu
      | tail _ hr =>
        show wakeMany (wakeOne ts u) r t = some .ready
        exact ih hr (by rw [wakeOne_other hu]; exact hsleep)

/-! ## Terminal-state monotonicity -/

/-- One step never moves a task out of a terminal state. -/
theorem step_preserves_terminal {s : RuntimeState} {u : TaskId}
    {st : TaskState} (h : s.taskState u = some st)
    (hterm : st.isTerminal = true) (op : RuntimeOp) :
    ((step s op).1).taskState u = some st := by
  have hne_sleeping : st ≠ .sleeping := by
    intro he; subst he; simp [TaskState.isTerminal] at hterm
  cases op with
  | spawn a =>
    simp only [step]
    split
    · next heq =>
      have hu : u ≠ s.nextId := by
        intro he; subst he; rw [h] at heq; cases heq
      simp [upd, hu, h]
    · exact h
  | schedule =>
    cases hr : s.running with
    | some _ => simp [step, hr, h]
    | none =>
      cases hq : s.readyQ with
      | nil => simp [step, hr, hq, h]
      | cons t q =>
        by_cases hrun : (s.taskState t).any TaskState.isRunnable = true
        · have hu : u ≠ t := by
            intro he; subst he
            rw [h] at hrun
            simp [Option.any] at hrun
            cases st <;> simp_all [TaskState.isRunnable, TaskState.isTerminal]
          simp [step, hr, hq, hrun, upd, hu, h]
        · simp at hrun
          simp [step, hr, hq, hrun, h]
  | yield t =>
    simp only [step]
    split
    · split
      · next heq =>
        have hu : u ≠ t := by
          intro he; subst he; rw [h] at heq; cases heq
          simp [TaskState.isTerminal] at hterm
        simp [upd, hu, h]
      · exact h
    · exact h
  | complete t =>
    simp only [step]
    split
    · split
      · next heq =>
        have hu : u ≠ t := by
          intro he; subst he; rw [h] at heq; cases heq
          simp [TaskState.isTerminal] at hterm
        simp [upd, hu, h]
      · exact h
    · exact h
  | cancel t =>
    simp only [step]
    split
    · next st' heq =>
      split
      · exact h
      · next hnt =>
        have hu : u ≠ t := by
          intro he; subst he; rw [h] at heq; cases heq
          exact hnt hterm
        simp [upd, hu, h]
    · exact h
  | send a m => simp only [step]; split <;> simp [h]
  | receive a =>
    simp only [step]
    split
    · split <;> simp [h]
    · exact h
  | sleep t d =>
    simp only [step]
    split
    · split
      · next heq =>
        have hu : u ≠ t := by
          intro he; subst he; rw [h] at heq; cases heq
          simp [TaskState.isTerminal] at hterm
        simp [upd, hu, h]
      · exact h
    · exact h
  | tick now =>
    by_cases hle : s.now ≤ now
    · simp only [step, if_pos hle]
      exact wakeMany_preserves_of_ne_sleeping h hne_sleeping _
    · simp [step, hle, h]
  | wake t =>
    simp only [step]
    split
    · next heq =>
      have hu : u ≠ t := by
        intro he; subst he; rw [h] at heq; cases heq
        simp [TaskState.isTerminal] at hterm
      simp [upd, hu, h]
    · exact h

/-- Completed tasks never resume (RFC 004 acceptance). -/
theorem step_preserves_completed {s : RuntimeState} {u : TaskId}
    (h : s.taskState u = some .completed) (op : RuntimeOp) :
    ((step s op).1).taskState u = some .completed :=
  step_preserves_terminal h rfl op

/-- Cancelled tasks never complete later (RFC 004 acceptance). -/
theorem step_preserves_cancelled {s : RuntimeState} {u : TaskId}
    (h : s.taskState u = some .cancelled) (op : RuntimeOp) :
    ((step s op).1).taskState u = some .cancelled :=
  step_preserves_terminal h rfl op

/-- Whole-program monotonicity: terminal states survive any program. -/
theorem run_preserves_terminal {u : TaskId} {st : TaskState}
    (hterm : st.isTerminal = true) :
    ∀ {s : RuntimeState}, s.taskState u = some st →
      ∀ ops : List RuntimeOp, (run s ops).taskState u = some st := by
  intro s h ops
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih =>
    exact ih (step_preserves_terminal h hterm op)

theorem run_preserves_completed {s : RuntimeState} {u : TaskId}
    (h : s.taskState u = some .completed) (ops : List RuntimeOp) :
    (run s ops).taskState u = some .completed :=
  run_preserves_terminal rfl h ops

theorem run_preserves_cancelled {s : RuntimeState} {u : TaskId}
    (h : s.taskState u = some .cancelled) (ops : List RuntimeOp) :
    (run s ops).taskState u = some .cancelled :=
  run_preserves_terminal rfl h ops

/-! ## Wake exactness (RFC 006) -/

/-- `wake t` does not touch any task other than `t`. -/
theorem wake_exact {s : RuntimeState} {t u : TaskId} (h : u ≠ t) :
    ((step s (.wake t)).1).taskState u = s.taskState u := by
  simp only [step]
  split
  · simp [upd, h]
  · rfl

/-- A valid wake moves the exact sleeping task to ready and enqueues
it exactly once at the tail. -/
theorem wake_sets_ready {s : RuntimeState} {t : TaskId}
    (h : s.taskState t = some .sleeping) :
    ((step s (.wake t)).1).taskState t = some .ready ∧
    ((step s (.wake t)).1).readyQ = s.readyQ ++ [t] := by
  simp [step, h, upd]

/-- Duplicate wake cannot duplicate ready entries: after a successful
wake, waking the same task again is invalid and changes nothing. -/
theorem wake_twice_invalid {s : RuntimeState} {t : TaskId}
    (h : s.taskState t = some .sleeping) :
    step ((step s (.wake t)).1) (.wake t) =
      (((step s (.wake t)).1), .invalid) := by
  have hready := (wake_sets_ready h).1
  generalize hS : (step s (.wake t)).1 = s' at hready ⊢
  simp [step, hready]

/-! ## Invalid operations never mutate (RFC 005, RFC 016) -/

/-- An invalid operation never mutates state: if `step` reports
`.invalid`, the state component is exactly the input state.  Combined
with the construction of `step`, this makes "invalid ⇒ no-op" a
theorem rather than a convention. -/
theorem step_invalid_unchanged {s : RuntimeState} {op : RuntimeOp}
    (h : (step s op).2 = .invalid) : (step s op).1 = s := by
  cases op with
  | spawn a =>
    cases hts : s.taskState s.nextId with
    | none => simp [step, hts] at h
    | some _ => simp [step, hts]
  | schedule =>
    cases hr : s.running with
    | some _ => simp [step, hr]
    | none =>
      cases hq : s.readyQ with
      | nil => simp [step, hr, hq]
      | cons t q =>
        by_cases hrun : (s.taskState t).any TaskState.isRunnable = true
        · simp [step, hr, hq, hrun] at h
        · simp at hrun; simp [step, hr, hq, hrun]
  | yield t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st => cases st <;> simp [step, hrt, hts] <;> simp [step, hrt, hts] at h
    · simp [step, hrt]
  | complete t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st => cases st <;> simp [step, hrt, hts] <;> simp [step, hrt, hts] at h
    · simp [step, hrt]
  | cancel t =>
    cases hts : s.taskState t with
    | none => simp [step, hts]
    | some st =>
      by_cases hterm : st.isTerminal = true
      · simp [step, hts, hterm]
      · simp at hterm; simp [step, hts, hterm] at h
  | send a m =>
    cases hmb : s.mailboxes a with
    | none => simp [step, hmb]
    | some mb => simp [step, hmb] at h
  | receive a =>
    cases hmb : s.mailboxes a with
    | none => simp [step, hmb]
    | some mb =>
      cases hd : mb.dequeue with
      | none => simp [step, hmb, hd]
      | some p => simp [step, hmb, hd] at h
  | sleep t d =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st => cases st <;> simp [step, hrt, hts] <;> simp [step, hrt, hts] at h
    · simp [step, hrt]
  | tick t =>
    by_cases hle : s.now ≤ t
    · simp [step, hle] at h
    · simp [step, hle]
  | wake t =>
    cases hts : s.taskState t with
    | none => simp [step, hts]
    | some st => cases st <;> simp [step, hts] <;> simp [step, hts] at h

end Henret

/-!
# Henret.Proofs.Lifecycle

Lifecycle theorems (RFC 004, RFC 006).

Main results:

* `step_preserves_terminal` — no operation moves a task out of a
  terminal state. Corollaries: `step_preserves_completed`,
  `step_preserves_cancelled`, and `run_preserves_*` for whole
  programs. "Completed tasks never resume; cancelled tasks never
  complete later."
* `wake_exact` — `wake t` changes no task other than `t`.
* `wake_sets_ready` / `wake_twice_invalid` — a wake moves exactly the
  sleeping task to ready; a duplicate wake is invalid, so it cannot
  duplicate ready entries.
* `step_invalid_unchanged` — an invalid operation never mutates state
  (RFC 005 invalid-operation policy).

All proofs are kernel-checked; none uses `sorry` or `native_decide`.
-/
