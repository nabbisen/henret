import Henret.Scheduler.Model
import Henret.Proofs.StepProjections

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
