import Henret.Core.Id

namespace Henret

/-- One pending timer: wake `task` once logical time reaches `deadline`. -/
structure TimerEntry where
  deadline : Nat
  task     : TaskId
deriving Repr, DecidableEq, Inhabited

namespace Timer

/-- Sortedness by deadline (non-strict, so equal deadlines coexist). -/
def Sorted (l : List TimerEntry) : Prop :=
  l.Pairwise (fun a b => a.deadline ≤ b.deadline)

@[simp] theorem sorted_nil : Sorted [] := List.Pairwise.nil

/-- Insert keeping the queue sorted. -/
def insertSorted (e : TimerEntry) : List TimerEntry → List TimerEntry
  | [] => [e]
  | x :: xs =>
    if e.deadline ≤ x.deadline then e :: x :: xs
    else x :: insertSorted e xs

theorem mem_insertSorted {e a : TimerEntry} {l : List TimerEntry} :
    a ∈ insertSorted e l ↔ a = e ∨ a ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons x xs ih =>
    by_cases h : e.deadline ≤ x.deadline
    · simp [insertSorted, h]
    · simp only [insertSorted, h, if_false, List.mem_cons, ih]
      constructor
      · rintro (rfl | he | hm)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl he
        · exact Or.inr (Or.inr hm)
      · rintro (he | rfl | hm)
        · exact Or.inr (Or.inl he)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hm)

/-- Sortedness is preserved by insertion (RFC 007 invariant). -/
theorem insertSorted_sorted {e : TimerEntry} {l : List TimerEntry}
    (h : Sorted l) : Sorted (insertSorted e l) := by
  induction l with
  | nil => simp [insertSorted, Sorted]
  | cons x xs ih =>
    rw [Sorted, List.pairwise_cons] at h
    by_cases hc : e.deadline ≤ x.deadline
    · simp only [insertSorted, hc, if_true]
      rw [Sorted, List.pairwise_cons]
      constructor
      · intro b hb
        cases hb with
        | head => exact hc
        | tail _ hb => exact Nat.le_trans hc (h.1 b hb)
      · rw [Sorted] at *
        exact List.pairwise_cons.mpr h
    · simp only [insertSorted, hc, if_false]
      rw [Sorted, List.pairwise_cons]
      constructor
      · intro b hb
        rcases mem_insertSorted.mp hb with rfl | hb
        · exact Nat.le_of_not_le hc
        · exact h.1 b hb
      · exact ih h.2

/-- Entries due at or before `now`, in queue order. -/
def expired (l : List TimerEntry) (now : Nat) : List TimerEntry :=
  l.filter (fun e => e.deadline ≤ now)

/-- Entries strictly in the future, in queue order. -/
def remaining (l : List TimerEntry) (now : Nat) : List TimerEntry :=
  l.filter (fun e => now < e.deadline)

theorem mem_expired {l : List TimerEntry} {now : Nat} {e : TimerEntry} :
    e ∈ expired l now ↔ e ∈ l ∧ e.deadline ≤ now := by
  simp [expired, List.mem_filter]

theorem mem_remaining {l : List TimerEntry} {now : Nat} {e : TimerEntry} :
    e ∈ remaining l now ↔ e ∈ l ∧ now < e.deadline := by
  simp [remaining, List.mem_filter]

/-- Filtering preserves sortedness. -/
theorem sorted_filter (p : TimerEntry → Bool) {l : List TimerEntry}
    (h : Sorted l) : Sorted (l.filter p) := by
  induction l with
  | nil => simp [Sorted]
  | cons x xs ih =>
    rw [Sorted, List.pairwise_cons] at h
    cases hp : p x with
    | true =>
      rw [List.filter_cons_of_pos hp]
      rw [Sorted, List.pairwise_cons]
      exact ⟨fun b hb => h.1 b (List.mem_filter.mp hb).1, ih h.2⟩
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp])]
      exact ih h.2

/-- `remaining` stays sorted. -/
theorem remaining_sorted {l : List TimerEntry} {now : Nat}
    (h : Sorted l) : Sorted (remaining l now) :=
  sorted_filter _ h

end Timer

end Henret

/-!
# Henret.Scheduler.Timer

Logical timers (RFC 007).

Time is logical ticks, not wall-clock time. The timer queue is a list
of entries kept sorted by deadline; `insertSorted` preserves
sortedness (proved here), and `tick now` splits the queue into expired
(`deadline ≤ now`) and future (`now < deadline`) entries.

The field is named `deadline` rather than RFC 007's sketch name `at`
because `at` is a reserved keyword in Lean 4.
-/
