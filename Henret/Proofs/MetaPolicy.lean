import Henret.Scheduler.MetaPolicy

/-!
# Henret.Proofs.MetaPolicy  (RFC 059)

Ordering facts for the metadata policies. These are *selection* theorems
(the chosen task is extremal among ready tasks) — **not** real-time guarantees.
No theorem here claims a deadline is met; that would require fairness/liveness,
which RFC 059 explicitly does not provide.
-/

namespace Henret

/-- A `pickBy` max fold (with a `Bool` comparator faithful to a `Nat` key)
returns an element whose key dominates every element folded over. -/
theorem foldl_best_ge (key : TaskId → Nat) (better : TaskId → TaskId → Bool)
    (hb : ∀ a b, better a b = true → key a < key b)
    (hb2 : ∀ a b, better a b = false → key b ≤ key a)
    (b : TaskId) (l : List TaskId) :
    ∀ u ∈ b :: l, key u ≤ key (l.foldl (fun b u => if better b u then u else b) b) := by
  induction l generalizing b with
  | nil => intro u hu; simp only [List.mem_singleton] at hu; subst hu; simp
  | cons x xs ih =>
    intro u hu
    simp only [List.foldl_cons]
    have hbb' : key b ≤ key (if better b x then x else b) := by
      by_cases h : better b x = true
      · simp only [h, if_true]; exact Nat.le_of_lt (hb b x h)
      · simp only [Bool.not_eq_true] at h; simp only [h, if_false]; exact Nat.le_refl _
    have hxb' : key x ≤ key (if better b x then x else b) := by
      by_cases h : better b x = true
      · simp only [h, if_true]; exact Nat.le_refl _
      · simp only [Bool.not_eq_true] at h; simp only [h, if_false]; exact hb2 b x h
    rcases List.mem_cons.mp hu with h | h
    · subst h; exact Nat.le_trans hbb' (ih _ _ (List.mem_cons_self ..))
    · rcases List.mem_cons.mp h with h | h
      · subst h; exact Nat.le_trans hxb' (ih _ _ (List.mem_cons_self ..))
      · exact ih _ u (List.mem_cons.mpr (Or.inr h))

/-- **`priority_policy_selects_max`** — the highest-priority policy chooses a
ready task whose priority is at least that of every ready task. -/
theorem priority_policy_selects_max (s : RuntimeState) {t : TaskId}
    (h : priorityPolicy.choose s = some t) :
    ∀ u ∈ s.readyQ, priorityOf s u ≤ priorityOf s t := by
  intro u hu
  have hch : priorityPolicy.choose s
      = pickBy (fun b u => priorityOf s b < priorityOf s u) s.readyQ := rfl
  rw [hch] at h
  cases hq : s.readyQ with
  | nil => rw [hq] at h; simp [pickBy] at h
  | cons hd tl =>
    rw [hq] at h hu
    simp only [pickBy] at h; injection h with h; subst h
    refine foldl_best_ge (priorityOf s) (fun b u => priorityOf s b < priorityOf s u)
      (fun a b hab => of_decide_eq_true hab)
      (fun a b hab => Nat.le_of_not_lt (of_decide_eq_false hab)) hd tl u hu

/-! ## Earliest-deadline-first ordering optimality

The bespoke `deadlineLt` order on `Option Nat` (with `none` as the latest) is a
strict total order; these three facts are exactly the hypotheses the fold-min
lemma needs. No theorem here claims a deadline is *met*. -/

/-- `deadlineLt` is irreflexive. -/
theorem deadlineLt_irrefl (a : Option Nat) : deadlineLt a a = false := by
  cases a with
  | none => rfl
  | some x => simp [deadlineLt]

/-- Transitivity bridging a strict step: `a ≤ b` and `a < c` give `¬ c < b`. -/
theorem dlt_htA (a b c : Option Nat)
    (h1 : deadlineLt a b = false) (h2 : deadlineLt a c = true) : deadlineLt c b = false := by
  cases a <;> cases b <;> cases c <;> simp_all [deadlineLt] <;> omega

/-- Transitivity of the non-strict relation: `x ≤ y` and `y ≤ z` give `x ≤ z`. -/
theorem dlt_htB (x y z : Option Nat)
    (h1 : deadlineLt y x = false) (h2 : deadlineLt z y = false) : deadlineLt z x = false := by
  cases x <;> cases y <;> cases z <;> simp_all [deadlineLt] <;> omega

/-- A `pickBy` min fold under a strict-total comparator returns an element that
nothing in the list strictly beats. -/
theorem foldl_winner (better : TaskId → TaskId → Bool)
    (hirr : ∀ a, better a a = false)
    (htA : ∀ p q r, better p q = false → better r q = true → better p r = false)
    (htB : ∀ p q r, better p q = false → better q r = false → better p r = false)
    (acc : TaskId) (l : List TaskId) :
    ∀ u ∈ acc :: l, better (l.foldl (fun b u => if better b u then u else b) acc) u = false := by
  induction l generalizing acc with
  | nil => intro u hu; simp only [List.mem_singleton] at hu; subst hu; exact hirr _
  | cons x xs ih =>
    intro u hu
    simp only [List.foldl_cons]
    by_cases hbx : better acc x = true
    · simp only [hbx, if_true]
      rcases List.mem_cons.mp hu with h | h
      · subst h; exact htA _ _ _ (ih _ _ (List.mem_cons_self ..)) hbx
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact ih _ _ (List.mem_cons_self ..)
        · exact ih _ _ (List.mem_cons.mpr (Or.inr h))
    · simp only [Bool.not_eq_true] at hbx
      simp only [hbx, if_false, Bool.false_eq_true]
      rcases List.mem_cons.mp hu with h | h
      · subst h; exact ih _ _ (List.mem_cons_self ..)
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact htB _ _ _ (ih _ _ (List.mem_cons_self ..)) hbx
        · exact ih _ _ (List.mem_cons.mpr (Or.inr h))

/-- **`deadline_policy_selects_min_deadline`** — the earliest-deadline-first
policy chooses a ready task whose deadline no ready task is strictly earlier
than (a minimum under `deadlineLt`). This is an *ordering* fact only; it does
**not** claim the deadline is met. -/
theorem deadline_policy_selects_min_deadline (s : RuntimeState) {t : TaskId}
    (h : edfPolicy.choose s = some t) :
    ∀ u ∈ s.readyQ, deadlineLt (deadlineOf s u) (deadlineOf s t) = false := by
  intro u hu
  have hch : edfPolicy.choose s
      = pickBy (fun b u => deadlineLt (deadlineOf s u) (deadlineOf s b)) s.readyQ := rfl
  rw [hch] at h
  cases hq : s.readyQ with
  | nil => rw [hq] at h; simp [pickBy] at h
  | cons hd tl =>
    rw [hq] at h hu
    simp only [pickBy] at h; injection h with h; subst h
    exact foldl_winner (fun b u => deadlineLt (deadlineOf s u) (deadlineOf s b))
      (fun a => deadlineLt_irrefl _)
      (fun _ _ _ h1 h2 => dlt_htA _ _ _ h1 h2)
      (fun _ _ _ h1 h2 => dlt_htB _ _ _ h1 h2)
      hd tl u hu

end Henret
