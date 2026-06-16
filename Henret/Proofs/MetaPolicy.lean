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

end Henret
