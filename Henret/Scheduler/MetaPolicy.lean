import Henret.Scheduler.Policy

/-!
# Henret.Scheduler.MetaPolicy  (RFC 059)

Metadata-driven `SchedulingPolicy` instances built on RFC 058's policy layer:
highest-priority-first, earliest-deadline-first, and a priority-then-deadline
hybrid. Each is a sound chooser over `readyQ`; selection reads `taskMeta`
(absent ⇒ `defaultMeta`). Because they are ordinary `SchedulingPolicy` values,
they inherit `policyStep_preserves_wf` for free.

Conventions: higher `priority` wins; a smaller `deadline` is more urgent and a
missing deadline sorts last; ties keep the earlier ready task (stable).
Deadlines are logical-time ordering only — **no real-time guarantee**.
-/

namespace Henret

/-- Pick the "best" element of a list under a strict `better current candidate`
relation, keeping the earliest on ties. -/
def pickBy (better : TaskId → TaskId → Bool) : List TaskId → Option TaskId
  | [] => none
  | t :: ts => some (ts.foldl (fun b u => if better b u then u else b) t)

theorem foldl_best_mem (better : TaskId → TaskId → Bool) (b : TaskId) (l : List TaskId) :
    l.foldl (fun b u => if better b u then u else b) b ∈ b :: l := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hsub : (if better b x then x else b) :: xs ⊆ b :: x :: xs := by
      intro a ha
      rcases List.mem_cons.mp ha with h | h
      · by_cases hb : better b x <;> simp_all <;>
          first
          | exact List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))
          | exact List.mem_cons_self ..
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
    exact hsub (ih (if better b x then x else b))

/-- `pickBy` always returns an element of the list. -/
theorem pickBy_mem {better : TaskId → TaskId → Bool} {l : List TaskId} {t : TaskId}
    (h : pickBy better l = some t) : t ∈ l := by
  cases l with
  | nil => simp [pickBy] at h
  | cons x xs =>
    simp only [pickBy] at h; injection h with h; subst h
    exact foldl_best_mem better x xs

/-- A task's effective priority (default `0` when unset). -/
def priorityOf (s : RuntimeState) (t : TaskId) : Nat :=
  ((s.taskMeta t).getD defaultMeta).priority

/-- A task's effective deadline (default `none` = least urgent). -/
def deadlineOf (s : RuntimeState) (t : TaskId) : Option Nat :=
  ((s.taskMeta t).getD defaultMeta).deadline

/-- `a` is a strictly earlier deadline than `b`; a present deadline beats a
missing one, and `none` is never earlier. -/
def deadlineLt : Option Nat → Option Nat → Bool
  | some x, some y => x < y
  | some _, none   => true
  | none, _        => false

/-- **Highest-priority-first** (stable among equals). -/
def priorityPolicy : SchedulingPolicy where
  choose s := pickBy (fun b u => priorityOf s b < priorityOf s u) s.readyQ
  choose_sound := fun _ _ h => pickBy_mem h

/-- **Earliest-deadline-first** (stable among equals; missing deadline last). -/
def edfPolicy : SchedulingPolicy where
  choose s := pickBy (fun b u => deadlineLt (deadlineOf s u) (deadlineOf s b)) s.readyQ
  choose_sound := fun _ _ h => pickBy_mem h

/-- **Priority-then-deadline** hybrid: higher priority wins; among equal
priorities, the earlier deadline wins. -/
def hybridPolicy : SchedulingPolicy where
  choose s := pickBy
    (fun b u => priorityOf s b < priorityOf s u ||
      (priorityOf s b == priorityOf s u && deadlineLt (deadlineOf s u) (deadlineOf s b)))
    s.readyQ
  choose_sound := fun _ _ h => pickBy_mem h

end Henret
