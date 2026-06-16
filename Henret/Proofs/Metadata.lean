import Henret.Scheduler.Model
import Henret.Proofs.Invariants
import Henret.Proofs.StepProjections

/-!
# Henret.Proofs.Metadata  (RFC 059)

Scheduling metadata (`taskMeta`) is **not** part of `WellFormed`: it is optional
annotation, and the non-goal "not every task must carry metadata" rules out an
"every spawned task has metadata" invariant. So the two metadata operations
preserve the whole 33-field invariant trivially — they touch only `taskMeta`,
which no `WellFormed` field mentions.
-/

namespace Henret

/-- Overwriting `taskMeta` preserves the full invariant: no `WellFormed` field
mentions `taskMeta`. -/
theorem wf_taskMeta_only {s : RuntimeState} (h : WellFormed s)
    (M : TaskId → Option TaskMeta) : WellFormed { s with taskMeta := M } :=
  { h with }

/-- `setPriority` preserves `WellFormed`. -/
theorem preserves_wf_setPriority {s : RuntimeState} (h : WellFormed s)
    (t : TaskId) (p : Nat) : WellFormed (step s (.setPriority t p)).1 := by
  simp only [step]; (repeat' split) <;> first | exact h | exact wf_taskMeta_only h _

/-- `setDeadline` preserves `WellFormed`. -/
theorem preserves_wf_setDeadline {s : RuntimeState} (h : WellFormed s)
    (t : TaskId) (d : Nat) : WellFormed (step s (.setDeadline t d)).1 := by
  simp only [step]; (repeat' split) <;> first | exact h | exact wf_taskMeta_only h _

/-- `setPriority` only writes the metadata of a spawned task: when `t` is not
spawned the operation is a no-op (`metadata_spawned` consistency, local form). -/
theorem setPriority_meta_of_spawned {s : RuntimeState} {t : TaskId} {p : Nat}
    (hns : s.taskState t = none) : (step s (.setPriority t p)).1.taskMeta = s.taskMeta := by
  simp [step, hns]

/-- `setDeadline` only writes the metadata of a spawned task. -/
theorem setDeadline_meta_of_spawned {s : RuntimeState} {t : TaskId} {d : Nat}
    (hns : s.taskState t = none) : (step s (.setDeadline t d)).1.taskMeta = s.taskMeta := by
  simp [step, hns]

end Henret
