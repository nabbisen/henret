import Henret.Scheduler.Model
import Henret.Core.Id

/-!
# Henret.Proofs.ResourceBranch  (RFC 057)

Per-branch behavioural theorems for the three ledger operations. Each pins
down both the `StepResult` returned and the resulting ledger record, so that
the conformance scenarios (and any downstream client) can rely on the exact
outcome of every reachable branch rather than re-deriving it from `step`.

The proofs are deliberately mechanical (`simp [step, <guards>]`); the value is
in the *statements*, which form the contract for the resource lifecycle.
-/

namespace Henret

/-! ## acquire -/

/-- A running task in `running` state acquires a fresh resource: the result is
`.acquired` of the *old* counter, the new id is owned-and-allocated, and the
counter advances by one. -/
theorem acquire_running_allocates {s : RuntimeState} {t : TaskId}
    (hrun : s.running = some t) (hst : s.taskState t = some .running) :
    (step s (.acquire t)).2 = .acquired s.nextResourceId ∧
    (step s (.acquire t)).1.resources s.nextResourceId = some ⟨t, .allocated⟩ ∧
    (step s (.acquire t)).1.nextResourceId = s.nextResourceId + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [step, hrun, hst, upd_self]

/-- A task that is not the running task cannot acquire: no state change. -/
theorem acquire_not_running_invalid {s : RuntimeState} {t : TaskId}
    (hrun : s.running ≠ some t) :
    step s (.acquire t) = (s, .invalid) := by
  simp [step, hrun]

/-- A running task whose state is not `running` (e.g. already completing)
cannot acquire: no state change. -/
theorem acquire_non_running_state_invalid {s : RuntimeState} {t : TaskId} {st : TaskState}
    (hrun : s.running = some t) (hst : s.taskState t = some st) (hne : st ≠ .running) :
    step s (.acquire t) = (s, .invalid) := by
  cases st <;> simp_all [step, hrun, hst]

/-! ## release -/

/-- The owning running task releases its allocated resource: result `.ok`, the
record flips to `released`. -/
theorem release_owner_allocated_ok {s : RuntimeState} {t : TaskId} {r : ResourceId}
    (hrun : s.running = some t) (hst : s.taskState t = some .running)
    (hres : s.resources r = some ⟨t, .allocated⟩) :
    (step s (.release t r)).2 = .ok ∧
    (step s (.release t r)).1.resources r = some ⟨t, .released⟩ := by
  refine ⟨?_, ?_⟩ <;> simp [step, hrun, hst, hres, upd_self]

/-- A task cannot release a resource it does not own, even while running: no
state change. -/
theorem release_non_owner_invalid {s : RuntimeState} {t o : TaskId} {r : ResourceId}
    (hrun : s.running = some t) (hst : s.taskState t = some .running)
    (hres : s.resources r = some ⟨o, .allocated⟩) (hne : o ≠ t) :
    step s (.release t r) = (s, .invalid) := by
  simp [step, hrun, hst, hres, hne]

/-- Releasing an already-released resource is invalid (double-release): no
state change. -/
theorem release_released_invalid {s : RuntimeState} {t o : TaskId} {r : ResourceId}
    (hrun : s.running = some t) (hst : s.taskState t = some .running)
    (hres : s.resources r = some ⟨o, .released⟩) :
    step s (.release t r) = (s, .invalid) := by
  simp [step, hrun, hst, hres]

/-- Releasing a closing resource is invalid (only `finalize` reclaims it): no
state change. -/
theorem release_closing_invalid {s : RuntimeState} {t o : TaskId} {r : ResourceId}
    (hrun : s.running = some t) (hst : s.taskState t = some .running)
    (hres : s.resources r = some ⟨o, .closing⟩) :
    step s (.release t r) = (s, .invalid) := by
  simp [step, hrun, hst, hres]

/-! ## finalize -/

/-- The environment finalizes a closing resource: result `.ok`, the record
flips to `released` keeping its owner. No running-task guard. -/
theorem finalize_closing_ok {s : RuntimeState} {o : TaskId} {r : ResourceId}
    (hres : s.resources r = some ⟨o, .closing⟩) :
    (step s (.finalize r)).2 = .ok ∧
    (step s (.finalize r)).1.resources r = some ⟨o, .released⟩ := by
  refine ⟨?_, ?_⟩ <;> simp [step, hres, upd_self]

/-- Finalizing an allocated resource is invalid (it must be `closing` first):
no state change. -/
theorem finalize_allocated_invalid {s : RuntimeState} {o : TaskId} {r : ResourceId}
    (hres : s.resources r = some ⟨o, .allocated⟩) :
    step s (.finalize r) = (s, .invalid) := by
  simp [step, hres]

/-- Finalizing an already-released resource is invalid: no state change. -/
theorem finalize_released_invalid {s : RuntimeState} {o : TaskId} {r : ResourceId}
    (hres : s.resources r = some ⟨o, .released⟩) :
    step s (.finalize r) = (s, .invalid) := by
  simp [step, hres]

end Henret
