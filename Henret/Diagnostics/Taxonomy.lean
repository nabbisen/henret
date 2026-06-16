import Henret.Core.Result
import Henret.Actor.Task

/-!
# Henret.Diagnostics.Taxonomy  (RFC 064)

A machine-checked classification of execution outcomes. RFC 064 defines a
project-wide vocabulary so that later work cannot conflate a protocol error,
ordinary waiting, cancellation, timeout, task fault, adapter failure, and
trusted-backend failure under the single word "failure".

This module pins the part of that taxonomy that is *representable in
`StepResult`* into a total `faultClass` function, so the classification is
enforced by the compiler: adding a `StepResult` constructor without classifying
it is a build error. The remaining taxonomy classes are state-level
(`TaskState`) or out-of-model (adapter / trusted backend); see
`docs/fault-taxonomy.md` for the full eight-class table.
-/

namespace Henret

/-- The outcome class of a `StepResult` (RFC 064, the `StepResult`-representable
slice of the taxonomy).

- `progress` — the operation made normal forward progress.
- `waiting` — a legal operation cannot proceed now because a resource is
  unavailable (empty mailbox → park; full mailbox → reject). **Not a fault.**
- `timeout` — a waiting condition expired by time rather than delivery.
  **Not a fault.**
- `protocolInvalid` — a semantic precondition was violated (the only fault
  class a pure `StepResult` can report). -/
inductive FaultClass
  | progress
  | waiting
  | timeout
  | protocolInvalid
  deriving DecidableEq, Repr, Inhabited

/-- Total classification of every `StepResult` outcome. -/
def faultClass : StepResult → FaultClass
  | .ok | .spawned _ | .scheduled _ | .received _ | .woke _ | .acquired _ => .progress
  | .blocked | .backpressured => .waiting
  | .timedOut => .timeout
  | .invalid => .protocolInvalid

/-- Of the `StepResult`-representable classes, only protocol invalidity is a
fault. Progress, waiting, and timeout are all normal transitions. -/
def FaultClass.isFault : FaultClass → Bool
  | .protocolInvalid => true
  | _ => false

/-- A `StepResult` is a fault exactly when it is protocol-invalid. -/
def StepResult.isFault (r : StepResult) : Bool := (faultClass r).isFault

/-! ## Pinning theorems (each by `rfl`/`decide`; no new axioms) -/

@[simp] theorem faultClass_invalid : faultClass .invalid = .protocolInvalid := rfl
@[simp] theorem faultClass_blocked : faultClass .blocked = .waiting := rfl
@[simp] theorem faultClass_backpressured : faultClass .backpressured = .waiting := rfl
@[simp] theorem faultClass_timedOut : faultClass .timedOut = .timeout := rfl
@[simp] theorem faultClass_ok : faultClass .ok = .progress := rfl

/-- **The disambiguation RFC 064 insists on**: protocol invalidity and ordinary
waiting are different classes. A parked `receive` (`.blocked`) is *not* a
rejected one (`.invalid`). -/
theorem blocked_not_invalid_class : faultClass .blocked ≠ faultClass .invalid := by decide

/-- Backpressure is ordinary waiting, not a protocol error. -/
theorem backpressured_not_invalid_class :
    faultClass .backpressured ≠ faultClass .invalid := by decide

/-- A timeout is not a protocol error. -/
theorem timedOut_not_invalid_class : faultClass .timedOut ≠ faultClass .invalid := by decide

/-- Protocol invalidity is a fault. -/
theorem invalid_is_fault : StepResult.isFault .invalid = true := by decide

/-- Ordinary waiting is **not** a fault (RFC 064 class 2 required property). -/
theorem blocked_not_fault : StepResult.isFault .blocked = false := by decide

/-- Backpressure is not a fault. -/
theorem backpressured_not_fault : StepResult.isFault .backpressured = false := by decide

/-- A timeout is not a fault. -/
theorem timedOut_not_fault : StepResult.isFault .timedOut = false := by decide

/-- Normal progress is not a fault. -/
theorem ok_not_fault : StepResult.isFault .ok = false := by decide

end Henret
