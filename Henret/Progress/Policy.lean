import Henret.Trace
/-!
  # Henret.Progress.Policy  (RFC 046)

  An **optional** policy layer for conditional liveness and fairness.

  Henret's core is a *safety* model: `reachable_wf` proves reachable states
  are well-formed, not that tasks make progress.  This module keeps that
  separation intact.  Nothing here is added to `WellFormed`.  Every
  progress statement is **conditional** on an explicit, named scheduling
  assumption — honest weak progress, never an unconditional liveness
  claim.

  ## Approach (RFC 046: "finite policy first")

  We index over *operation steps* (not raw trace events, which a single op
  may emit several of) and reconstruct the state at each prefix with
  `run s (ops.take i)`.  Predicates are decidable on closed terms, so
  fair/unfair example traces can be checked by `decide`.

  ## What is honest here

  - The model's `readyQ` is **FIFO**: `schedule` takes the head; `yield`,
    `spawn`, and wakeups append to the tail.  So the head of `readyQ` is
    always the next task scheduled — a genuine bounded-progress fact
    (`schedule_schedules_head`), kernel-checked.
  - Whole-program fairness is **not** unconditional: an op sequence that
    simply stops issuing `schedule` starves every queued task.  We make
    that explicit with a representable unfair trace.
-/
namespace Henret.Progress

open Henret Henret.Trace

/-! ## State reconstruction and trace-step predicates -/

/-- The state after the first `i` operations. -/
def stateAt (s : RuntimeState) (ops : List RuntimeOp) (i : Nat) : RuntimeState :=
  run s (ops.take i)

/-- `t` is runnable (queued in `readyQ`) at operation step `i`. -/
def runnableAtStep (s : RuntimeState) (ops : List RuntimeOp) (i : Nat) (t : TaskId) : Prop :=
  t ∈ (stateAt s ops i).readyQ

/-- Operation `i` is a `schedule` that selects task `t`. -/
def scheduledAtStep (s : RuntimeState) (ops : List RuntimeOp) (i : Nat) (t : TaskId) : Prop :=
  ∃ op, ops[i]? = some op ∧ (step (stateAt s ops i) op).2 = .scheduled t

instance (s ops i t) : Decidable (runnableAtStep s ops i t) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- `scheduledAtStep` is decidable: `ops[i]?` pins the operation, then the
    result of `step` is decidably `.scheduled t`. -/
instance (s ops i t) : Decidable (scheduledAtStep s ops i t) :=
  match hm : ops[i]? with
  | none => isFalse (by rintro ⟨op, hop, _⟩; rw [hop] at hm; exact Option.noConfusion hm)
  | some op =>
    if hd : (step (stateAt s ops i) op).2 = .scheduled t then
      isTrue ⟨op, hm, hd⟩
    else
      isFalse (by
        rintro ⟨op', hop', hr⟩
        rw [hop'] at hm
        cases Option.some.inj hm
        exact hd hr)

/-! ## Bounded weak fairness -/

/-- **Bounded ready-fairness** with window `k`: every task that is runnable
    at some step is scheduled within `k` further steps.  This is the
    explicit scheduling assumption; it is a property of the *operation
    sequence* (the scheduler's choices), not of `WellFormed`. -/
def BoundedReadyFair (k : Nat) (s : RuntimeState) (ops : List RuntimeOp) : Prop :=
  ∀ i t, runnableAtStep s ops i t →
    ∃ j, i ≤ j ∧ j ≤ i + k ∧ scheduledAtStep s ops j t

/-! ## Conditional progress theorems

    These are deliberately close to tautological: their value is making
    the scheduling assumption explicit and reusable, per RFC 046. -/

/-- Under bounded ready-fairness, a task runnable at step `i` is scheduled
    within `k` steps.  Conditional on the explicit `BoundedReadyFair`
    assumption — no unconditional liveness is claimed. -/
theorem ready_eventually_scheduled_under_bounded_fairness
    {k : Nat} {s : RuntimeState} {ops : List RuntimeOp} {i : Nat} {t : TaskId}
    (hfair : BoundedReadyFair k s ops)
    (hrun : runnableAtStep s ops i t) :
    ∃ j, i ≤ j ∧ j ≤ i + k ∧ scheduledAtStep s ops j t :=
  hfair i t hrun

/-! ## Driver-level bounded progress (unconditional, but local)

    The one genuinely unconditional progress fact: the head of `readyQ` is
    scheduled by the very next `schedule`, because the model's queue is
    FIFO.  No fairness assumption is needed for this local step. -/

/-- If nothing is running and `t` is the runnable head of `readyQ`, then a
    `schedule` op schedules exactly `t`.  This is the FIFO head-progress
    fact: the next scheduled task is always the current head. -/
theorem schedule_schedules_head
    {s : RuntimeState} {t : TaskId} {q : List TaskId}
    (hrun : s.running = none)
    (hq : s.readyQ = t :: q)
    (hrunnable : (s.taskState t).any TaskState.isRunnable) :
    (step s .schedule).2 = .scheduled t := by
  simp [step, hrun, hq, hrunnable]

/-- The FIFO consequence: a runnable head is scheduled *within one step*
    (the `BoundedReadyFair 0` witness for the head, with no assumption). -/
theorem head_scheduled_within_one
    {s : RuntimeState} {ops : List RuntimeOp} {t : TaskId} {q : List TaskId}
    {i : Nat}
    (hop : ops[i]? = some .schedule)
    (hrun : (stateAt s ops i).running = none)
    (hq : (stateAt s ops i).readyQ = t :: q)
    (hrunnable : ((stateAt s ops i).taskState t).any TaskState.isRunnable) :
    scheduledAtStep s ops i t :=
  ⟨.schedule, hop, schedule_schedules_head hrun hq hrunnable⟩

end Henret.Progress
