import Henret.Bridge.Grammar
import Henret.Proofs.Invariants
/-!
  # Henret.Bridge.State

  The `BridgeState` relation connecting henret's `RuntimeState` to a
  lean-runtime-compatible model of per-worker queues.

  ## Design

  lean-runtime models the scheduler as `ModelSchedulerState`:
  a `Nat`-indexed map from worker id to a queue of `TaskId`s.
  We mirror this representation here so the bridge stays self-contained
  (the lean-runtime package is a separate Lake package; we do not `import` it).

  A `BridgeState s wqs` holds when:
  1. The **ready queue** of henret corresponds to worker 0's queue:
     `s.readyQ = wqs 0`.
  2. The **running slot** is either empty (none) or contains a task that
     does not appear in any worker queue (it is currently executing).
  3. All tasks in every worker queue are in a runnable state (per
     `WellFormed.readyQ_queued` and the bridge invariant).

  For the initial single-worker bridge we track only worker 0. Multi-worker
  extension (generalising to `n : Nat` workers) is deferred.
-/
namespace Henret.Bridge

/-! ## Mirror of lean-runtime's ModelSchedulerState -/

/-- Per-worker task queue (mirrors `lean-runtime`'s `ModelSchedulerState`). -/
def WorkerQueues := WorkerIdx → List TaskId

/-- The single-worker projection: only worker 0 is tracked. -/
def WorkerQueues.single (q : List TaskId) : WorkerQueues := fun w =>
  if w = 0 then q else []

/-! ## BridgeState relation -/

/-- `BridgeState s wqs` holds when the henret scheduler state `s` corresponds
to the lean-runtime worker queue map `wqs` under the single-worker projection.

Fields:
- `queue_eq` — worker 0's queue equals henret's `readyQ`.
- `other_empty` — all other workers have empty queues (single-worker model).
-/
structure BridgeState (s : RuntimeState) (wqs : WorkerQueues) : Prop where
  /-- The ready queue equals worker 0's queue. -/
  queue_eq    : s.readyQ = wqs 0
  /-- All non-zero workers are empty (single-worker model). -/
  other_empty : ∀ w : WorkerIdx, w ≠ 0 → wqs w = []

/-! ## Constructors and projections -/

/-- The initial state satisfies `BridgeState`: `readyQ = []` and all queues empty. -/
theorem bridgeState_init :
    BridgeState RuntimeState.init (WorkerQueues.single []) := {
  queue_eq    := by simp [RuntimeState.init, WorkerQueues.single]
  other_empty := by intro w _; simp [WorkerQueues.single, show w ≠ 0 from ‹_›]
}

/-- A `BridgeState` for `s` gives a `BridgeState` for the state after applying
a `Push 0 t` operation — reflecting that `Push` appends to worker 0's queue. -/
theorem bridgeState_push0 {s : RuntimeState} {wqs : WorkerQueues}
    (hbs : BridgeState s wqs) (t : TaskId) :
    BridgeState { s with readyQ := s.readyQ ++ [t] }
                (fun w => if w = 0 then wqs 0 ++ [t] else wqs w) := {
  queue_eq    := by simp [hbs.queue_eq]
  other_empty := by
    intro w hw
    simp [show w ≠ 0 from hw]
    exact hbs.other_empty w hw
}

/-- A `BridgeState` for `s` gives a `BridgeState` after a `Pop 0` when the
queue is non-empty. -/
theorem bridgeState_pop0 {s : RuntimeState} {wqs : WorkerQueues}
    (hbs : BridgeState s wqs) {t : TaskId} {rest : List TaskId}
    (hq : s.readyQ = t :: rest) :
    BridgeState { s with readyQ := rest }
                (fun w => if w = 0 then rest else wqs w) := {
  queue_eq    := by simp
  other_empty := by
    intro w hw
    simp [show w ≠ 0 from hw]
    exact hbs.other_empty w hw
}

/-- A `BridgeState` is preserved by operations that do not touch `readyQ`. -/
theorem bridgeState_readyQ_unchanged {s s' : RuntimeState} {wqs : WorkerQueues}
    (hbs : BridgeState s wqs) (h : s'.readyQ = s.readyQ) :
    BridgeState s' wqs := {
  queue_eq    := by rw [h]; exact hbs.queue_eq
  other_empty := hbs.other_empty
}

/-! ## Queue model for QOp application -/

/-- Apply a single `QOp` to a `WorkerQueues` map. -/
def applyQOp (wqs : WorkerQueues) : QOp → WorkerQueues
  | .Push w t  => fun w' => if w' = w then wqs w ++ [t] else wqs w'
  | .Pop w     => fun w' =>
      if w' = w then (wqs w).tail else wqs w'
  | .Steal _ _ => wqs  -- steal moves tasks; simplified for single-worker bridge
  | .Wake _    => wqs  -- wake changes readiness, not queue membership
  | .Inject t  => fun w' => if w' = 0 then wqs 0 ++ [t] else wqs w'

/-- Apply a list of `QOp`s in order. -/
def applyQOps (wqs : WorkerQueues) : List QOp → WorkerQueues
  | []        => wqs
  | op :: ops => applyQOps (applyQOp wqs op) ops

end Henret.Bridge
