import Henret.Bridge.Grammar
import Henret.Proofs.Invariants
/-!
  # Henret.Bridge.State  (RFC 035 skeleton; RFC 036 completion)

  The `BridgeState` relation connecting henret's `RuntimeState` to a
  lean-runtime-compatible model of per-worker queues, and the queue
  model that `toQOps` translation operates on.

  ## Design

  lean-runtime models the scheduler as a `Nat`-indexed map from worker id
  to a queue of `TaskId`s. We mirror this here so the bridge stays
  self-contained (the lean-runtime package is a separate Lake package).

  `BridgeState s wqs` holds when:
  - `s.readyQ = wqs 0`  (queue projection onto worker 0)
  - All other worker queues are empty (single-worker model)

  This is a **queue projection bridge**: it relates Henret's `readyQ` to
  worker 0's queue.  It does not relate the running slot, sleeping/waiting
  tasks, or actor semantics.  Multi-worker extension is deferred to RFC 043.
-/
namespace Henret.Bridge

/-! ## Mirror of lean-runtime's ModelSchedulerState -/

/-- Per-worker task queue (mirrors `lean-runtime`'s `ModelSchedulerState`). -/
def WorkerQueues := WorkerIdx → List TaskId

/-- The empty initial worker-queue map: all workers have empty queues. -/
def WorkerQueues.init : WorkerQueues := fun _ => []

/-- The single-worker projection: only worker 0 is set; others are empty. -/
def WorkerQueues.single (q : List TaskId) : WorkerQueues := fun w =>
  if w = 0 then q else []

/-! ## BridgeState relation -/

/-- `BridgeState s wqs` — henret's `readyQ` equals worker 0's queue under the
    single-worker projection.

    This is a **queue projection bridge** (RFC 036): it relates `readyQ` only.
    It does not claim fairness, native execution, or actor semantics. -/
structure BridgeState (s : RuntimeState) (wqs : WorkerQueues) : Prop where
  /-- The ready queue equals worker 0's queue. -/
  queue_eq    : s.readyQ = wqs 0
  /-- All non-zero workers are empty (single-worker model). -/
  other_empty : ∀ w : WorkerIdx, w ≠ 0 → wqs w = []

/-! ## Constructors and projections -/

/-- The initial state satisfies `BridgeState` against the empty worker queues. -/
theorem bridgeState_init :
    BridgeState RuntimeState.init WorkerQueues.init := {
  queue_eq    := by simp [RuntimeState.init, WorkerQueues.init]
  other_empty := by intro w _; simp [WorkerQueues.init]
}

/-- A `BridgeState` for `s` gives a `BridgeState` after a `Push 0 t`. -/
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

/-- A `BridgeState` for `s` gives a `BridgeState` after a `Filter 0 t`. -/
theorem bridgeState_filter0 {s : RuntimeState} {wqs : WorkerQueues}
    (hbs : BridgeState s wqs) (t : TaskId) :
    BridgeState { s with readyQ := s.readyQ.filter (· ≠ t) }
                (fun w => if w = 0 then (wqs 0).filter (· ≠ t) else wqs w) := {
  queue_eq    := by simp [hbs.queue_eq]
  other_empty := by
    intro w hw
    simp [show w ≠ 0 from hw]
    exact hbs.other_empty w hw
}

/-- `BridgeState` is preserved by operations that do not touch `readyQ`. -/
theorem bridgeState_readyQ_unchanged {s s' : RuntimeState} {wqs : WorkerQueues}
    (hbs : BridgeState s wqs) (h : s'.readyQ = s.readyQ) :
    BridgeState s' wqs := {
  queue_eq    := by rw [h]; exact hbs.queue_eq
  other_empty := hbs.other_empty
}

/-! ## Queue model for QOp application -/

/-- Apply a single `QOp` to a `WorkerQueues` map.

    `Wake`, `Steal`, and `Inject` are defined but are no-ops in the
    single-worker bridge (they are never emitted by `toQOps`). -/
def applyQOp (wqs : WorkerQueues) : QOp → WorkerQueues
  | .Push w t    => fun w' => if w' = w then wqs w ++ [t] else wqs w'
  | .Pop w       => fun w' => if w' = w then (wqs w).tail else wqs w'
  | .Filter w t  => fun w' => if w' = w then (wqs w).filter (· ≠ t) else wqs w'
  | .Steal _ _   => wqs   -- no-op in single-worker bridge
  | .Wake _      => wqs   -- not emitted by toQOps; semantically no-op
  | .Inject t    => fun w' => if w' = 0 then wqs 0 ++ [t] else wqs w'

/-- Apply a list of `QOp`s in order. -/
def applyQOps (wqs : WorkerQueues) : List QOp → WorkerQueues
  | []        => wqs
  | op :: ops => applyQOps (applyQOp wqs op) ops

/-- Thread `toQOps` through a sequence of operations, accumulating the
    translated `QOp` list.  State-dependent because `toQOps` reads the
    current scheduler state. -/
def toQOpsTrace (s : RuntimeState) : List RuntimeOp → List QOp
  | []        => []
  | op :: ops => toQOps s op ++ toQOpsTrace (step s op).1 ops

end Henret.Bridge
