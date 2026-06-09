import Henret.Bridge.State
import Henret.Proofs
/-!
  # Henret.Bridge.Preservation  (RFC 035)
-/
namespace Henret.Bridge

/-- `BridgeState` is preserved by steps that don't touch `readyQ`. -/
theorem bridge_stable {s s' : RuntimeState} {wqs : WorkerQueues}
    (hbs : BridgeState s wqs) (h : s'.readyQ = s.readyQ) :
    BridgeState s' wqs :=
  { queue_eq := h.trans hbs.queue_eq, other_empty := hbs.other_empty }

/-- Every reachable state bridges to its own `readyQ`. -/
theorem reachable_bridge (ops : List RuntimeOp) :
    ∃ wqs : WorkerQueues, BridgeState (run RuntimeState.init ops) wqs :=
  ⟨WorkerQueues.single (run RuntimeState.init ops).readyQ,
    { queue_eq    := by simp [WorkerQueues.single]
      other_empty := fun w hw => by simp [WorkerQueues.single, hw] }⟩

private def pushWorker0 (wqs : WorkerQueues) (t : TaskId) : WorkerQueues :=
  fun w => if w = 0 then wqs 0 ++ [t] else wqs w

private theorem applyQOps_push0 (wqs : WorkerQueues) (t : TaskId) :
    applyQOps wqs [.Push 0 t] = pushWorker0 wqs t := by
  funext w; simp only [applyQOps, applyQOp, List.foldl, pushWorker0]

private theorem applyQOps_nil (wqs : WorkerQueues) : applyQOps wqs [] = wqs := rfl

private theorem applyQOps_wake_noop (wqs : WorkerQueues) (t : TaskId) :
    applyQOps wqs [.Wake t] = wqs := by
  simp only [applyQOps, applyQOp, List.foldl]

-- readyQ is invariant under complete (all branches return s.readyQ)
private theorem complete_rq (s : RuntimeState) (t : TaskId) :
    (step s (.complete t)).1.readyQ = s.readyQ := by
  simp only [step]
  by_cases h : s.running = some t
  · rw [if_pos h]; cases s.taskState t with
    | some st => cases st <;> simp | none => rfl
  · rw [if_neg h]

-- readyQ is invariant under receive (mailbox ops don't touch the queue)
private theorem receive_rq (s : RuntimeState) (t : TaskId) :
    (step s (.receive t)).1.readyQ = s.readyQ := by
  by_cases h1 : s.running = some t
  · cases h2 : s.taskState t with
    | some st => cases st with
      | running =>
        cases h3 : s.taskOwner t with
        | some a =>
          cases h4 : s.mailboxes a with
          | some mb =>
            cases h5 : mb.dequeue with
            | some p => simp [step, h1, h2, h3, h4, h5]
            | none   => simp [step, h1, h2, h3, h4, h5]
          | none => simp [step, h1, h2, h3, h4]
        | none => simp [step, h1, h2, h3]
      | new | ready | yielded | sleeping | completed | cancelled | waiting =>
        simp [step, h1, h2]
    | none => simp [step, h1, h2]
  · simp [step, h1]

-- readyQ is invariant under sleep
private theorem sleep_rq (s : RuntimeState) (t : TaskId) (d : Nat) :
    (step s (.sleep t d)).1.readyQ = s.readyQ := by
  simp only [step]
  by_cases h : s.running = some t
  · rw [if_pos h]; cases s.taskState t with
    | some st => cases st <;> simp | none => rfl
  · rw [if_neg h]

-- yield readyQ is unchanged when yield is invalid
private theorem yield_invalid_rq (s : RuntimeState) (t : TaskId)
    (h : s.running ≠ some t ∨ s.taskState t ≠ some .running) :
    (step s (.yield t)).1.readyQ = s.readyQ := by
  simp only [step]
  rcases h with h | h
  · rw [if_neg h]
  · by_cases hrt : s.running = some t
    · rw [if_pos hrt]; cases hts : s.taskState t with
      | some st => cases st with
        | running => simp [hts] at h
        | new | ready | yielded | sleeping | completed | cancelled | waiting => simp
      | none => rfl
    · rw [if_neg hrt]

-- wake readyQ is unchanged when wake is invalid
private theorem wake_invalid_rq (s : RuntimeState) (t : TaskId)
    (h : s.taskState t ≠ some .sleeping) :
    (step s (.wake t)).1.readyQ = s.readyQ := by
  cases hts : s.taskState t with
  | some st => cases st with
    | sleeping => exact absurd hts h
    | new | ready | running | yielded | completed | cancelled | waiting => simp [step, hts]
  | none => simp [step, hts]

/-- **Bridge for spawn**. -/
theorem bridge_spawn (s : RuntimeState) (a : ActorId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.spawn a)).1 (applyQOps wqs (toQOps s (.spawn a))) := by
  cases hts : s.taskState s.nextId with
  | some _ =>
    rw [toQOps_spawn_invalid _ _ (by simp [hts]), applyQOps_nil]
    exact bridge_stable hbs (by simp [step, hts])
  | none =>
    rw [toQOps_spawn_valid _ _ hts, applyQOps_push0]
    have hq : (step s (.spawn a)).1.readyQ = s.readyQ ++ [s.nextId] := by simp [step, hts]
    exact { queue_eq    := by simp [pushWorker0, hq, hbs.queue_eq]
            other_empty := fun w hw => by
              simp [pushWorker0, show w ≠ 0 from hw]; exact hbs.other_empty w hw }

/-- **Bridge for yield**. -/
theorem bridge_yield (s : RuntimeState) (t : TaskId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.yield t)).1 (applyQOps wqs (toQOps s (.yield t))) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | some st => cases st with
      | running =>
        rw [toQOps_yield_valid _ _ hrt hts, applyQOps_push0]
        have hq : (step s (.yield t)).1.readyQ = s.readyQ ++ [t] := by simp [step, hrt, hts]
        exact { queue_eq    := by simp [pushWorker0, hq, hbs.queue_eq]
                other_empty := fun w hw => by
                  simp [pushWorker0, show w ≠ 0 from hw]; exact hbs.other_empty w hw }
      | new | ready | yielded | sleeping | completed | cancelled | waiting =>
        rw [toQOps_yield_invalid _ _ (Or.inr (by simp [hts])), applyQOps_nil]
        exact bridge_stable hbs (yield_invalid_rq s t (Or.inr (by simp [hts])))
    | none =>
      rw [toQOps_yield_invalid _ _ (Or.inr (by simp [hts])), applyQOps_nil]
      exact bridge_stable hbs (yield_invalid_rq s t (Or.inr (by simp [hts])))
  · rw [toQOps_yield_invalid _ _ (Or.inl hrt), applyQOps_nil]
    exact bridge_stable hbs (yield_invalid_rq s t (Or.inl hrt))

/-- **Bridge for wake**. -/
theorem bridge_wake (s : RuntimeState) (t : TaskId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.wake t)).1 (applyQOps wqs (toQOps s (.wake t))) := by
  cases hts : s.taskState t with
  | some st => cases st with
    | sleeping =>
      rw [toQOps_wake_valid _ _ hts, applyQOps_push0]
      have hq : (step s (.wake t)).1.readyQ = s.readyQ ++ [t] := by simp [step, hts]
      exact { queue_eq    := by simp [pushWorker0, hq, hbs.queue_eq]
              other_empty := fun w hw => by
                simp [pushWorker0, show w ≠ 0 from hw]; exact hbs.other_empty w hw }
    | new | ready | running | yielded | completed | cancelled | waiting =>
      rw [toQOps_wake_invalid _ _ (by simp [hts]), applyQOps_nil]
      exact bridge_stable hbs (wake_invalid_rq s t (by simp [hts]))
  | none =>
    rw [toQOps_wake_invalid _ _ (by simp [hts]), applyQOps_nil]
    exact bridge_stable hbs (wake_invalid_rq s t (by simp [hts]))

/-- **Bridge for complete** (readyQ-stable). -/
theorem bridge_complete (s : RuntimeState) (t : TaskId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.complete t)).1 (applyQOps wqs (toQOps s (.complete t))) := by
  rw [toQOps_complete_nil, applyQOps_nil]; exact bridge_stable hbs (complete_rq s t)

/-- **Bridge for receive** (readyQ-stable). -/
theorem bridge_receive (s : RuntimeState) (t : TaskId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.receive t)).1 (applyQOps wqs (toQOps s (.receive t))) := by
  rw [toQOps_receive_nil, applyQOps_nil]; exact bridge_stable hbs (receive_rq s t)

/-- **Bridge for sleep** (readyQ-stable). -/
theorem bridge_sleep (s : RuntimeState) (t : TaskId) (d : Nat) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.sleep t d)).1 (applyQOps wqs (toQOps s (.sleep t d))) := by
  rw [toQOps_sleep_nil, applyQOps_nil]; exact bridge_stable hbs (sleep_rq s t d)

end Henret.Bridge
