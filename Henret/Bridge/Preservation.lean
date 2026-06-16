import Henret.Bridge.State
import Henret.Proofs
/-!
  # Henret.Bridge.Preservation  (RFC 036)

  Complete single-worker bridge preservation theorems.

  ## Coverage

  Every `RuntimeOp` has a bridge theorem of the form:

  ```
  bridge_<op> : BridgeState s wqs → WellFormed s →
    BridgeState (step s op).1 (applyQOps wqs (toQOps s op))
  ```

  Theorems that do not need `WellFormed` (readyQ-stable ops, spawn, yield,
  wake) omit the `hwf` hypothesis.

  ## Headline theorems

  - `bridge_step_single_worker` — single-step bridge for any `RuntimeOp`.
  - `bridge_run_tracks_single_worker` — trace-level bridge: running any
    sequence of ops from `init` tracks the queue projection.
  - `reachable_bridge` — existential form (kept for backward compatibility).
-/
namespace Henret.Bridge

/-! ## Stable helper: QOps that do not change readyQ -/

/-- `BridgeState` is preserved by steps that don't touch `readyQ`. -/
theorem bridge_stable {s s' : RuntimeState} {wqs : WorkerQueues}
    (hbs : BridgeState s wqs) (h : s'.readyQ = s.readyQ) :
    BridgeState s' wqs :=
  { queue_eq := h.trans hbs.queue_eq, other_empty := hbs.other_empty }

/-! ## applyQOps helper lemmas -/

private theorem applyQOps_nil (wqs : WorkerQueues) : applyQOps wqs [] = wqs := rfl

private theorem applyQOps_push0 (wqs : WorkerQueues) (t : TaskId) :
    applyQOps wqs [.Push 0 t] = fun w => if w = 0 then wqs 0 ++ [t] else wqs w := rfl

private theorem applyQOps_pop0 (wqs : WorkerQueues) :
    applyQOps wqs [.Pop 0] = fun w => if w = 0 then (wqs 0).tail else wqs w := rfl

private theorem applyQOps_filter0 (wqs : WorkerQueues) (t : TaskId) :
    applyQOps wqs [.Filter 0 t] = fun w => if w = 0 then (wqs 0).filter (· ≠ t) else wqs w := rfl

/-- Applying a list of `Push 0 u` ops for each `u` in a list appends the list to worker 0. -/
private theorem applyQOps_pushes0 (wqs : WorkerQueues) (ts : List TaskId) :
    applyQOps wqs (ts.map (fun u => .Push 0 u)) =
    (fun w => if w = 0 then wqs 0 ++ ts else wqs w) := by
  induction ts generalizing wqs with
  | nil =>
    funext w; by_cases h : w = 0 <;> simp [applyQOps, h]
  | cons t rest ih =>
    funext w
    simp only [List.map, applyQOps, applyQOp]
    -- Goal: applyQOps wqs' (rest.map ..) w = if w = 0 then wqs 0 ++ t :: rest else wqs w
    -- where wqs' := fun w' => if w' = 0 then wqs 0 ++ [t] else wqs w'
    rw [ih (fun w' => if w' = 0 then wqs 0 ++ [t] else wqs w')]
    by_cases hw : w = 0
    · simp [hw, List.append_assoc]
    · simp [hw]

-- Two focused lemmas for Filter-chain reasoning, used by bridge_cancelTree.
-- Proving the full function equality is avoided; proving the two field
-- obligations (at0, other) directly is simpler and sufficient.

/-- Applying a list of Filter ops at worker 0 = filtering worker 0 by (· ∉ ts). -/
private theorem applyQOps_filters0_at0 (wqs : WorkerQueues) (ts : List TaskId) :
    (applyQOps wqs (ts.map (.Filter 0 ·))) 0 = (wqs 0).filter (· ∉ ts) := by
  induction ts generalizing wqs with
  | nil =>
    simp only [List.map, applyQOps]
    -- (wqs 0).filter (fun x => decide (x ∉ [])) = wqs 0
    induction (wqs 0) with
    | nil => simp
    | cons a l ih =>
      simp only [List.filter_cons, List.mem_nil_iff, not_false_eq_true,
                 decide_eq_true_eq, ite_true]
      exact congrArg (a :: ·) ih
  | cons t rest ih =>
    simp only [List.map, applyQOps, applyQOp, ite_true]
    rw [ih (fun w' => if w' = 0 then (wqs 0).filter (· ≠ t) else wqs w')]
    simp only [ite_true, List.filter_filter]
    congr 1; funext x
    have h : (x ∉ rest ∧ x ≠ t) ↔ (x ∉ t :: rest) := by
      simp [List.mem_cons, not_or, and_comm]
    rw [← Bool.decide_and]
    exact decide_eq_decide.mpr h

/-- Applying Filter ops leaves non-zero workers unchanged. -/
private theorem applyQOps_filters0_other (wqs : WorkerQueues) (ts : List TaskId)
    {w : WorkerIdx} (hw : w ≠ 0) :
    (applyQOps wqs (ts.map (.Filter 0 ·))) w = wqs w := by
  induction ts generalizing wqs with
  | nil => simp [applyQOps]
  | cons t rest ih =>
    simp only [List.map, applyQOps, applyQOp, if_neg hw]
    exact (ih (fun w' => if w' = 0 then (wqs 0).filter (· ≠ t) else wqs w')).trans (by simp [hw])

-- readyQ is invariant under complete
private theorem complete_rq (s : RuntimeState) (t : TaskId) :
    (step s (.complete t)).1.readyQ = s.readyQ := by
  simp only [step]
  by_cases h : s.running = some t
  · rw [if_pos h]; cases s.taskState t with
    | some st => cases st <;> simp | none => rfl
  · rw [if_neg h]

-- readyQ is invariant under receive
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
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed | failed =>
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
        | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed | failed => simp
      | none => rfl
    · rw [if_neg hrt]

-- wake readyQ is unchanged when wake is invalid
private theorem wake_invalid_rq (s : RuntimeState) (t : TaskId)
    (h : s.taskState t ≠ some .sleeping) :
    (step s (.wake t)).1.readyQ = s.readyQ := by
  cases hts : s.taskState t with
  | some st => cases st with
    | sleeping => exact absurd hts h
    | new | ready | running | yielded | completed | cancelled | waiting | waitingTimed | failed => simp [step, hts]
  | none => simp [step, hts]

-- cancel valid: readyQ filtered
private theorem cancel_valid_rq (s : RuntimeState) (t : TaskId) (st : TaskState)
    (hts : s.taskState t = some st) (hnt : ¬st.isTerminal) :
    (step s (.cancel t)).1.readyQ = s.readyQ.filter (· ≠ t) := by
  simp [step, hts, hnt]

-- cancel invalid (terminal): readyQ unchanged
private theorem cancel_invalid_rq (s : RuntimeState) (t : TaskId)
    (h : s.taskState t = none ∨ ∃ st, s.taskState t = some st ∧ st.isTerminal) :
    (step s (.cancel t)).1.readyQ = s.readyQ := by
  rcases h with h | ⟨st, hts, ht⟩
  · simp [step, h]
  · simp [step, hts, ht]

-- schedule valid: readyQ pops head
private theorem schedule_valid_rq (s : RuntimeState) (t : TaskId) (rest : List TaskId)
    (hr : s.running = none) (hq : s.readyQ = t :: rest)
    (hrun : (s.taskState t).any TaskState.isRunnable = true) :
    (step s .schedule).1.readyQ = rest := by
  simp [step, hr, hq, hrun]

-- send valid with waiter: readyQ gets w pushed
private theorem send_valid_waiter_rq (s : RuntimeState) (t b w : TaskId) (m : Message)
    (oa : ActorId) (mb : Mailbox) (ws : List TaskId)
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some oa) (hmb : s.mailboxes b = some mb)
    (hac : s.actorStatus b ≠ .closed)
    (hwt : s.mailboxWaiters b = w :: ws)
    (hfull : s.mailboxFull b mb = false) :
    (step s (.send t b m)).1.readyQ = s.readyQ ++ [w] := by
  simp [step, hac, hrt, hts, how, hmb, hwt, hfull]

-- send valid without any waiter: readyQ unchanged
private theorem send_valid_no_waiter_rq (s : RuntimeState) (t b : TaskId) (m : Message)
    (oa : ActorId) (mb : Mailbox)
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some oa) (hmb : s.mailboxes b = some mb)
    (hac : s.actorStatus b ≠ .closed)
    (hwt : s.mailboxWaiters b = []) (htw : s.timedMailboxWaiters b = [])
    (hfull : s.mailboxFull b mb = false) :
    (step s (.send t b m)).1.readyQ = s.readyQ := by
  simp [step, hac, hrt, hts, how, hmb, hwt, htw, hfull]

-- send valid with timed waiter: readyQ gets w pushed
private theorem send_valid_timed_waiter_rq (s : RuntimeState) (t b w : TaskId) (m : Message)
    (oa : ActorId) (mb : Mailbox) (ws : List TaskId)
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some oa) (hmb : s.mailboxes b = some mb)
    (hac : s.actorStatus b ≠ .closed)
    (hwt : s.mailboxWaiters b = []) (htws : s.timedMailboxWaiters b = w :: ws)
    (hfull : s.mailboxFull b mb = false) :
    (step s (.send t b m)).1.readyQ = s.readyQ ++ [w] := by
  simp [step, hac, hrt, hts, how, hmb, hwt, htws, hfull]

-- inject valid with waiter: readyQ gets w pushed
private theorem inject_valid_waiter_rq (s : RuntimeState) (a w : ActorId) (m : Message)
    (mb : Mailbox) (ws : List TaskId)
    (hrs : s.runtimeStatus = .running) (hac : s.actorStatus a ≠ .closed)
    (hmb : s.mailboxes a = some mb) (hwt : s.mailboxWaiters a = w :: ws)
    (hfull : s.mailboxFull a mb = false) :
    (step s (.inject a m)).1.readyQ = s.readyQ ++ [w] := by
  simp [step, hrs, hac, hmb, hwt, hfull]

-- inject valid without any waiter: readyQ unchanged
private theorem inject_valid_no_waiter_rq (s : RuntimeState) (a : ActorId) (m : Message)
    (mb : Mailbox) (hrs : s.runtimeStatus = .running) (hac : s.actorStatus a ≠ .closed)
    (hmb : s.mailboxes a = some mb)
    (hwt : s.mailboxWaiters a = []) (htw : s.timedMailboxWaiters a = [])
    (hfull : s.mailboxFull a mb = false) :
    (step s (.inject a m)).1.readyQ = s.readyQ := by
  simp [step, hrs, hac, hmb, hwt, htw, hfull]

-- inject valid with timed waiter: readyQ gets w pushed
private theorem inject_valid_timed_waiter_rq (s : RuntimeState) (a w : ActorId) (m : Message)
    (mb : Mailbox) (ws : List TaskId)
    (hrs : s.runtimeStatus = .running) (hac : s.actorStatus a ≠ .closed)
    (hmb : s.mailboxes a = some mb)
    (hwt : s.mailboxWaiters a = []) (htws : s.timedMailboxWaiters a = w :: ws)
    (hfull : s.mailboxFull a mb = false) :
    (step s (.inject a m)).1.readyQ = s.readyQ ++ [w] := by
  simp [step, hrs, hac, hmb, hwt, htws, hfull]

-- tick valid: readyQ gets woken appended
private theorem tick_valid_rq (s : RuntimeState) (t : Nat) (h : s.now ≤ t) :
    let woken := ((Timer.expired s.timers t).map TimerEntry.task)
    (step s (.tick t)).1.readyQ = s.readyQ ++
      (woken.filter (fun u => s.taskState u = some .sleeping) ++
       woken.filter (fun u => s.taskState u = some .waitingTimed)) := by
  simp [step, h]

/-! ## Per-operation bridge theorems -/

/-- **Bridge for spawn** (RFC 035). -/
theorem bridge_spawn (s : RuntimeState) (a : ActorId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.spawn a)).1 (applyQOps wqs (toQOps s (.spawn a))) := by
  by_cases hrs : s.runtimeStatus = .running
  · cases hts : s.taskState s.nextId with
    | some _ =>
      rw [toQOps_spawn_invalid _ _ (by simp [hts]), applyQOps_nil]
      exact bridge_stable hbs (by simp [step, hrs, hts])
    | none =>
      rw [toQOps_spawn_valid _ _ hrs hts, applyQOps_push0]
      have hq : (step s (.spawn a)).1.readyQ = s.readyQ ++ [s.nextId] := by simp [step, hrs, hts]
      exact { queue_eq    := by simp [hq, hbs.queue_eq]
              other_empty := fun w hw => by
                simp [show w ≠ 0 from hw]; exact hbs.other_empty w hw }
  · rw [show toQOps s (.spawn a) = [] by simp [toQOps, hrs], applyQOps_nil]
    exact bridge_stable hbs (by simp [step, hrs])

/-- **Bridge for spawnChild** (RFC 036). -/
theorem bridge_spawnChild (s : RuntimeState) (t : TaskId) (a : ActorId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.spawnChild t a)).1 (applyQOps wqs (toQOps s (.spawnChild t a))) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | some st => cases st with
      | running =>
        cases how : s.taskOwner t with
        | some _ =>
          cases hfresh : s.taskState s.nextId with
          | none =>
            rw [toQOps_spawnChild_valid _ _ _ _ hrt hts how hfresh, applyQOps_push0]
            have hq : (step s (.spawnChild t a)).1.readyQ = s.readyQ ++ [s.nextId] := by
              simp [step, hrt, hts, how, hfresh]
            exact { queue_eq    := by simp [hq, hbs.queue_eq]
                    other_empty := fun w hw => by
                      simp [show w ≠ 0 from hw]; exact hbs.other_empty w hw }
          | some _ =>
            rw [show toQOps s (.spawnChild t a) = [] by simp [toQOps, hrt, hts, how, hfresh],
                applyQOps_nil]
            exact bridge_stable hbs (by simp [step, hrt, hts, how, hfresh])
        | none =>
          rw [show toQOps s (.spawnChild t a) = [] by simp [toQOps, hrt, hts, how], applyQOps_nil]
          exact bridge_stable hbs (by simp [step, hrt, hts, how])
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed | failed =>
        rw [show toQOps s (.spawnChild t a) = [] by simp [toQOps, hrt, hts], applyQOps_nil]
        exact bridge_stable hbs (by simp [step, hrt, hts])
    | none =>
      rw [show toQOps s (.spawnChild t a) = [] by simp [toQOps, hrt, hts], applyQOps_nil]
      exact bridge_stable hbs (by simp [step, hrt, hts])
  · rw [show toQOps s (.spawnChild t a) = [] by simp [toQOps, hrt], applyQOps_nil]
    exact bridge_stable hbs (by simp [step, hrt])

/-- **Bridge for schedule** (RFC 036). -/
theorem bridge_schedule (s : RuntimeState) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s .schedule).1 (applyQOps wqs (toQOps s .schedule)) := by
  match hr : s.running, hq : s.readyQ with
  | none, t :: rest =>
    cases hrun : (s.taskState t).any TaskState.isRunnable with
    | true =>
      rw [toQOps_schedule_nonempty _ _ _ hr hq hrun, applyQOps_pop0]
      have hrq : (step s .schedule).1.readyQ = rest := schedule_valid_rq s t rest hr hq hrun
      have hwq0 : wqs 0 = t :: rest := by rw [← hbs.queue_eq]; exact hq
      exact { queue_eq    := by simp [hrq, hwq0]
              other_empty := fun w hw => by
                simp [show w ≠ 0 from hw]; exact hbs.other_empty w hw }
    | false =>
      rw [show toQOps s .schedule = [] by simp [toQOps, hr, hq, hrun], applyQOps_nil]
      exact bridge_stable hbs (by simp [step, hr, hq, hrun])
  | none, [] =>
    rw [toQOps_schedule_empty _ hq, applyQOps_nil]
    exact bridge_stable hbs (by simp [step, hr, hq])
  | some t, _ =>
    rw [show toQOps s .schedule = [] by simp [toQOps, hr], applyQOps_nil]
    exact bridge_stable hbs (by simp [step, hr])

/-- **Bridge for yield** (RFC 035). -/
theorem bridge_yield (s : RuntimeState) (t : TaskId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.yield t)).1 (applyQOps wqs (toQOps s (.yield t))) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | some st => cases st with
      | running =>
        rw [toQOps_yield_valid _ _ hrt hts, applyQOps_push0]
        have hq : (step s (.yield t)).1.readyQ = s.readyQ ++ [t] := by simp [step, hrt, hts]
        exact { queue_eq    := by simp [hq, hbs.queue_eq]
                other_empty := fun w hw => by
                  simp [show w ≠ 0 from hw]; exact hbs.other_empty w hw }
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed | failed =>
        rw [toQOps_yield_invalid _ _ (Or.inr (by simp [hts])), applyQOps_nil]
        exact bridge_stable hbs (yield_invalid_rq s t (Or.inr (by simp [hts])))
    | none =>
      rw [toQOps_yield_invalid _ _ (Or.inr (by simp [hts])), applyQOps_nil]
      exact bridge_stable hbs (yield_invalid_rq s t (Or.inr (by simp [hts])))
  · rw [toQOps_yield_invalid _ _ (Or.inl hrt), applyQOps_nil]
    exact bridge_stable hbs (yield_invalid_rq s t (Or.inl hrt))

/-- **Bridge for wake** (RFC 035). -/
theorem bridge_wake (s : RuntimeState) (t : TaskId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.wake t)).1 (applyQOps wqs (toQOps s (.wake t))) := by
  cases hts : s.taskState t with
  | some st => cases st with
    | sleeping =>
      rw [toQOps_wake_valid _ _ hts, applyQOps_push0]
      have hq : (step s (.wake t)).1.readyQ = s.readyQ ++ [t] := by simp [step, hts]
      exact { queue_eq    := by simp [hq, hbs.queue_eq]
              other_empty := fun w hw => by
                simp [show w ≠ 0 from hw]; exact hbs.other_empty w hw }
    | new | ready | running | yielded | completed | cancelled | waiting | waitingTimed | failed =>
      rw [toQOps_wake_invalid _ _ (by simp [hts]), applyQOps_nil]
      exact bridge_stable hbs (wake_invalid_rq s t (by simp [hts]))
  | none =>
    rw [toQOps_wake_invalid _ _ (by simp [hts]), applyQOps_nil]
    exact bridge_stable hbs (wake_invalid_rq s t (by simp [hts]))

/-- **Bridge for cancel** (RFC 036).  Uses `WellFormed.readyQ_nodup` to confirm
    that filtering is well-defined (though the proof doesn't need nodup directly,
    `WellFormed` confirms the task list is well-structured). -/
theorem bridge_cancel (s : RuntimeState) (t : TaskId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.cancel t)).1 (applyQOps wqs (toQOps s (.cancel t))) := by
  cases hts : s.taskState t with
  | none =>
    rw [toQOps_cancel_invalid_unspawned _ _ hts, applyQOps_nil]
    exact bridge_stable hbs (cancel_invalid_rq s t (Or.inl hts))
  | some st =>
    by_cases hterm : st.isTerminal
    · rw [toQOps_cancel_invalid_terminal _ _ _ hts hterm, applyQOps_nil]
      exact bridge_stable hbs (cancel_invalid_rq s t (Or.inr ⟨st, hts, hterm⟩))
    · rw [toQOps_cancel_valid _ _ _ hts hterm, applyQOps_filter0]
      have hrq := cancel_valid_rq s t st hts hterm
      exact { queue_eq    := by simp [hrq, hbs.queue_eq]
              other_empty := fun w hw => by
                simp [show w ≠ 0 from hw]; exact hbs.other_empty w hw }

/-- **Bridge for complete** (readyQ-stable). -/
theorem bridge_complete (s : RuntimeState) (t : TaskId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.complete t)).1 (applyQOps wqs (toQOps s (.complete t))) := by
  rw [toQOps_complete_nil, applyQOps_nil]; exact bridge_stable hbs (complete_rq s t)

/-- **Bridge for receive** (readyQ-stable: parking does not alter `readyQ` since
    the running task is not in `readyQ` per `WellFormed.running_not_in_readyQ`). -/
theorem bridge_receive (s : RuntimeState) (t : TaskId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.receive t)).1 (applyQOps wqs (toQOps s (.receive t))) := by
  rw [toQOps_receive_nil, applyQOps_nil]; exact bridge_stable hbs (receive_rq s t)

/-- **Bridge for sleep** (readyQ-stable). -/
theorem bridge_sleep (s : RuntimeState) (t : TaskId) (d : Nat) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.sleep t d)).1 (applyQOps wqs (toQOps s (.sleep t d))) := by
  rw [toQOps_sleep_nil, applyQOps_nil]; exact bridge_stable hbs (sleep_rq s t d)

/-- **Bridge for send** (RFC 036).  Guard-compatible: only emits `Push 0 w`
    when the step is valid and wakes a waiter. -/
theorem bridge_send (s : RuntimeState) (t b : TaskId) (m : Message) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.send t b m)).1 (applyQOps wqs (toQOps s (.send t b m))) := by
  by_cases hcl : s.actorStatus b = .closed
  · rw [show toQOps s (.send t b m) = [] by simp [toQOps, hcl], applyQOps_nil]
    exact bridge_stable hbs (by simp [step, hcl])
  · by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | some st => cases st with
        | running =>
          cases how : s.taskOwner t with
          | some oa =>
            cases hmb : s.mailboxes b with
            | some mb =>
              by_cases hfull : s.mailboxFull b mb = true
              · -- Full mailbox: backpressured no-op; toQOps emits [] (RFC 056)
                rw [show toQOps s (.send t b m) = [] by
                  simp [toQOps, hcl, hrt, hts, how, hmb, hfull], applyQOps_nil]
                exact bridge_stable hbs (by simp [step, hcl, hrt, hts, how, hmb, hfull])
              simp only [Bool.not_eq_true] at hfull
              cases hwt : s.mailboxWaiters b with
              | nil =>
                cases htw : s.timedMailboxWaiters b with
                | nil =>
                  rw [toQOps_send_valid_no_waiter _ _ _ _ oa mb hrt hts how hmb hcl hwt htw, applyQOps_nil]
                  exact bridge_stable hbs (send_valid_no_waiter_rq s t b m oa mb hrt hts how hmb hcl hwt htw hfull)
                | cons w ws =>
                  rw [toQOps_send_valid_timed_waiter _ _ _ w _ oa mb ws hrt hts how hmb hcl hwt htw hfull, applyQOps_push0]
                  have hrq := send_valid_timed_waiter_rq s t b w m oa mb ws hrt hts how hmb hcl hwt htw hfull
                  exact { queue_eq    := by simp [hrq, hbs.queue_eq]
                          other_empty := fun w' hw' => by
                            simp [show w' ≠ 0 from hw']; exact hbs.other_empty w' hw' }
              | cons w ws =>
                rw [toQOps_send_valid_waiter _ _ _ w _ oa mb ws hrt hts how hmb hcl hwt hfull, applyQOps_push0]
                have hrq := send_valid_waiter_rq s t b w m oa mb ws hrt hts how hmb hcl hwt hfull
                exact { queue_eq    := by simp [hrq, hbs.queue_eq]
                        other_empty := fun w' hw' => by
                          simp [show w' ≠ 0 from hw']; exact hbs.other_empty w' hw' }
            | none =>
              rw [show toQOps s (.send t b m) = [] by simp [toQOps, hcl, hrt, hts, how, hmb],
                  applyQOps_nil]
              exact bridge_stable hbs (by simp [step, hcl, hrt, hts, how, hmb])
          | none =>
            rw [show toQOps s (.send t b m) = [] by simp [toQOps, hcl, hrt, hts, how], applyQOps_nil]
            exact bridge_stable hbs (by simp [step, hcl, hrt, hts, how])
        | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed | failed =>
          rw [show toQOps s (.send t b m) = [] by simp [toQOps, hcl, hrt, hts], applyQOps_nil]
          exact bridge_stable hbs (by simp [step, hcl, hrt, hts])
      | none =>
        rw [show toQOps s (.send t b m) = [] by simp [toQOps, hcl, hrt, hts], applyQOps_nil]
        exact bridge_stable hbs (by simp [step, hcl, hrt, hts])
    · rw [show toQOps s (.send t b m) = [] by simp [toQOps, hcl, hrt], applyQOps_nil]
      exact bridge_stable hbs (by simp [step, hcl, hrt])

/-- **Bridge for inject** (RFC 036). -/
theorem bridge_inject (s : RuntimeState) (a : ActorId) (m : Message) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.inject a m)).1 (applyQOps wqs (toQOps s (.inject a m))) := by
  by_cases hg : s.runtimeStatus ≠ .running ∨ s.actorStatus a = .closed
  · rw [show toQOps s (.inject a m) = [] by simp [toQOps, hg], applyQOps_nil]
    exact bridge_stable hbs (by simp [step, hg])
  · obtain ⟨hrs0, hac⟩ := not_or.mp hg
    have hrs : s.runtimeStatus = .running := Decidable.of_not_not hrs0
    cases hmb : s.mailboxes a with
    | none =>
      rw [show toQOps s (.inject a m) = [] by simp [toQOps, hg, hmb], applyQOps_nil]
      exact bridge_stable hbs (by simp [step, hg, hmb])
    | some mb =>
      by_cases hfull : s.mailboxFull a mb = true
      · -- Full mailbox: backpressured no-op; toQOps emits [] (RFC 056)
        rw [show toQOps s (.inject a m) = [] by simp [toQOps, hg, hmb, hfull], applyQOps_nil]
        exact bridge_stable hbs (by simp [step, hg, hmb, hfull])
      simp only [Bool.not_eq_true] at hfull
      cases hwt : s.mailboxWaiters a with
      | nil =>
        cases htw : s.timedMailboxWaiters a with
        | nil =>
          rw [toQOps_inject_valid_no_waiter s a m mb hrs hac hwt hmb htw, applyQOps_nil]
          exact bridge_stable hbs (inject_valid_no_waiter_rq s a m mb hrs hac hmb hwt htw hfull)
        | cons w ws =>
          rw [toQOps_inject_valid_timed_waiter s a w m mb ws hrs hac hmb hwt htw hfull, applyQOps_push0]
          have hrq := inject_valid_timed_waiter_rq s a w m mb ws hrs hac hmb hwt htw hfull
          exact { queue_eq    := by simp [hrq, hbs.queue_eq]
                  other_empty := fun w' hw' => by
                    simp [show w' ≠ 0 from hw']; exact hbs.other_empty w' hw' }
      | cons w ws =>
        rw [toQOps_inject_valid_waiter s a w m mb ws hrs hac hmb hwt hfull, applyQOps_push0]
        have hrq := inject_valid_waiter_rq s a w m mb ws hrs hac hmb hwt hfull
        exact { queue_eq    := by simp [hrq, hbs.queue_eq]
                other_empty := fun w' hw' => by
                  simp [show w' ≠ 0 from hw']; exact hbs.other_empty w' hw' }

/-- **Bridge for tick** (RFC 036).  Uses tick argument `t`, not `s.now`.
    Emits `Push 0 u` for each task woken by the tick. -/
theorem bridge_tick (s : RuntimeState) (t : Nat) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.tick t)).1 (applyQOps wqs (toQOps s (.tick t))) := by
  by_cases ht : s.now ≤ t
  · have hrq := tick_valid_rq s t ht
    let expiredTasks := (Timer.expired s.timers t).map TimerEntry.task
    rw [toQOps_tick_valid s t ht, applyQOps_pushes0]
    exact { queue_eq    := by simp [hrq, hbs.queue_eq, expiredTasks]
            other_empty := fun w hw => by
              simp [show w ≠ 0 from hw]; exact hbs.other_empty w hw }
  · rw [toQOps_tick_invalid _ _ ht, applyQOps_nil]
    exact bridge_stable hbs (by simp [step, ht])

/-! ## Unified single-step bridge theorem -/

/-- **Bridge for cancelTree** (RFC 039). Emits Filter ops for each cancelled task;
    their combined effect matches `applyCancelTree`'s `readyQ` filter. -/
theorem bridge_cancelTree (s : RuntimeState) (root : TaskId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.cancelTree root)).1
                (applyQOps wqs (toQOps s (.cancelTree root))) := by
  rw [toQOps_cancelTree]
  have hrq : (step s (.cancelTree root)).1.readyQ =
             s.readyQ.filter (· ∉ descendantsOf s root) := by
    simp [step, applyCancelTree]
  exact { queue_eq    := by
            rw [hrq, hbs.queue_eq, ← applyQOps_filters0_at0]
          other_empty := fun w hw => by
            rw [applyQOps_filters0_other _ _ hw]
            exact hbs.other_empty w hw }

/-- **Bridge for fail** (RFC 049). Mirrors `bridge_cancel`: a non-terminal
    task is filtered from the ready queue. -/
theorem bridge_fail (s : RuntimeState) (t : TaskId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.fail t)).1 (applyQOps wqs (toQOps s (.fail t))) := by
  cases hts : s.taskState t with
  | none =>
    rw [show toQOps s (.fail t) = [] by simp [toQOps, hts], applyQOps_nil]
    exact bridge_stable hbs (by simp [step, hts])
  | some st =>
    by_cases hterm : st.isTerminal
    · rw [show toQOps s (.fail t) = [] by simp [toQOps, hts, hterm], applyQOps_nil]
      exact bridge_stable hbs (by simp [step, hts, hterm])
    · rw [show toQOps s (.fail t) = [.Filter 0 t] by simp [toQOps, hts, hterm], applyQOps_filter0]
      have hrq : (step s (.fail t)).1.readyQ = s.readyQ.filter (· ≠ t) := by
        simp [step, hts, hterm]
      exact { queue_eq    := by simp [hrq, hbs.queue_eq]
              other_empty := fun w hw => by
                simp [show w ≠ 0 from hw]; exact hbs.other_empty w hw }

/-- **Bridge for restartOne** (RFC 049). Mirrors `bridge_spawnChild`: a fresh
    replacement task is pushed to worker 0. -/
theorem bridge_restartOne (s : RuntimeState) (t failedChild : TaskId) (a : ActorId)
    (wqs : WorkerQueues) (hbs : BridgeState s wqs) :
    BridgeState (step s (.restartOne t failedChild a)).1
                (applyQOps wqs (toQOps s (.restartOne t failedChild a))) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | some st => cases st with
      | running =>
        by_cases hpar : s.taskParent failedChild = some t
        · cases hfc : s.taskState failedChild with
          | some stf => cases stf with
            | failed =>
              cases hfresh : s.taskState s.nextId with
              | none =>
                rw [show toQOps s (.restartOne t failedChild a) = [.Push 0 s.nextId] by
                      simp [toQOps, hrt, hts, hpar, hfc, hfresh], applyQOps_push0]
                have hq : (step s (.restartOne t failedChild a)).1.readyQ = s.readyQ ++ [s.nextId] := by
                  simp [step, hrt, hts, hpar, hfc, hfresh]
                exact { queue_eq    := by simp [hq, hbs.queue_eq]
                        other_empty := fun w hw => by
                          simp [show w ≠ 0 from hw]; exact hbs.other_empty w hw }
              | some _ =>
                rw [show toQOps s (.restartOne t failedChild a) = [] by
                      simp [toQOps, hrt, hts, hpar, hfc, hfresh], applyQOps_nil]
                exact bridge_stable hbs (by simp [step, hrt, hts, hpar, hfc, hfresh])
            | new | ready | running | yielded | sleeping | completed | cancelled | waiting | waitingTimed =>
              rw [show toQOps s (.restartOne t failedChild a) = [] by
                    simp [toQOps, hrt, hts, hpar, hfc], applyQOps_nil]
              exact bridge_stable hbs (by simp [step, hrt, hts, hpar, hfc])
          | none =>
            rw [show toQOps s (.restartOne t failedChild a) = [] by
                  simp [toQOps, hrt, hts, hpar, hfc], applyQOps_nil]
            exact bridge_stable hbs (by simp [step, hrt, hts, hpar, hfc])
        · rw [show toQOps s (.restartOne t failedChild a) = [] by
                simp [toQOps, hrt, hts, hpar], applyQOps_nil]
          exact bridge_stable hbs (by simp [step, hrt, hts, hpar])
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed | failed =>
        rw [show toQOps s (.restartOne t failedChild a) = [] by
              simp [toQOps, hrt, hts], applyQOps_nil]
        exact bridge_stable hbs (by simp [step, hrt, hts])
    | none =>
      rw [show toQOps s (.restartOne t failedChild a) = [] by
            simp [toQOps, hrt, hts], applyQOps_nil]
      exact bridge_stable hbs (by simp [step, hrt, hts])
  · rw [show toQOps s (.restartOne t failedChild a) = [] by
          simp [toQOps, hrt], applyQOps_nil]
    exact bridge_stable hbs (by simp [step, hrt])

/-- **Bridge for closeActor** (RFC 055).  `toQOps = []` and `readyQ` is
    unchanged, so the bridge is stable. -/
theorem bridge_closeActor (s : RuntimeState) (a : ActorId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.closeActor a)).1 (applyQOps wqs (toQOps s (.closeActor a))) := by
  rw [show toQOps s (.closeActor a) = [] from rfl, applyQOps_nil]
  exact bridge_stable hbs (by simp only [step]; split <;> rfl)

/-- **Bridge for shutdown** (RFC 055). -/
theorem bridge_shutdown (s : RuntimeState) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s .shutdown).1 (applyQOps wqs (toQOps s .shutdown)) := by
  rw [show toQOps s .shutdown = [] from rfl, applyQOps_nil]
  exact bridge_stable hbs rfl

/-- **Bridge for stopWhenIdle** (RFC 055). -/
theorem bridge_stopWhenIdle (s : RuntimeState) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s .stopWhenIdle).1 (applyQOps wqs (toQOps s .stopWhenIdle)) := by
  rw [show toQOps s .stopWhenIdle = [] from rfl, applyQOps_nil]
  exact bridge_stable hbs (by simp only [step]; split <;> rfl)

/-- **Bridge for stopWhenDrained** (RFC 087). -/
theorem bridge_stopWhenDrained (s : RuntimeState) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s .stopWhenDrained).1 (applyQOps wqs (toQOps s .stopWhenDrained)) := by
  rw [show toQOps s .stopWhenDrained = [] from rfl, applyQOps_nil]
  exact bridge_stable hbs (by simp only [step]; split <;> rfl)

/-- **`bridge_acquireActor`** (RFC 091) — actor-owned acquisition changes the
    resource ledger but never a worker queue, so the queue-projection bridge is
    stable (`toQOps = []`). Like `closeActor`, this confirms the bridge tracks
    queues, not full state. -/
theorem bridge_acquireActor (s : RuntimeState) (a : ActorId) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s (.acquireActor a)).1 (applyQOps wqs (toQOps s (.acquireActor a))) := by
  rw [show toQOps s (.acquireActor a) = [] from rfl, applyQOps_nil]
  apply bridge_stable hbs
  simp only [step]; (repeat' split) <;> rfl

/-- **`bridge_step_single_worker`** — For any `RuntimeOp`, if `BridgeState` holds
    before the step, it holds after, with the translated queue effects applied.
    This is the central single-worker bridge theorem (RFC 036). -/
theorem bridge_step_single_worker (s : RuntimeState) (op : RuntimeOp) (wqs : WorkerQueues)
    (hbs : BridgeState s wqs) :
    BridgeState (step s op).1 (applyQOps wqs (toQOps s op)) := by
  match op with
  | .spawn a         => exact bridge_spawn s a wqs hbs
  | .spawnChild t a  => exact bridge_spawnChild s t a wqs hbs
  | .schedule        => exact bridge_schedule s wqs hbs
  | .yield t         => exact bridge_yield s t wqs hbs
  | .wake t          => exact bridge_wake s t wqs hbs
  | .cancel t        => exact bridge_cancel s t wqs hbs
  | .complete t      => exact bridge_complete s t wqs hbs
  | .receive t       => exact bridge_receive s t wqs hbs
  | .sleep t d       => exact bridge_sleep s t d wqs hbs
  | .send t b m      => exact bridge_send s t b m wqs hbs
  | .inject a m      => exact bridge_inject s a m wqs hbs
  | .tick t          => exact bridge_tick s t wqs hbs
  | .cancelTree root => exact bridge_cancelTree s root wqs hbs
  | .fail t          => exact bridge_fail s t wqs hbs
  | .restartOne p c a => exact bridge_restartOne s p c a wqs hbs
  | .closeActor a    => exact bridge_closeActor s a wqs hbs
  | .shutdown        => exact bridge_shutdown s wqs hbs
  | .stopWhenIdle    => exact bridge_stopWhenIdle s wqs hbs
  | .stopWhenDrained => exact bridge_stopWhenDrained s wqs hbs
  | .receiveUntil t d =>
    rw [show toQOps s (.receiveUntil t d) = [] from by simp [toQOps], applyQOps_nil]
    apply bridge_stable hbs
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;> (try split) <;> simp
  | .receiveByOccurrence t occ =>
    rw [show toQOps s (.receiveByOccurrence t occ) = [] from by simp [toQOps], applyQOps_nil]
    apply bridge_stable hbs
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;> simp
  | .receiveFrom t src =>
    rw [show toQOps s (.receiveFrom t src) = [] from by simp [toQOps], applyQOps_nil]
    apply bridge_stable hbs
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> (try split) <;> simp
  | .acquire t =>
    rw [show toQOps s (.acquire t) = [] from rfl, applyQOps_nil]
    apply bridge_stable hbs
    simp only [step]; (repeat' split) <;> rfl
  | .acquireActor a => exact bridge_acquireActor s a wqs hbs
  | .release t r =>
    rw [show toQOps s (.release t r) = [] from rfl, applyQOps_nil]
    apply bridge_stable hbs
    simp only [step]; (repeat' split) <;> rfl
  | .finalize r =>
    rw [show toQOps s (.finalize r) = [] from rfl, applyQOps_nil]
    apply bridge_stable hbs
    simp only [step]; (repeat' split) <;> rfl
  | .setPriority t p =>
    rw [show toQOps s (.setPriority t p) = [] from rfl, applyQOps_nil]
    apply bridge_stable hbs
    simp only [step]; (repeat' split) <;> rfl
  | .setDeadline t d =>
    rw [show toQOps s (.setDeadline t d) = [] from rfl, applyQOps_nil]
    apply bridge_stable hbs
    simp only [step]; (repeat' split) <;> rfl

/-! ## applyQOps append lemma -/

/-- Distributing append over `applyQOps`: processing `as ++ bs` equals
    processing `bs` starting from the state after processing `as`. -/
theorem applyQOps_append (wqs : WorkerQueues) (as bs : List QOp) :
    applyQOps wqs (as ++ bs) = applyQOps (applyQOps wqs as) bs := by
  induction as generalizing wqs with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.cons_append, applyQOps]
    exact ih (applyQOp wqs op)

/-! ## Trace-level bridge theorems -/

/-- **`bridge_run_general`** — From any state satisfying `BridgeState`, running
    any operation sequence keeps `BridgeState` with translated queue effects.
    This is the inductive backbone of the trace theorem. -/
theorem bridge_run_general (s : RuntimeState) (wqs : WorkerQueues)
    (ops : List RuntimeOp) (hbs : BridgeState s wqs) :
    BridgeState (run s ops) (applyQOps wqs (toQOpsTrace s ops)) := by
  induction ops generalizing s wqs with
  | nil => simp [run, applyQOps, toQOpsTrace, hbs]
  | cons op rest ih =>
    simp only [run_cons, toQOpsTrace]
    rw [applyQOps_append]
    exact ih (step s op).1 (applyQOps wqs (toQOps s op))
             (bridge_step_single_worker s op wqs hbs)

/-- **`bridge_run_tracks_single_worker`** — Running any sequence of operations
    from the initial state keeps `BridgeState` with the initial (empty) worker
    queues updated by all translated queue effects.

    This is the headline bridge theorem (RFC 036): it shows that the queue
    projection tracks Henret's `readyQ` through an entire run. -/
theorem bridge_run_tracks_single_worker (ops : List RuntimeOp) :
    BridgeState
      (run RuntimeState.init ops)
      (applyQOps WorkerQueues.init (toQOpsTrace RuntimeState.init ops)) :=
  bridge_run_general RuntimeState.init WorkerQueues.init ops bridgeState_init

/-! ## Backward-compatible existential form -/

/-- Every reachable state has a worker-queue witness satisfying `BridgeState`.
    Kept for backward compatibility; `bridge_run_tracks_single_worker` and
    `bridge_step_single_worker` are the stronger headline theorems (RFC 036). -/
theorem reachable_bridge (ops : List RuntimeOp) :
    ∃ wqs : WorkerQueues, BridgeState (run RuntimeState.init ops) wqs :=
  ⟨applyQOps WorkerQueues.init (toQOpsTrace RuntimeState.init ops),
   bridge_run_tracks_single_worker ops⟩

end Henret.Bridge
