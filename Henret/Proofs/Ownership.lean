import Henret.Proofs.Invariants
import Henret.Proofs.Lifecycle
import Henret.Proofs.StepProjections

namespace Henret

/-! ## Wake helpers preserve definedness -/

/-- `wakeOne` maps `some` to `some`: waking never un-spawns a task. -/
theorem wakeOne_isSome {ts : TaskMap} {u : TaskId} {st : TaskState}
    (h : ts u = some st) (t : TaskId) :
    ∃ st', wakeOne ts t u = some st' := by
  by_cases hu : u = t
  · subst hu
    unfold wakeOne
    rw [h]
    cases st <;> simp_all [upd]
  · unfold wakeOne
    cases hts : ts t with
    | none => exact ⟨st, h⟩
    | some s' => cases s' <;> simp_all [upd, hu]

/-- `wakeMany` maps `some` to `some`. -/
theorem wakeMany_isSome {u : TaskId} :
    ∀ {l : List TaskId} {ts : TaskMap} {st : TaskState},
      ts u = some st → ∃ st', wakeMany ts l u = some st' := by
  intro l
  induction l with
  | nil => intro ts st h; exact ⟨st, h⟩
  | cons t r ih =>
    intro ts st h
    obtain ⟨st1, h1⟩ := wakeOne_isSome h t
    exact ih h1

/-- `wakeOne` maps `none` to `none`: waking never spawns a task. -/
theorem wakeOne_none {ts : TaskMap} {u : TaskId} (h : ts u = none)
    (t : TaskId) : wakeOne ts t u = none := by
  unfold wakeOne
  cases hts : ts t with
  | none => exact h
  | some s' =>
    cases s' with
    | sleeping | waitingTimed =>
      have hu : u ≠ t := fun he => by rw [he, hts] at h; cases h
      simp [upd, hu]
      exact h
    | new | ready | running | yielded | completed | cancelled | waiting => exact h

/-- `wakeMany` maps `none` to `none`. -/
theorem wakeMany_none {u : TaskId} :
    ∀ {l : List TaskId} {ts : TaskMap}, ts u = none →
      wakeMany ts l u = none := by
  intro l
  induction l with
  | nil => intro ts h; exact h
  | cons t r ih => intro ts h; exact ih (wakeOne_none h t)

/-! ## Once spawned, always spawned -/

/-- No operation maps a spawned task's state back to `none`. -/
theorem step_preserves_spawned {s : RuntimeState} {u : TaskId} {st : TaskState}
    (h : s.taskState u = some st) (op : RuntimeOp) :
    ∃ st', ((step s op).1).taskState u = some st' := by
  cases op with
  | spawn a =>
    cases hts : s.taskState s.nextId with
    | some _ => exact ⟨st, by simp [step, hts, h]⟩
    | none =>
      by_cases hu : u = s.nextId
      · subst hu; rw [h] at hts; cases hts
      · exact ⟨st, by simp [step, hts, upd, hu, h]⟩
  | spawnChild pt pa =>
    -- step result: if all guards pass, taskState updated at nextId only; else unchanged
    have hstate : ∃ st', ((step s (.spawnChild pt pa)).1).taskState u = some st' := by
      by_cases hrt : s.running = some pt
      · cases hts2 : s.taskState pt with
        | none => exact ⟨st, by simp [step, hrt, hts2, h]⟩
        | some stpt =>
          cases running_case : stpt with
          | running =>
            cases how : s.taskOwner pt with
            | none => exact ⟨st, by simp_all [step, upd]⟩
            | some _ =>
              cases hfresh : s.taskState s.nextId with
              | some _ => exact ⟨st, by simp_all [step, upd]⟩
              | none =>
                by_cases hu : u = s.nextId
                · subst hu; rw [h] at hfresh; cases hfresh
                · exact ⟨st, by simp_all [step, upd]⟩
          | new | ready | yielded | sleeping | waitingTimed | waiting | completed | cancelled =>
            exact ⟨st, by simp_all [step, upd]⟩
      · exact ⟨st, by simp [step, hrt, h]⟩
    exact hstate
  | schedule =>
    cases hr : s.running with
    | some _ => exact ⟨st, by simp [step, hr, h]⟩
    | none =>
      cases hq : s.readyQ with
      | nil => exact ⟨st, by simp [step, hr, hq, h]⟩
      | cons t q =>
        by_cases hrun : (s.taskState t).any TaskState.isRunnable = true
        · simp only [step, hr, hq, if_pos hrun]
          by_cases hut : u = t
          · subst hut; exact ⟨.running, by simp [upd]⟩
          · exact ⟨st, by simp [upd, if_neg hut]; exact h⟩
        · exact ⟨st, by simp [step, hr, hq, hrun, h]⟩
  | yield t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => exact ⟨st, by simp [step, hrt, hts, h]⟩
      | some st' =>
        cases st' with
        | running =>
          by_cases hut : u = t
          · subst hut; exact ⟨.yielded, by simp [step, hrt, hts, upd]⟩
          · exact ⟨st, by simp [step, hrt, hts, upd, if_neg hut]; exact h⟩
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          exact ⟨st, by simp [step, hrt, hts, h]⟩
    · exact ⟨st, by simp [step, hrt, h]⟩
  | complete t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => exact ⟨st, by simp [step, hrt, hts, h]⟩
      | some st' =>
        cases st' with
        | running =>
          by_cases hut : u = t
          · subst hut; exact ⟨.completed, by simp [step, hrt, hts, upd]⟩
          · exact ⟨st, by simp [step, hrt, hts, upd, if_neg hut]; exact h⟩
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          exact ⟨st, by simp [step, hrt, hts, h]⟩
    · exact ⟨st, by simp [step, hrt, h]⟩
  | cancel t =>
    cases hts : s.taskState t with
    | none => exact ⟨st, by simp [step, hts, h]⟩
    | some st' =>
      by_cases hterm' : st'.isTerminal = true
      · exact ⟨st, by simp [step, hts, hterm', h]⟩
      · simp at hterm'
        by_cases hut : u = t
        · subst hut; exact ⟨.cancelled, by simp [step, hts, hterm', upd]⟩
        · exact ⟨st, by simp [step, hts, hterm', upd, if_neg hut]; exact h⟩
  | send t' b m =>
    by_cases hrt : s.running = some t'
    · cases hts : s.taskState t' with
      | none => exact ⟨st, by simp [step, hrt, hts, h]⟩
      | some stt =>
        cases stt with
        | running =>
          cases how : s.taskOwner t' with
          | none => exact ⟨st, by simp [step, hrt, hts, how, h]⟩
          | some o =>
            cases hmb : s.mailboxes b with
            | none => exact ⟨st, by simp [step, hrt, hts, how, hmb, h]⟩
            | some mb =>
              cases hw : s.mailboxWaiters b with
              | cons w ws =>
                by_cases huw : u = w
                · subst huw; exact ⟨.ready, by simp [step, hrt, hts, how, hmb, hw, upd]⟩
                · exact ⟨st, by simp [step, hrt, hts, how, hmb, hw, upd, huw]; exact h⟩
              | nil =>
                cases htw : s.timedMailboxWaiters b with
                | nil => exact ⟨st, by simp [step, hrt, hts, how, hmb, hw, htw, upd, h]⟩
                | cons w ws =>
                  by_cases huw : u = w
                  · subst huw; exact ⟨.ready, by simp [step, hrt, hts, how, hmb, hw, htw, upd]⟩
                  · exact ⟨st, by simp [step, hrt, hts, how, hmb, hw, htw, upd, huw]; exact h⟩
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          exact ⟨st, by simp [step, hrt, hts, h]⟩
    · exact ⟨st, by simp [step, hrt, h]⟩
  | receive t' =>
    by_cases hrt : s.running = some t'
    · cases hts : s.taskState t' with
      | none => exact ⟨st, by simp [step, hrt, hts, h]⟩
      | some stt =>
        cases stt with
        | running =>
          cases how : s.taskOwner t' with
          | none => exact ⟨st, by simp [step, hrt, hts, how, h]⟩
          | some a =>
            cases hmb : s.mailboxes a with
            | none => exact ⟨st, by simp [step, hrt, hts, how, hmb, h]⟩
            | some mb =>
              cases hd : mb.dequeue with
              | some p => exact ⟨st, by simp [step, hrt, hts, how, hmb, hd, h]⟩
              | none =>
                by_cases hut : u = t'
                · subst hut; exact ⟨.waiting, by simp [step, hrt, hts, how, hmb, hd, upd]⟩
                · exact ⟨st, by simp [step, hrt, hts, how, hmb, hd, upd, hut]; exact h⟩
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          exact ⟨st, by simp [step, hrt, hts, h]⟩
    · exact ⟨st, by simp [step, hrt, h]⟩
  | inject a m =>
    cases hmb : s.mailboxes a with
    | none => exact ⟨st, by simp [step, hmb, h]⟩
    | some mb =>
      cases hw : s.mailboxWaiters a with
      | cons w ws =>
        by_cases huw : u = w
        · subst huw; exact ⟨.ready, by simp [step, hmb, hw, upd]⟩
        · exact ⟨st, by simp [step, hmb, hw, upd, huw]; exact h⟩
      | nil =>
        cases htw : s.timedMailboxWaiters a with
        | nil => exact ⟨st, by simp [step, hmb, hw, htw, upd, h]⟩
        | cons w ws =>
          by_cases huw : u = w
          · subst huw; exact ⟨.ready, by simp [step, hmb, hw, htw, upd]⟩
          · exact ⟨st, by simp [step, hmb, hw, htw, upd, huw]; exact h⟩
  | sleep t d =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => exact ⟨st, by simp [step, hrt, hts, h]⟩
      | some st' =>
        cases st' with
        | running =>
          by_cases hut : u = t
          · subst hut; exact ⟨.sleeping, by simp [step, hrt, hts, upd]⟩
          · exact ⟨st, by simp [step, hrt, hts, upd, if_neg hut]; exact h⟩
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          exact ⟨st, by simp [step, hrt, hts, h]⟩
    · exact ⟨st, by simp [step, hrt, h]⟩
  | tick now =>
    by_cases hle : s.now ≤ now
    · -- taskState after tick = wakeMany applied to woken; wakeMany preserves isSome
      simp only [step, if_pos hle]
      apply wakeMany_isSome h
    · exact ⟨st, by simp [step, hle, h]⟩
  | wake t =>
    cases hts : s.taskState t with
    | none => exact ⟨st, by simp [step, hts, h]⟩
    | some st' =>
      cases st' with
      | sleeping =>
        by_cases hut : u = t
        · subst hut; exact ⟨.ready, by simp [step, hts, upd]⟩
        · exact ⟨st, by simp [step, hts, upd, if_neg hut]; exact h⟩
      | new | ready | running | yielded | waitingTimed | completed | cancelled | waiting =>
        exact ⟨st, by simp [step, hts, h]⟩
  | cancelTree root =>
    simp only [step, applyCancelTree]
    by_cases hu : u ∈ descendantsOf s root
    · simp only [hu, ite_true, h]
      by_cases hterm : st.isTerminal
      · exact ⟨st, by simp [hterm]⟩
      · exact ⟨.cancelled, by simp [hterm]⟩
    · exact ⟨st, by simp [hu, h]⟩
  | receiveUntil t' deadline =>
    by_cases hrt : s.running = some t'
    · cases hts : s.taskState t' with
      | none => exact ⟨st, by simp [step, hrt, hts, h]⟩
      | some stt =>
        cases stt with
        | running =>
          cases how : s.taskOwner t' with
          | none => exact ⟨st, by simp [step, hrt, hts, how, h]⟩
          | some a =>
            cases hmb : s.mailboxes a with
            | none => exact ⟨st, by simp [step, hrt, hts, how, hmb, h]⟩
            | some mb =>
              cases hdq : mb.dequeue with
              | some p => exact ⟨st, by simp [step, hrt, hts, how, hmb, hdq, upd, h]⟩
              | none =>
                by_cases hpast : deadline ≤ s.now
                · exact ⟨st, by simp [step, hrt, hts, how, hmb, hdq, if_pos hpast, h]⟩
                · simp only [step, hrt, hts, how, hmb, hdq, if_neg hpast]
                  by_cases hut : u = t'
                  · subst hut; exact ⟨.waitingTimed, by simp [upd]⟩
                  · exact ⟨st, by simp [upd, if_neg hut]; exact h⟩
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          exact ⟨st, by simp [step, hrt, hts, h]⟩
    · exact ⟨st, by simp [step, hrt, h]⟩

/-- One step never moves a task out of a terminal state.
Requires `WellFormed s` because send/inject wake-one can write `.ready`
to a waiter; waiters are `.waiting` (non-terminal) in well-formed states. -/
theorem step_preserves_terminal {s : RuntimeState} {u : TaskId}
    {st : TaskState} (h_wf : WellFormed s) (h : s.taskState u = some st)
    (hterm : st.isTerminal = true) (op : RuntimeOp) :
    ((step s op).1).taskState u = some st := by
  cases op with
  | spawn a =>
    simp only [step]; split
    · next heq =>
      have hu : u ≠ s.nextId := fun he => by subst he; rw [h] at heq; cases heq
      simp [upd, hu, h]
    · exact h
  | spawnChild pt pa =>
    by_cases hrt : s.running = some pt
    · cases hts2 : s.taskState pt with
      | none => simp [step, hrt, hts2]; exact h
      | some stpt =>
          cases running_case : stpt with
          | running =>
            cases how : s.taskOwner pt with
            | none => simp_all [step, upd]
            | some _ =>
              cases hfresh : s.taskState s.nextId with
              | some _ => simp_all [step, upd]
              | none =>
                have hu : u ≠ s.nextId := fun he => by subst he; rw [h] at hfresh; cases hfresh
                simp_all [step, upd]
          | new | ready | yielded | sleeping | waitingTimed | waiting | completed | cancelled =>
            simp_all [step, upd]
    · simp [step, hrt]; exact h
  | schedule =>
    cases hr : s.running with
    | some _ => simp [step, hr, h]
    | none =>
      cases hq : s.readyQ with
      | nil => simp [step, hr, hq]; exact h
      | cons t q =>
        by_cases hrun : (s.taskState t).any TaskState.isRunnable = true
        · simp only [step, hr, hq, if_pos hrun]
          by_cases hut : u = t
          · subst hut
            rw [h] at hrun
            simp only [Option.any, TaskState.isRunnable] at hrun
            cases st <;> simp_all [TaskState.isTerminal, TaskState.isRunnable]
          · simp only [upd, if_neg hut]; exact h
        · simp [step, hr, hq, hrun]; exact h
  | yield t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]; exact h
      | some st' =>
        cases st' with
        | running =>
          by_cases hut : u = t
          · subst hut
            have heq := hts.symm.trans h; simp at heq; subst heq
            simp [TaskState.isTerminal] at hterm
          · simp [step, hrt, hts, upd, hut]; exact h
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          simp [step, hrt, hts]; exact h
    · simp [step, hrt]; exact h
  | complete t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]; exact h
      | some st' =>
        cases st' with
        | running =>
          by_cases hut : u = t
          · subst hut
            have heq := hts.symm.trans h; simp at heq; subst heq
            simp [TaskState.isTerminal] at hterm
          · simp [step, hrt, hts, upd, hut]; exact h
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          simp [step, hrt, hts]; exact h
    · simp [step, hrt]; exact h
  | cancel t =>
    cases hts : s.taskState t with
    | none => simp [step, hts]; exact h
    | some st' =>
      by_cases hterm' : st'.isTerminal = true
      · simp [step, hts, hterm']; exact h
      · simp at hterm'
        by_cases hut : u = t
        · subst hut
          have heq := hts.symm.trans h; simp at heq; subst heq
          exact absurd hterm (by rw [hterm']; decide)
        · simp [step, hts, hterm', upd, hut]; exact h
  | send t b m =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]; exact h
      | some st' =>
        cases st' with
        | running =>
          cases how : s.taskOwner t with
          | none => simp [step, hrt, hts, how]; exact h
          | some o =>
            cases hmb : s.mailboxes b with
            | none => simp [step, hrt, hts, how, hmb]; exact h
            | some mb =>
              cases hw : s.mailboxWaiters b with
              | cons w ws =>
                by_cases huw : u = w
                · subst huw
                  have hmem : u ∈ s.mailboxWaiters b := hw ▸ List.mem_cons_self u ws
                  rw [h_wf.waiters_waiting b u hmem] at h; simp at h; subst h; simp [TaskState.isTerminal] at hterm
                · simp [step, hrt, hts, how, hmb, hw, upd, huw]; exact h
              | nil =>
                cases htw : s.timedMailboxWaiters b with
                | nil => simp [step, hrt, hts, how, hmb, hw, htw, upd]; exact h
                | cons w ws =>
                  by_cases huw : u = w
                  · subst huw
                    have hmem : u ∈ s.timedMailboxWaiters b := htw ▸ List.mem_cons_self u ws
                    rw [h_wf.timed_waiters_valid b u hmem] at h; simp at h; subst h; simp [TaskState.isTerminal] at hterm
                  · simp [step, hrt, hts, how, hmb, hw, htw, upd, huw]; exact h
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          simp [step, hrt, hts]; exact h
    · simp [step, hrt]; exact h
  | receive t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]; exact h
      | some st' =>
        cases st' with
        | running =>
          cases how : s.taskOwner t with
          | none => simp [step, hrt, hts, how]; exact h
          | some a =>
            cases hmb : s.mailboxes a with
            | none => simp [step, hrt, hts, how, hmb]; exact h
            | some mb =>
              cases hd : mb.dequeue with
              | some p => simp [step, hrt, hts, how, hmb, hd]; exact h
              | none =>
                by_cases hut : u = t
                · subst hut
                  have heq := hts.symm.trans h; simp at heq; subst heq
                  simp [TaskState.isTerminal] at hterm
                · simp [step, hrt, hts, how, hmb, hd, upd, hut]; exact h
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          simp [step, hrt, hts]; exact h
    · simp [step, hrt]; exact h
  | inject a m =>
    cases hmb : s.mailboxes a with
    | none => simp [step, hmb]; exact h
    | some mb =>
      cases hw : s.mailboxWaiters a with
      | cons w ws =>
        by_cases huw : u = w
        · subst huw
          have hmem : u ∈ s.mailboxWaiters a := hw ▸ List.mem_cons_self u ws
          rw [h_wf.waiters_waiting a u hmem] at h; simp at h; subst h; simp [TaskState.isTerminal] at hterm
        · simp [step, hmb, hw, upd, huw]; exact h
      | nil =>
        cases htw : s.timedMailboxWaiters a with
        | nil => simp [step, hmb, hw, htw, upd]; exact h
        | cons w ws =>
          by_cases huw : u = w
          · subst huw
            have hmem : u ∈ s.timedMailboxWaiters a := htw ▸ List.mem_cons_self u ws
            rw [h_wf.timed_waiters_valid a u hmem] at h; simp at h; subst h; simp [TaskState.isTerminal] at hterm
          · simp [step, hmb, hw, htw, upd, huw]; exact h
  | sleep t d =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]; exact h
      | some st' =>
        cases st' with
        | running =>
          by_cases hut : u = t
          · subst hut
            have heq := hts.symm.trans h; simp at heq; subst heq
            simp [TaskState.isTerminal] at hterm
          · simp [step, hrt, hts, upd, hut]; exact h
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          simp [step, hrt, hts]; exact h
    · simp [step, hrt]; exact h
  | tick t =>
    by_cases hle : s.now ≤ t
    · simp only [step, if_pos hle]
      have hnot : u ∉ (((Timer.expired s.timers t).map TimerEntry.task).filter
            (fun v => s.taskState v = some .sleeping) ++
            ((Timer.expired s.timers t).map TimerEntry.task).filter
            (fun v => s.taskState v = some .waitingTimed)) := by
        intro hm
        simp only [List.mem_append, List.mem_filter, decide_eq_true_eq] at hm
        rcases hm with ⟨_, hv⟩ | ⟨_, hv⟩
        · have := h.symm.trans hv; cases this; simp [TaskState.isTerminal] at hterm
        · have := h.symm.trans hv; cases this; simp [TaskState.isTerminal] at hterm
      rw [wakeMany_preserves_other hnot]; exact h
    · simp [step, hle]; exact h
  | wake t =>
    cases hts : s.taskState t with
    | none => simp [step, hts]; exact h
    | some st' =>
      cases st' with
      | sleeping =>
        by_cases hut : u = t
        · subst hut
          have heq := hts.symm.trans h; simp at heq; subst heq
          simp [TaskState.isTerminal] at hterm
        · simp [step, hts, upd, hut]; exact h
      | new | ready | running | yielded | waitingTimed | completed | cancelled | waiting =>
        simp [step, hts]; exact h
  | cancelTree root =>
    simp only [step, applyCancelTree]
    by_cases hu : u ∈ descendantsOf s root
    · simp only [hu, ite_true, h, hterm]
    · simp [hu, h]
  | receiveUntil t' deadline =>
    by_cases hrt : s.running = some t'
    · cases hts : s.taskState t' with
      | none => simp [step, hrt, hts]; exact h
      | some st' =>
        cases st' with
        | running =>
          cases how : s.taskOwner t' with
          | none => simp [step, hrt, hts, how]; exact h
          | some a =>
            cases hmb : s.mailboxes a with
            | none => simp [step, hrt, hts, how, hmb]; exact h
            | some mb =>
              cases hdq : mb.dequeue with
              | some p => simp [step, hrt, hts, how, hmb, hdq]; exact h
              | none =>
                by_cases hpast : deadline ≤ s.now
                · simp [step, hrt, hts, how, hmb, hdq, if_pos hpast]; exact h
                · by_cases hut : u = t'
                  · subst hut
                    have heq := hts.symm.trans h; simp at heq; subst heq
                    simp [TaskState.isTerminal] at hterm
                  · simp [step, hrt, hts, how, hmb, hdq, if_neg hpast, upd, hut]; exact h
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          simp [step, hrt, hts]; exact h
    · simp [step, hrt]; exact h
theorem step_preserves_completed {s : RuntimeState} {u : TaskId}
    (h_wf : WellFormed s) (h : s.taskState u = some .completed) (op : RuntimeOp) :
    ((step s op).1).taskState u = some .completed :=
  step_preserves_terminal h_wf h rfl op

/-- Cancelled tasks never complete later (RFC 004 acceptance). -/
theorem step_preserves_cancelled {s : RuntimeState} {u : TaskId}
    (h_wf : WellFormed s) (h : s.taskState u = some .cancelled) (op : RuntimeOp) :
    ((step s op).1).taskState u = some .cancelled :=
  step_preserves_terminal h_wf h rfl op


/-- `wake t` does not touch any task other than `t`. -/
theorem wake_exact {s : RuntimeState} {t u : TaskId} (h : u ≠ t) :
    ((step s (.wake t)).1).taskState u = s.taskState u := by
  simp only [step]
  split
  · simp [upd, h]
  · rfl

/-- A valid wake moves the exact sleeping task to ready and enqueues
it exactly once at the tail. -/
theorem wake_sets_ready {s : RuntimeState} {t : TaskId}
    (h : s.taskState t = some .sleeping) :
    ((step s (.wake t)).1).taskState t = some .ready ∧
    ((step s (.wake t)).1).readyQ = s.readyQ ++ [t] := by
  simp [step, h, upd]

/-- Duplicate wake cannot duplicate ready entries: after a successful
wake, waking the same task again is invalid and changes nothing. -/
theorem wake_twice_invalid {s : RuntimeState} {t : TaskId}
    (h : s.taskState t = some .sleeping) :
    step ((step s (.wake t)).1) (.wake t) =
      (((step s (.wake t)).1), .invalid) := by
  have hready := (wake_sets_ready h).1
  generalize hS : (step s (.wake t)).1 = s' at hready ⊢
  simp [step, hready]

/-! ## Invalid operations never mutate (RFC 005, RFC 016) -/

/-- An invalid operation never mutates state: if `step` reports
`.invalid`, the state component is exactly the input state.  Combined
with the construction of `step`, this makes "invalid ⇒ no-op" a
theorem rather than a convention. -/
theorem step_invalid_unchanged {s : RuntimeState} {op : RuntimeOp}
    (h : (step s op).2 = .invalid) : (step s op).1 = s := by
  cases op with
  | spawn a =>
    cases hts : s.taskState s.nextId with
    | none => simp [step, hts] at h
    | some _ => simp [step, hts]
  | spawnChild t a =>
    by_cases hrt : s.running = some t
    · cases hts2 : s.taskState t with
      | none => simp_all [step]
      | some stpt => cases running_case : stpt with
        | running => cases how : s.taskOwner t with
          | none => simp_all [step]
          | some _ => cases hfresh : s.taskState s.nextId with
            | none => simp_all [step, upd]
            | some _ => simp_all [step]
        | new | ready | yielded | sleeping | waitingTimed | waiting | completed | cancelled =>
          simp_all [step]
    · simp_all [step]
  | schedule =>
    cases hr : s.running with
    | some _ => simp [step, hr]
    | none =>
      cases hq : s.readyQ with
      | nil => simp [step, hr, hq]
      | cons t q =>
        by_cases hrun : (s.taskState t).any TaskState.isRunnable = true
        · simp [step, hr, hq, hrun] at h
        · simp at hrun; simp [step, hr, hq, hrun]
  | yield t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st => cases st <;> simp [step, hrt, hts] <;> simp [step, hrt, hts] at h
    · simp [step, hrt]
  | complete t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st => cases st <;> simp [step, hrt, hts] <;> simp [step, hrt, hts] at h
    · simp [step, hrt]
  | cancel t =>
    cases hts : s.taskState t with
    | none => simp [step, hts]
    | some st =>
      by_cases hterm : st.isTerminal = true
      · simp [step, hts, hterm]
      · simp at hterm; simp [step, hts, hterm] at h
  | send t b m =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st =>
        cases st with
        | running =>
          cases how : s.taskOwner t with
          | none => simp [step, hrt, hts, how]
          | some o =>
            cases hmb : s.mailboxes b with
            | none => simp [step, hrt, hts, how, hmb]
            | some mb =>
              -- send always succeeds when guards pass; no invalid branch
              cases hw : s.mailboxWaiters b with
              | cons w ws => simp [step, hrt, hts, how, hmb, hw] at h
              | nil =>
                cases htw : s.timedMailboxWaiters b with
                | nil => simp [step, hrt, hts, how, hmb, hw, htw] at h
                | cons w ws => simp [step, hrt, hts, how, hmb, hw, htw] at h
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          simp [step, hrt, hts]
    · simp [step, hrt]
  | receive t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st =>
        cases st with
        | running =>
          cases how : s.taskOwner t with
          | none => simp [step, hrt, hts, how]
          | some a =>
            cases hmb : s.mailboxes a with
            | none => simp [step, hrt, hts, how, hmb]
            | some mb =>
              cases hd : mb.dequeue with
              | none => simp [step, hrt, hts, how, hmb, hd] at h
              | some p => simp [step, hrt, hts, how, hmb, hd] at h
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          simp [step, hrt, hts]
    · simp [step, hrt]
  | inject a m =>
    cases hmb : s.mailboxes a with
    | none => simp [step, hmb]
    | some mb =>
      cases hw : s.mailboxWaiters a with
      | cons w ws => simp [step, hmb, hw] at h
      | nil =>
        cases htw : s.timedMailboxWaiters a with
        | nil => simp [step, hmb, hw, htw] at h
        | cons w ws => simp [step, hmb, hw, htw] at h
  | sleep t d =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st => cases st <;> simp [step, hrt, hts] <;> simp [step, hrt, hts] at h
    · simp [step, hrt]
  | tick t =>
    by_cases hle : s.now ≤ t
    · simp [step, hle] at h
    · simp [step, hle]
  | wake t =>
    cases hts : s.taskState t with
    | none => simp [step, hts]
    | some st => cases st <;> simp [step, hts] <;> simp [step, hts] at h
  | cancelTree _ => simp [step] at h
  | receiveUntil t deadline =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts]
      | some st =>
        cases st with
        | running =>
          cases how : s.taskOwner t with
          | none => simp [step, hrt, hts, how]
          | some a =>
            cases hmb : s.mailboxes a with
            | none => simp [step, hrt, hts, how, hmb]
            | some mb =>
              cases hdq : mb.dequeue with
              | some p => simp [step, hrt, hts, how, hmb, hdq] at h
              | none =>
                by_cases hpast : deadline ≤ s.now
                · simp [step, hrt, hts, how, hmb, hdq, if_pos hpast] at h
                · simp [step, hrt, hts, how, hmb, hdq, if_neg hpast] at h
        | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting =>
          simp [step, hrt, hts]
    · simp [step, hrt]


end Henret
