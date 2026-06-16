import Henret.Proofs.Invariants
import Henret.Proofs.Ownership
import Henret.Proofs.StepFields
import Henret.Proofs.StepFields

namespace Henret

-- ─────────────────────────────────────────────────────────────────
-- Per-operation WellFormed preservation: lifecycle operations
-- (spawn, schedule, yield, complete, cancel)   RFC 034
-- ─────────────────────────────────────────────────────────────────

theorem preserves_wf_spawn (h : WellFormed s) (a : ActorId) :
    WellFormed ((step s (.spawn a)).1) := by
  by_cases hrs : s.runtimeStatus = .running
  · cases hts : s.taskState s.nextId with
    | some _ => simpa [step, hrs, hts] using h
    | none =>
      have hnq : s.nextId ∉ s.readyQ := fun hm => by
        have h1 := h.readyQ_queued _ hm; rw [hts] at h1; simp [Option.any] at h1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [step, hrs, hts, if_true]
        exact nodup_append_singleton h.readyQ_nodup hnq
      · intro u hm
        simp only [step, hrs, hts, if_true] at hm ⊢
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · have hu : u ≠ s.nextId := fun he => hnq (he ▸ hm)
          simp only [upd, if_neg hu]; exact h.readyQ_queued u hm
        · simp [upd, Option.any, TaskState.isRunnable]
      · intro u hr
        simp only [step, hrs, hts, if_true] at hr ⊢
        have h1 := h.running_runs u hr
        have hu : u ≠ s.nextId := fun he => by rw [he, hts] at h1; cases h1
        simp only [upd, if_neg hu]; exact h1
      · simp only [step, hrs, hts, if_true]; exact h.timers_nodup
      · intro e he
        simp only [step, hrs, hts, if_true] at he ⊢
        rcases h.timers_sleep e he with h1 | h1
        · have hu : e.task ≠ s.nextId := fun heq => by rw [heq, hts] at h1; cases h1
          exact Or.inl (by simp only [upd, if_neg hu]; exact h1)
        · have hu : e.task ≠ s.nextId := fun heq => by rw [heq, hts] at h1; cases h1
          exact Or.inr (by simp only [upd, if_neg hu]; exact h1)
      · intro u hu
        simp only [step, hrs, hts, if_true] at hu ⊢
        have h1 : u ≠ s.nextId := Nat.ne_of_gt hu
        have h2 : s.nextId ≤ u := Nat.le_of_succ_le hu
        simp only [upd, if_neg h1]; exact h.fresh_none u h2
      · simp only [step, hrs, hts, if_true]; exact h.timers_sorted
      · intro u st hts'
        simp only [step, hrs, hts, if_true] at hts' ⊢
        by_cases hu : u = s.nextId
        · subst hu; exact ⟨a, by simp [upd]⟩
        · simp only [upd, if_neg hu] at hts' ⊢; exact h.spawned_has_owner u st hts'
      · intro u b hown
        cases hmb0 : s.mailboxes a with
        | some mba =>
          simp only [step, hrs, hts, hmb0, if_true] at hown ⊢
          by_cases hu : u = s.nextId
          · subst hu; simp only [upd_self] at hown; injection hown with hab; subst hab
            exact ⟨mba, hmb0⟩
          · simp only [upd, if_neg hu] at hown; exact h.owned_has_mailbox u b hown
        | none =>
          simp only [step, hrs, hts, hmb0, if_true] at hown ⊢
          by_cases hu : u = s.nextId
          · subst hu; simp only [upd_self] at hown; injection hown with hab; subst hab
            exact ⟨Mailbox.empty, by simp [upd]⟩
          · simp only [upd, if_neg hu] at hown
            obtain ⟨mb', hmb'⟩ := h.owned_has_mailbox u b hown
            by_cases hba : b = a
            · subst hba; rw [hmb'] at hmb0; cases hmb0
            · exact ⟨mb', by simp only [upd, if_neg hba]; exact hmb'⟩
      · intro u st hts' hrun
        simp only [step, hrs, hts, if_true] at hts' ⊢
        by_cases hu : u = s.nextId
        · subst hu; rw [List.mem_append, List.mem_singleton]; exact Or.inr rfl
        · simp only [upd, if_neg hu] at hts'
          rw [List.mem_append]; exact Or.inl (h.runnable_queued u st hts' hrun)
      · -- waiters_waiting (RFC 031)
        intro a u hm; simp only [step, hrs, hts, if_true] at hm ⊢
        have hts_u := h.waiters_waiting a u hm
        by_cases hu : u = s.nextId
        · subst hu; simp [h.fresh_none s.nextId (Nat.le_refl _)] at hts_u
        · simp only [upd, if_neg hu]; exact hts_u
      · -- waiters_owned (RFC 031)
        intro a u hm; simp only [step, hrs, hts, if_true] at hm ⊢
        have hts_u := h.waiters_waiting a u hm
        have ho := h.waiters_owned a u hm
        by_cases hu : u = s.nextId
        · subst hu; simp [h.fresh_none s.nextId (Nat.le_refl _)] at hts_u
        · simp only [upd, if_neg hu]; exact ho
      · -- waiting_queued (RFC 031)
        intro u hts'
        simp only [step, hrs, hts, if_true] at hts' ⊢
        by_cases hu : u = s.nextId
        · subst hu; simp only [upd_self] at hts'; cases hts'
        · simp only [upd, if_neg hu] at hts'
          obtain ⟨a', ha', hmem⟩ := h.waiting_queued u hts'
          exact ⟨a', by simp only [upd, if_neg hu]; exact ha', hmem⟩
      · -- waiters_nodup (RFC 031)
        intro a; simp only [step, hrs, hts, if_true]; exact h.waiters_nodup a
      · -- parent_lt (RFC 042)
        intro t p hp
        exact wf_parent_lt_pass h (by simp [step, hrs, hts]) t p hp
      · -- parent_spawned (RFC 032)
        intro t p hp
        have hpar : s.taskParent t = some p := by simp only [step, hrs, hts, upd, if_true] at hp; exact hp
        obtain ⟨st, hst⟩ := h.parent_spawned t p hpar
        -- taskState_new at p: spawn only sets nextId; no parent is nextId by parent_lt+fresh_none
        have hpn : p ≠ s.nextId := fun he => absurd (he ▸ hts) (by rw [h.parent_spawned t p hpar |>.choose_spec]; simp)
        exact ⟨st, by simp only [step, hrs, hts, upd, if_neg hpn, if_true]; exact hst⟩
      · -- occ_fresh (RFC 033): spawn creates empty mailbox at most
        intro ac mb env hmb henv; simp only [step, hrs, hts, if_true] at hmb ⊢
        cases hmba : s.mailboxes a with
        | some _ => simp only [hmba] at hmb; exact h.occ_fresh ac mb env hmb henv
        | none =>
          simp only [hmba] at hmb
          by_cases hac : ac = a
          · subst hac; rw [upd_self] at hmb
            have hmeq : Mailbox.empty = mb := Option.some.inj hmb; subst hmeq
            simp [Mailbox.empty] at henv
          · exact h.occ_fresh ac mb env (by simp only [upd, if_neg hac] at hmb; exact hmb) henv
      · -- occ_nodup (RFC 033): spawn creates empty mailbox at most
        intro ac mb hmb; simp only [step, hrs, hts, if_true] at hmb
        cases hmba : s.mailboxes a with
        | some _ => simp only [hmba] at hmb; exact h.occ_nodup ac mb hmb
        | none =>
          simp only [hmba] at hmb
          by_cases hac : ac = a
          · subst hac; rw [upd_self] at hmb
            have hmeq : Mailbox.empty = mb := Option.some.inj hmb; subst hmeq
            simp [Mailbox.empty]
          · exact h.occ_nodup ac mb (by simp only [upd, if_neg hac] at hmb; exact hmb)
      · -- occ_disjoint (RFC 033): spawn creates empty mailbox at most
        intro ac b mba mbb hab hmba hmbb ea hea eb heb
        simp only [step, hrs, hts, if_true] at hmba hmbb
        have hmba' : s.mailboxes ac = some mba := by
          cases hm : s.mailboxes a with
          | some _ => simp only [hm] at hmba; exact hmba
          | none =>
            simp only [hm] at hmba
            by_cases h1 : ac = a
            · subst h1; rw [upd_self] at hmba
              have hmeq : Mailbox.empty = mba := Option.some.inj hmba; subst hmeq
              simp [Mailbox.empty] at hea
            · simp only [upd, if_neg h1] at hmba; exact hmba
        have hmbb' : s.mailboxes b = some mbb := by
          cases hm : s.mailboxes a with
          | some _ => simp only [hm] at hmbb; exact hmbb
          | none =>
            simp only [hm] at hmbb
            by_cases h1 : b = a
            · subst h1; rw [upd_self] at hmbb
              have hmeq : Mailbox.empty = mbb := Option.some.inj hmbb; subst hmeq
              simp [Mailbox.empty] at heb
            · simp only [upd, if_neg h1] at hmbb; exact hmbb
        exact h.occ_disjoint ac b mba mbb hab hmba' hmbb' ea hea eb heb
      · -- owner_spawned (RFC 038): spawn writes taskOwner only at nextId
        intro u a' how
        by_cases hun : u = s.nextId
        · subst hun; exact ⟨.new, by simp [step, hrs, hts, upd_self]⟩
        · obtain ⟨st, hst⟩ := h.owner_spawned u a'
              (by simp only [step, hrs, hts, upd, if_neg hun, if_true] at how; exact how)
          exact ⟨st, by simp [step, hrs, hts, upd, if_neg hun, hst]⟩
      · -- parent_child_spawned (RFC 038): spawn doesn't write taskParent
        intro u p hp
        obtain ⟨st, hst⟩ := h.parent_child_spawned u p
              (by simp only [step, hrs, hts, if_true] at hp; exact hp)
        have hun : u ≠ s.nextId := fun he =>
          absurd (he ▸ hts) (by rw [hst]; simp)
        exact ⟨st, by simp [step, hrs, hts, upd, if_neg hun, hst]⟩
      · -- timed_has_deadline (RFC 040)
        intro u hu
        by_cases huf : u = s.nextId
        · subst huf; simp [step, hrs, hts] at hu
        · have htask : ((step s (.spawn a)).1).taskState u = s.taskState u := by
            simp [step, hrs, hts, upd, if_neg huf]
          obtain ⟨d, hd⟩ := h.timed_has_deadline u (htask ▸ hu)
          exact ⟨d, by simpa [step, hrs, hts] using hd⟩
      · -- deadline_is_timed (RFC 040)
        intro u d hd
        by_cases huf : u = s.nextId
        · subst huf
          have := h.deadline_is_timed s.nextId d (by simpa [step, hrs, hts] using hd)
          rw [hts] at this; cases this
        · have hwait : ((step s (.spawn a)).1).waitDeadline u = s.waitDeadline u := by
            simp only [step, hrs, hts, if_true]
          have hback := h.deadline_is_timed u d (hwait ▸ hd)
          have htask : s.taskState u = ((step s (.spawn a)).1).taskState u := by
            simp [step, hrs, hts, upd, if_neg huf]
          exact htask ▸ hback
      · -- timed_has_timer (RFC 040)
        intro u hu
        by_cases huf : u = s.nextId
        · subst huf; simp [step, hrs, hts] at hu
        · have htask : ((step s (.spawn a)).1).taskState u = s.taskState u := by
            simp [step, hrs, hts, upd, if_neg huf]
          obtain ⟨e, he, hek⟩ := h.timed_has_timer u (htask ▸ hu)
          exact ⟨e, by simpa [step, hrs, hts] using he, hek⟩
      · -- timed_is_waiter (RFC 040)
        intro u hu
        by_cases huf : u = s.nextId
        · subst huf; simp [step, hrs, hts] at hu
        · have htask : ((step s (.spawn a)).1).taskState u = s.taskState u := by
            simp [step, hrs, hts, upd, if_neg huf]
          obtain ⟨b, hb⟩ := h.timed_is_waiter u (htask ▸ hu)
          exact ⟨b, by simpa [step, hrs, hts] using hb⟩
      · -- timed_waiters_valid (RFC 040)
        intro b u hu
        by_cases huf : u = s.nextId
        · subst huf
          simp only [step, hrs, hts, if_true] at hu
          exact absurd (h.timed_waiters_valid b s.nextId hu) (by rw [hts]; simp)
        · have htimedw : ((step s (.spawn a)).1).timedMailboxWaiters b = s.timedMailboxWaiters b := by
            simp only [step, hrs, hts, if_true]
          have hval := h.timed_waiters_valid b u (htimedw ▸ hu)
          have htask : s.taskState u = ((step s (.spawn a)).1).taskState u := by
            simp [step, hrs, hts, upd, if_neg huf]
          exact htask ▸ hval
      · -- timed_waiters_nodup (RFC 040)
        intro b; simp [step, hrs, hts]; exact h.timed_waiters_nodup b
      · -- timed_waiters_exclusive (RFC 040)
        intro a' b' u hab' hma hmb'
        exact h.timed_waiters_exclusive a' b' u hab'
          (by simpa [step, hrs, hts] using hma) (by simpa [step, hrs, hts] using hmb')
      · -- mailbox_within_capacity (RFC 056): spawn adds at most an empty mailbox for `a`
        intro a' n mbx hcap hmbx
        cases hmb0 : s.mailboxes a with
        | some mba =>
          simp only [step, hrs, hts, hmb0, if_true] at hcap hmbx
          exact h.mailbox_within_capacity a' n mbx hcap hmbx
        | none =>
          simp only [step, hrs, hts, hmb0, if_true] at hcap hmbx
          by_cases ha' : a' = a
          · subst ha'; simp only [upd_self] at hmbx
            injection hmbx with hmeq; subst hmeq; simp [Mailbox.empty]
          · simp only [upd, if_neg ha'] at hmbx
            exact h.mailbox_within_capacity a' n mbx hcap hmbx

  · simpa [step, hrs] using h
theorem preserves_wf_schedule (h : WellFormed s) :
    WellFormed ((step s .schedule).1) := by
  cases hr : s.running with
  | some _ => simpa [step, hr] using h
  | none =>
    cases hq : s.readyQ with
    | nil => simpa [step, hr, hq] using h
    | cons t q =>
      by_cases hrun : (s.taskState t).any TaskState.isRunnable = true
      · have hnodup := h.readyQ_nodup; rw [hq, List.nodup_cons] at hnodup
        have htsome : ∃ x, s.taskState t = some x := by
          cases hto : s.taskState t with
          | none => rw [hto] at hrun; simp [Option.any] at hrun
          | some x => exact ⟨x, rfl⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [step, hr, hq, if_pos hrun]; exact hnodup.2
        · intro u hm
          simp only [step, hr, hq, if_pos hrun] at hm ⊢
          have hu : u ≠ t := fun he => hnodup.1 (he ▸ hm)
          simp only [upd, if_neg hu]
          exact h.readyQ_queued u (by rw [hq]; exact List.mem_cons_of_mem t hm)
        · intro u hru
          simp only [step, hr, hq, if_pos hrun] at hru ⊢; cases hru; simp [upd]
        · simp only [step, hr, hq, if_pos hrun]; exact h.timers_nodup
        · intro e he
          simp only [step, hr, hq, if_pos hrun] at he ⊢
          rcases h.timers_sleep e he with h1 | h1
          · have hu : e.task ≠ t := fun heq => by
              rw [heq] at h1; rw [h1] at hrun; simp [Option.any, TaskState.isRunnable] at hrun
            exact Or.inl (by simp only [upd, if_neg hu]; exact h1)
          · have hu : e.task ≠ t := fun heq => by
              rw [heq] at h1; rw [h1] at hrun; simp [Option.any, TaskState.isRunnable] at hrun
            exact Or.inr (by simp only [upd, if_neg hu]; exact h1)
        · intro u hu
          simp only [step, hr, hq, if_pos hrun] at hu ⊢
          obtain ⟨x, hx⟩ := htsome
          have h1 : u ≠ t := fun he => by
            rw [← he] at hx; rw [h.fresh_none u hu] at hx; cases hx
          simp only [upd, if_neg h1]; exact h.fresh_none u hu
        · simp only [step, hr, hq, if_pos hrun]; exact h.timers_sorted
        · intro u st hts'
          simp only [step, hr, hq, if_pos hrun] at hts' ⊢
          by_cases hu : u = t
          · subst hu; obtain ⟨x, hx⟩ := htsome; exact h.spawned_has_owner u x hx
          · simp only [upd, if_neg hu] at hts'; exact h.spawned_has_owner u st hts'
        · intro u b hown
          simp only [step, hr, hq, if_pos hrun] at hown ⊢
          exact h.owned_has_mailbox u b hown
        · intro u st hts' hrun'
          simp only [step, hr, hq, if_pos hrun] at hts' ⊢
          by_cases hu : u = t
          · subst hu; simp only [upd_self] at hts'; cases hts'
            simp [TaskState.isRunnable] at hrun'
          · simp only [upd, if_neg hu] at hts'
            have hmem := h.runnable_queued u st hts' hrun'
            rw [hq, List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact absurd rfl hu
            · exact hmem
        · -- waiters_waiting (RFC 031)
          intro a u hm; simp only [step, hr, hq, if_pos hrun] at hm ⊢
          obtain ⟨x, hx⟩ := htsome
          have hts_u := h.waiters_waiting a u hm
          by_cases hut : u = t
          · subst hut; simp_all [Option.any, TaskState.isRunnable]
          · simp only [upd, if_neg hut]; exact hts_u
        · -- waiters_owned (RFC 031)
          intro a u hm; simp only [step, hr, hq, if_pos hrun] at hm ⊢
          have ho := h.waiters_owned a u hm
          have hts_u := h.waiters_waiting a u hm
          obtain ⟨x, hx⟩ := htsome
          by_cases hut : u = t
          · subst hut; simp_all [Option.any, TaskState.isRunnable]
          · exact ho
        · -- waiting_queued (RFC 031)
          intro u hts'; simp only [step, hr, hq, if_pos hrun] at hts' ⊢
          by_cases hut : u = t
          · subst hut; simp only [upd_self] at hts'; cases hts'
          · simp only [upd, if_neg hut] at hts'
            exact h.waiting_queued u hts'
        · -- waiters_nodup (RFC 031)
          intro a; simp only [step, hr, hq, if_pos hrun]
          exact h.waiters_nodup a
        · -- parent_lt (RFC 042)
          intro u p hp
          exact wf_parent_lt_pass h (by simp [step, hr, hq, if_pos hrun]) u p hp
        · -- parent_spawned (RFC 042)
          intro u p hp
          obtain ⟨st, hst⟩ := h.parent_spawned u p (by simpa [step, hr, hq, if_pos hrun] using hp)
          exact step_preserves_spawned hst _
        · -- occ_fresh (RFC 042)
          intro a mb env hmb henv
          exact wf_occ_fresh_pass h (by simp [step, hr, hq, if_pos hrun]) (by simp [step, hr, hq, if_pos hrun]) a mb env hmb henv
        · -- occ_nodup (RFC 042)
          intro a mb hmb
          exact wf_occ_nodup_pass h (by simp [step, hr, hq, if_pos hrun]) a mb hmb
        · -- occ_disjoint (RFC 042)
          intro a b mba mbb hab hmba hmbb ea hea eb heb
          exact wf_occ_disjoint_pass h (by simp [step, hr, hq, if_pos hrun]) a b mba mbb hab hmba hmbb ea hea eb heb
        · -- owner_spawned (RFC 038): taskOwner unchanged by schedule
          intro u a' how
          obtain ⟨st, hst⟩ := h.owner_spawned u a'
            (by simp only [step, hr, hq, if_pos hrun] at how; exact how)
          exact step_preserves_spawned hst _
        · -- parent_child_spawned (RFC 038): taskParent unchanged by schedule
          intro u p hp
          obtain ⟨st, hst⟩ := h.parent_child_spawned u p
            (by simp only [step, hr, hq, if_pos hrun] at hp; exact hp)
          exact step_preserves_spawned hst _
        · -- timed_has_deadline (RFC 040)
          intro u hu
          by_cases huf : u = t
          · subst huf; simp [step, hr, hq, if_pos hrun] at hu
          · have htask : ((step s .schedule).1).taskState u = s.taskState u := by
              simp [step, hr, hq, if_pos hrun, upd, if_neg huf]
            obtain ⟨d, hd⟩ := h.timed_has_deadline u (htask ▸ hu)
            exact ⟨d, by simpa [step, hr, hq, if_pos hrun] using hd⟩
        · -- deadline_is_timed (RFC 040)
          intro u d hd
          by_cases huf : u = t
          · have hwait : ((step s .schedule).1).waitDeadline u = s.waitDeadline u := by
              simp only [step, hr, hq, if_pos hrun]
            have hval := h.deadline_is_timed u d (hwait ▸ hd)
            rw [huf] at hval; rw [hval] at hrun
            simp [Option.any, TaskState.isRunnable] at hrun
          · have hwait : ((step s .schedule).1).waitDeadline u = s.waitDeadline u := by
              simp [step, hr, hq, if_pos hrun, upd, if_neg huf]
            have hback := h.deadline_is_timed u d (hwait ▸ hd)
            have htask : s.taskState u = ((step s .schedule).1).taskState u := by
              simp [step, hr, hq, if_pos hrun, upd, if_neg huf]
            exact htask ▸ hback
        · -- timed_has_timer (RFC 040)
          intro u hu
          by_cases huf : u = t
          · subst huf; simp [step, hr, hq, if_pos hrun] at hu
          · have htask : ((step s .schedule).1).taskState u = s.taskState u := by
              simp [step, hr, hq, if_pos hrun, upd, if_neg huf]
            obtain ⟨e, he, hek⟩ := h.timed_has_timer u (htask ▸ hu)
            exact ⟨e, by simpa [step, hr, hq, if_pos hrun] using he, hek⟩
        · -- timed_is_waiter (RFC 040)
          intro u hu
          by_cases huf : u = t
          · subst huf; simp [step, hr, hq, if_pos hrun] at hu
          · have htask : ((step s .schedule).1).taskState u = s.taskState u := by
              simp [step, hr, hq, if_pos hrun, upd, if_neg huf]
            obtain ⟨b, hb⟩ := h.timed_is_waiter u (htask ▸ hu)
            exact ⟨b, by simpa [step, hr, hq, if_pos hrun] using hb⟩
        · -- timed_waiters_valid (RFC 040)
          intro b u hu
          by_cases huf : u = t
          · simp only [step, hr, hq, if_pos hrun] at hu
            have := h.timed_waiters_valid b u hu
            rw [huf] at this; rw [this] at hrun
            simp [Option.any, TaskState.isRunnable] at hrun
          · have htimedw : ((step s .schedule).1).timedMailboxWaiters b = s.timedMailboxWaiters b := by
              simp only [step, hr, hq, if_pos hrun]
            have hval := h.timed_waiters_valid b u (htimedw ▸ hu)
            have htask : s.taskState u = ((step s .schedule).1).taskState u := by
              simp [step, hr, hq, if_pos hrun, upd, if_neg huf]
            exact htask ▸ hval
        · -- timed_waiters_nodup (RFC 040)
          intro b; simp [step, hr, hq, if_pos hrun]; exact h.timed_waiters_nodup b
        · -- timed_waiters_exclusive (RFC 040)
          intro a' b' u hab' hma hmb'
          exact h.timed_waiters_exclusive a' b' u hab'
            (by simpa [step, hr, hq, if_pos hrun] using hma)
            (by simpa [step, hr, hq, if_pos hrun] using hmb')
        · -- mailbox_within_capacity (RFC 056): schedule touches neither mailboxes nor policy
          intro a' n mbx hcap hmbx
          exact h.mailbox_within_capacity a' n mbx
            (by simpa [step, hr, hq, if_pos hrun] using hcap)
            (by simpa [step, hr, hq, if_pos hrun] using hmbx)

      · simp at hrun; simpa [step, hr, hq, hrun] using h

theorem preserves_wf_yield (h : WellFormed s) :
    WellFormed ((step s (.yield t)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some s' =>
      cases s' with
      | running =>
        have hnq : t ∉ s.readyQ := fun hm => by
          have h1 := h.readyQ_queued t hm; rw [hts] at h1
          simp [Option.any, TaskState.isRunnable] at h1
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [step, hrt, hts, if_pos rfl]; simp only [if_pos]
          exact nodup_append_singleton h.readyQ_nodup hnq
        · intro u hm
          simp [step, hrt, hts] at hm ⊢
          rcases hm with hm | rfl
          · have hu : u ≠ t := fun he => hnq (he ▸ hm)
            simp only [upd, if_neg hu]; exact h.readyQ_queued u hm
          · simp [upd, Option.any, TaskState.isRunnable]
        · intro u hru; simp [step, hrt, hts] at hru
        · simp only [step]; simp [hrt, hts]; exact h.timers_nodup
        · intro e he
          simp [step, hrt, hts] at he ⊢
          rcases h.timers_sleep e he with h1 | h1
          · have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
            exact Or.inl (by simp only [upd, if_neg hu]; exact h1)
          · have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
            exact Or.inr (by simp only [upd, if_neg hu]; exact h1)
        · intro u hu
          simp [step, hrt, hts] at hu ⊢
          have h1 : u ≠ t := fun he => by
            rw [← he] at hts; rw [h.fresh_none u hu] at hts; cases hts
          simp only [upd, if_neg h1]; exact h.fresh_none u hu
        · simp [step, hrt, hts]; exact h.timers_sorted
        · intro u st hts'
          simp [step, hrt, hts] at hts' ⊢
          by_cases hu : u = t
          · subst hu; exact h.spawned_has_owner u .running hts
          · simp only [upd, if_neg hu] at hts'; exact h.spawned_has_owner u st hts'
        · intro u b hown
          simp [step, hrt, hts] at hown ⊢; exact h.owned_has_mailbox u b hown
        · intro u st hts' hrun
          simp [step, hrt, hts] at hts' ⊢
          by_cases hu : u = t
          · subst hu; exact Or.inr rfl
          · simp only [upd, if_neg hu] at hts'
            exact Or.inl (h.runnable_queued u st hts' hrun)
        · -- waiters_waiting (RFC 031)
          intro a u hm; simp [step, hrt, hts] at hm ⊢
          have hts_u := h.waiters_waiting a u hm
          by_cases hut : u = t
          · subst hut; simp_all
          · simp only [upd, if_neg hut]; exact hts_u
        · -- waiters_owned (RFC 031)
          intro a u hm; simp [step, hrt, hts] at hm ⊢
          have hts_u := h.waiters_waiting a u hm
          by_cases hut : u = t
          · subst hut; simp_all
          · exact h.waiters_owned a u hm
        · -- waiting_queued (RFC 031)
          intro u hts'; simp [step, hrt, hts] at hts' ⊢
          by_cases hut : u = t
          · subst hut; simp only [upd_self] at hts'; cases hts'
          · simp only [upd, if_neg hut] at hts'
            exact h.waiting_queued u hts'
        · -- waiters_nodup (RFC 031)
          intro a; simp [step, hrt, hts]
          exact h.waiters_nodup a
        · -- parent_lt (RFC 042)
          intro u p hp
          exact wf_parent_lt_pass h (by simp [step, hrt, hts]) u p hp
        · -- parent_spawned (RFC 042)
          intro u p hp
          obtain ⟨st, hst⟩ := h.parent_spawned u p (by simpa [step, hrt, hts] using hp)
          exact step_preserves_spawned hst _
        · -- occ_fresh (RFC 042)
          intro a mb env hmb henv
          exact wf_occ_fresh_pass h (by simp [step, hrt, hts]) (by simp [step, hrt, hts]) a mb env hmb henv
        · -- occ_nodup (RFC 042)
          intro a mb hmb
          exact wf_occ_nodup_pass h (by simp [step, hrt, hts]) a mb hmb
        · -- occ_disjoint (RFC 042)
          intro a b mba mbb hab hmba hmbb ea hea eb heb
          exact wf_occ_disjoint_pass h (by simp [step, hrt, hts]) a b mba mbb hab hmba hmbb ea hea eb heb
        · -- owner_spawned (RFC 038): taskOwner unchanged by yield
          intro u a' how
          obtain ⟨st, hst⟩ := h.owner_spawned u a'
            (by simp only [step, hrt, hts] at how; exact how)
          exact step_preserves_spawned hst _
        · -- parent_child_spawned (RFC 038): taskParent unchanged by yield
          intro u p hp
          obtain ⟨st, hst⟩ := h.parent_child_spawned u p
            (by simp only [step, hrt, hts] at hp; exact hp)
          exact step_preserves_spawned hst _
        · -- timed_has_deadline (RFC 040)
          intro u hu
          by_cases huf : u = t
          · subst huf; simp [step, hrt, hts, upd_self] at hu
          · have htask : ((step s (.yield t)).1).taskState u = s.taskState u := by
              simp [step, hrt, hts, upd, if_neg huf]
            obtain ⟨d, hd⟩ := h.timed_has_deadline u (htask ▸ hu)
            exact ⟨d, by simpa [step, hrt, hts] using hd⟩
        · -- deadline_is_timed (RFC 040)
          intro u d hd
          by_cases huf : u = t
          · have hwait : ((step s (.yield t)).1).waitDeadline u = s.waitDeadline u := by
              simp [step, hrt, hts]
            have hval := h.deadline_is_timed u d (hwait ▸ hd)
            rw [huf] at hval; rw [hval] at hts; cases hts
          · have hwait : ((step s (.yield t)).1).waitDeadline u = s.waitDeadline u := by
              simp [step, hrt, hts, upd, if_neg huf]
            have hback := h.deadline_is_timed u d (hwait ▸ hd)
            have htask : s.taskState u = ((step s (.yield t)).1).taskState u := by
              simp [step, hrt, hts, upd, if_neg huf]
            exact htask ▸ hback
        · -- timed_has_timer (RFC 040)
          intro u hu
          by_cases huf : u = t
          · subst huf; simp [step, hrt, hts, upd_self] at hu
          · have htask : ((step s (.yield t)).1).taskState u = s.taskState u := by
              simp [step, hrt, hts, upd, if_neg huf]
            obtain ⟨e, he, hek⟩ := h.timed_has_timer u (htask ▸ hu)
            exact ⟨e, by simpa [step, hrt, hts] using he, hek⟩
        · -- timed_is_waiter (RFC 040)
          intro u hu
          by_cases huf : u = t
          · subst huf; simp [step, hrt, hts, upd_self] at hu
          · have htask : ((step s (.yield t)).1).taskState u = s.taskState u := by
              simp [step, hrt, hts, upd, if_neg huf]
            obtain ⟨b, hb⟩ := h.timed_is_waiter u (htask ▸ hu)
            exact ⟨b, by simpa [step, hrt, hts] using hb⟩
        · -- timed_waiters_valid (RFC 040)
          intro b u hu
          by_cases huf : u = t
          · simp only [step, hrt, hts] at hu
            have := h.timed_waiters_valid b u hu
            -- u = t (huf), s.taskState t = .running (hts); .waitingTimed ≠ .running
            rw [huf] at this; exact absurd (hts.symm.trans this) (by decide)
          · have htimedw : ((step s (.yield t)).1).timedMailboxWaiters b = s.timedMailboxWaiters b := by
              simp [step, hrt, hts]
            have hval := h.timed_waiters_valid b u (htimedw ▸ hu)
            have htask : s.taskState u = ((step s (.yield t)).1).taskState u := by
              simp [step, hrt, hts, upd, if_neg huf]
            exact htask ▸ hval
        · -- timed_waiters_nodup (RFC 040)
          intro b; simp [step, hrt, hts]; exact h.timed_waiters_nodup b
        · -- timed_waiters_exclusive (RFC 040)
          intro a' b' u hab' hma hmb'
          exact h.timed_waiters_exclusive a' b' u hab'
            (by simpa [step, hrt, hts] using hma) (by simpa [step, hrt, hts] using hmb')
        · -- mailbox_within_capacity (RFC 056): yield touches neither mailboxes nor policy
          intro a' n mbx hcap hmbx
          exact h.mailbox_within_capacity a' n mbx
            (by simpa [step, hrt, hts] using hcap) (by simpa [step, hrt, hts] using hmbx)

      | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting | failed =>
        simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h

theorem preserves_wf_complete (h : WellFormed s) :
    WellFormed ((step s (.complete t)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some s' =>
      cases s' with
      | running =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [step, hrt, hts]; exact h.readyQ_nodup
        · intro u hm
          simp [step, hrt, hts] at hm ⊢
          have h1 := h.readyQ_queued u hm
          have hu : u ≠ t := fun he => by
            rw [he, hts] at h1; simp [Option.any, TaskState.isRunnable] at h1
          simp only [upd, if_neg hu]; exact h1
        · intro u hru; simp [step, hrt, hts] at hru
        · simp [step, hrt, hts]; exact h.timers_nodup
        · intro e he
          simp [step, hrt, hts] at he ⊢
          rcases h.timers_sleep e he with h1 | h1
          · have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
            exact Or.inl (by simp only [upd, if_neg hu]; exact h1)
          · have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
            exact Or.inr (by simp only [upd, if_neg hu]; exact h1)
        · intro u hu
          simp [step, hrt, hts] at hu ⊢
          have h1 : u ≠ t := fun he => by
            rw [← he] at hts; rw [h.fresh_none u hu] at hts; cases hts
          simp only [upd, if_neg h1]; exact h.fresh_none u hu
        · simp [step, hrt, hts]; exact h.timers_sorted
        · intro u st hts'
          simp [step, hrt, hts] at hts' ⊢
          by_cases hu : u = t
          · subst hu; exact h.spawned_has_owner u .running hts
          · simp only [upd, if_neg hu] at hts'; exact h.spawned_has_owner u st hts'
        · intro u b hown
          simp [step, hrt, hts] at hown ⊢; exact h.owned_has_mailbox u b hown
        · intro u st hts' hrun
          simp [step, hrt, hts] at hts' ⊢
          by_cases hu : u = t
          · subst hu; simp only [upd_self] at hts'; cases hts'
            simp [TaskState.isRunnable] at hrun
          · simp only [upd, if_neg hu] at hts'
            exact h.runnable_queued u st hts' hrun
        · -- waiters_waiting (RFC 031)
          intro a u hm; simp [step, hrt, hts] at hm ⊢
          have hts_u := h.waiters_waiting a u hm
          by_cases hut : u = t
          · subst hut; simp_all
          · simp only [upd, if_neg hut]; exact hts_u
        · -- waiters_owned (RFC 031)
          intro a u hm; simp [step, hrt, hts] at hm ⊢
          have hts_u := h.waiters_waiting a u hm
          by_cases hut : u = t
          · subst hut; simp_all
          · exact h.waiters_owned a u hm
        · -- waiting_queued (RFC 031)
          intro u hts'; simp [step, hrt, hts] at hts' ⊢
          by_cases hut : u = t
          · subst hut; simp only [upd_self] at hts'; cases hts'
          · simp only [upd, if_neg hut] at hts'
            exact h.waiting_queued u hts'
        · -- waiters_nodup (RFC 031)
          intro a; simp [step, hrt, hts]
          exact h.waiters_nodup a
        · -- parent_lt (RFC 042)
          intro u p hp
          exact wf_parent_lt_pass h (by simp [step, hrt, hts]) u p hp
        · -- parent_spawned (RFC 032)
          intro u p hp
          have hpar : s.taskParent u = some p := by simp only [step, hrt, hts] at hp; exact hp
          obtain ⟨st, hst⟩ := h.parent_spawned u p hpar
          by_cases hpt : p = t
          · exact ⟨.completed, by simp [step, hrt, hts, upd_self, hpt]⟩
          · exact ⟨st, by simp [step, hrt, hts, upd, if_neg hpt]; exact hst⟩
        · -- occ_fresh (RFC 042)
          intro a mb env hmb henv
          exact wf_occ_fresh_pass h (by simp [step, hrt, hts]) (by simp [step, hrt, hts]) a mb env hmb henv
        · -- occ_nodup (RFC 042)
          intro a mb hmb
          exact wf_occ_nodup_pass h (by simp [step, hrt, hts]) a mb hmb
        · -- occ_disjoint (RFC 042)
          intro a b mba mbb hab hmba hmbb ea hea eb heb
          exact wf_occ_disjoint_pass h (by simp [step, hrt, hts]) a b mba mbb hab hmba hmbb ea hea eb heb
        · -- owner_spawned (RFC 038): taskOwner unchanged by complete
          intro u a' how
          obtain ⟨st, hst⟩ := h.owner_spawned u a'
            (by simp only [step, hrt, hts] at how; exact how)
          exact step_preserves_spawned hst _
        · -- parent_child_spawned (RFC 038): taskParent unchanged by complete
          intro u p hp
          obtain ⟨st, hst⟩ := h.parent_child_spawned u p
            (by simp only [step, hrt, hts] at hp; exact hp)
          exact step_preserves_spawned hst _
        · -- timed_has_deadline (RFC 040)
          intro u hu
          by_cases huf : u = t
          · subst huf; simp [step, hrt, hts, upd_self] at hu
          · have htask : ((step s (.complete t)).1).taskState u = s.taskState u := by
              simp [step, hrt, hts, upd, if_neg huf]
            obtain ⟨d, hd⟩ := h.timed_has_deadline u (htask ▸ hu)
            exact ⟨d, by simpa [step, hrt, hts] using hd⟩
        · -- deadline_is_timed (RFC 040)
          intro u d hd
          by_cases huf : u = t
          · have hwait : ((step s (.complete t)).1).waitDeadline u = s.waitDeadline u := by
              simp [step, hrt, hts]
            have hval := h.deadline_is_timed u d (hwait ▸ hd)
            rw [huf] at hval; rw [hval] at hts; cases hts
          · have hwait : ((step s (.complete t)).1).waitDeadline u = s.waitDeadline u := by
              simp [step, hrt, hts, upd, if_neg huf]
            have hback := h.deadline_is_timed u d (hwait ▸ hd)
            have htask : s.taskState u = ((step s (.complete t)).1).taskState u := by
              simp [step, hrt, hts, upd, if_neg huf]
            exact htask ▸ hback
        · -- timed_has_timer (RFC 040)
          intro u hu
          by_cases huf : u = t
          · subst huf; simp [step, hrt, hts, upd_self] at hu
          · have htask : ((step s (.complete t)).1).taskState u = s.taskState u := by
              simp [step, hrt, hts, upd, if_neg huf]
            obtain ⟨e, he, hek⟩ := h.timed_has_timer u (htask ▸ hu)
            exact ⟨e, by simpa [step, hrt, hts] using he, hek⟩
        · -- timed_is_waiter (RFC 040)
          intro u hu
          by_cases huf : u = t
          · subst huf; simp [step, hrt, hts, upd_self] at hu
          · have htask : ((step s (.complete t)).1).taskState u = s.taskState u := by
              simp [step, hrt, hts, upd, if_neg huf]
            obtain ⟨b, hb⟩ := h.timed_is_waiter u (htask ▸ hu)
            exact ⟨b, by simpa [step, hrt, hts] using hb⟩
        · -- timed_waiters_valid (RFC 040)
          intro b u hu
          by_cases huf : u = t
          · simp only [step, hrt, hts] at hu
            have := h.timed_waiters_valid b u hu
            -- u = t (huf), s.taskState t = .running (hts); .waitingTimed ≠ .running
            rw [huf] at this; exact absurd (hts.symm.trans this) (by decide)
          · have htimedw : ((step s (.complete t)).1).timedMailboxWaiters b = s.timedMailboxWaiters b := by
              simp [step, hrt, hts]
            have hval := h.timed_waiters_valid b u (htimedw ▸ hu)
            have htask : s.taskState u = ((step s (.complete t)).1).taskState u := by
              simp [step, hrt, hts, upd, if_neg huf]
            exact htask ▸ hval
        · -- timed_waiters_nodup (RFC 040)
          intro b; simp [step, hrt, hts]; exact h.timed_waiters_nodup b
        · -- timed_waiters_exclusive (RFC 040)
          intro a' b' u hab' hma hmb'
          exact h.timed_waiters_exclusive a' b' u hab'
            (by simpa [step, hrt, hts] using hma) (by simpa [step, hrt, hts] using hmb')
        · -- mailbox_within_capacity (RFC 056): complete touches neither mailboxes nor policy
          intro a' n mbx hcap hmbx
          exact h.mailbox_within_capacity a' n mbx
            (by simpa [step, hrt, hts] using hcap) (by simpa [step, hrt, hts] using hmbx)

      | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting | failed =>
        simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h

theorem preserves_wf_cancel (h : WellFormed s) :
    WellFormed ((step s (.cancel t)).1) := by
  cases hts : s.taskState t with
  | none => simpa [step, hts] using h
  | some s' =>
    by_cases hterm : s'.isTerminal = true
    · simpa [step, hts, hterm] using h
    · simp at hterm
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [step, hts, hterm]; exact h.readyQ_nodup.filter _
      · intro u hm
        simp [step, hts, hterm] at hm ⊢
        obtain ⟨hm, hu⟩ := hm
        simp only [upd, if_neg hu]; exact h.readyQ_queued u hm
      · intro u hru
        simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hru ⊢
        by_cases hcase : s.running = some t
        · rw [if_pos hcase] at hru; cases hru
        · rw [if_neg hcase] at hru
          have h1 := h.running_runs u hru
          have hu : u ≠ t := fun he => hcase (he ▸ hru)
          simp only [upd, if_neg hu]; exact h1
      · simp [step, hts, hterm]
        exact nodup_of_sublist
          (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup
      · intro e he
        simp [step, hts, hterm] at he ⊢
        obtain ⟨he, hu⟩ := he
        rcases h.timers_sleep e he with h1 | h1
        · exact Or.inl (by simp only [upd, if_neg hu]; exact h1)
        · exact Or.inr (by simp only [upd, if_neg hu]; exact h1)
      · intro u hu
        simp [step, hts, hterm] at hu ⊢
        have h1 : u ≠ t := fun he => by
          rw [← he] at hts; rw [h.fresh_none u hu] at hts; cases hts
        simp only [upd, if_neg h1]; exact h.fresh_none u hu
      · simp [step, hts, hterm]; exact Timer.sorted_filter _ h.timers_sorted
      · intro u st hts'
        simp [step, hts, hterm] at hts' ⊢
        by_cases hu : u = t
        · subst hu; exact h.spawned_has_owner u s' hts
        · simp only [upd, if_neg hu] at hts'; exact h.spawned_has_owner u st hts'
      · intro u b hown
        simp [step, hts, hterm] at hown ⊢; exact h.owned_has_mailbox u b hown
      · intro u st hts' hrun
        simp [step, hts, hterm] at hts' ⊢
        by_cases hu : u = t
        · subst hu; simp only [upd_self] at hts'; cases hts'
          simp [TaskState.isRunnable] at hrun
        · simp only [upd, if_neg hu] at hts'
          exact ⟨h.runnable_queued u st hts' hrun, hu⟩
      · -- waiters_waiting (RFC 031)
        intro a u hm
        simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hm ⊢
        cases hown : s.taskOwner t with
        | none =>
          -- t has no owner → t is not in any waiter list → u ≠ t
          simp only [hown] at hm ⊢
          have ho := h.waiters_owned a u hm
          have hut : u ≠ t := by
            intro he
            have ho := h.waiters_owned a u hm
            rw [he, hown] at ho; cases ho
          simp only [upd, if_neg hut]
          exact h.waiters_waiting a u hm
        | some oa =>
          simp only [hown] at hm ⊢
          by_cases hao : a = oa
          · subst hao; simp only [if_pos rfl] at hm ⊢
            have hmem := (List.mem_filter.mp hm).1
            have hut : u ≠ t := by
              intro he
              have := (List.mem_filter.mp hm).2
              simp [he, decide_eq_true_eq] at this
            have hts_u := h.waiters_waiting a u hmem
            simp only [upd, if_neg hut]; exact hts_u
          · simp only [if_neg hao] at hm ⊢
            have hts_u := h.waiters_waiting a u hm
            have hut : u ≠ t := by
              intro he
              have ho := h.waiters_owned a u hm
              rw [he, hown] at ho
              exact absurd (Option.some.inj ho).symm hao
            simp only [upd, if_neg hut]; exact hts_u
      · -- waiters_owned (RFC 031)
        intro a u hm
        simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hm ⊢
        cases hown : s.taskOwner t with
        | none =>
          simp only [hown] at hm ⊢
          exact h.waiters_owned a u hm
        | some oa =>
          simp only [hown] at hm ⊢
          by_cases hao : a = oa
          · subst hao; simp only [if_pos rfl] at hm ⊢
            exact h.waiters_owned a u (List.mem_filter.mp hm).1
          · simp only [if_neg hao] at hm ⊢
            exact h.waiters_owned a u hm
      · -- waiting_queued (RFC 031)
        intro u hts'
        simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hts' ⊢
        by_cases hut : u = t
        · subst hut; simp only [upd_self] at hts'; cases hts'
        · simp only [upd, if_neg hut] at hts'
          obtain ⟨a, ha, hmem⟩ := h.waiting_queued u hts'
          refine ⟨a, ha, ?_⟩
          cases hown : s.taskOwner t with
          | none => simp only [hown]; exact hmem
          | some oa =>
            simp only [hown]
            by_cases hao : a = oa
            · subst hao; simp only [if_pos rfl]
              exact List.mem_filter.mpr ⟨hmem, by simpa [decide_eq_true_eq] using hut⟩
            · simp only [if_neg hao]; exact hmem
      · -- waiters_nodup (RFC 031)
        intro a
        simp only [step, hts, hterm, Bool.false_eq_true, if_false]
        cases hown : s.taskOwner t with
        | none => simp only [hown]; exact h.waiters_nodup a
        | some oa =>
          simp only [hown]
          by_cases hao : a = oa
          · subst hao; simp only [if_pos rfl]
            exact (h.waiters_nodup a).filter _
          · simp only [if_neg hao]; exact h.waiters_nodup a
      · -- parent_lt (RFC 042)
        intro u p hp
        exact wf_parent_lt_pass h (by simp [step, hts, hterm, Bool.false_eq_true, if_false]) u p hp
      · -- parent_spawned (RFC 042)
        intro u p hp
        obtain ⟨st, hst⟩ := h.parent_spawned u p
          (by simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hp; exact hp)
        exact step_preserves_spawned hst _
      · -- occ_fresh (RFC 042)
        intro a mb env hmb henv
        exact wf_occ_fresh_pass h (by simp [step, hts, hterm, if_false]) (by simp [step, hts, hterm, if_false]) a mb env hmb henv
      · -- occ_nodup (RFC 042)
        intro a mb hmb
        exact wf_occ_nodup_pass h (by simp [step, hts, hterm, if_false]) a mb hmb
      · -- occ_disjoint (RFC 042)
        intro a b mba mbb hab hmba hmbb ea hea eb heb
        exact wf_occ_disjoint_pass h (by simp [step, hts, hterm, if_false]) a b mba mbb hab hmba hmbb ea hea eb heb
      · -- owner_spawned (RFC 038): taskOwner unchanged by cancel
        intro u a' how
        obtain ⟨st, hst⟩ := h.owner_spawned u a'
          (by simp [step, hts, hterm, if_false] at how; exact how)
        exact step_preserves_spawned hst _
      · -- parent_child_spawned (RFC 038): taskParent unchanged by cancel
        intro u p hp
        obtain ⟨st, hst⟩ := h.parent_child_spawned u p
          (by simp [step, hts, hterm, if_false] at hp; exact hp)
        exact step_preserves_spawned hst _
      · -- timed_has_deadline (RFC 040)
        intro u hu
        by_cases huf : u = t
        · subst huf; simp [step, hts, hterm] at *
        · have htask : ((step s (.cancel t)).1).taskState u = s.taskState u := by
            simp [step, hts, hterm, if_false, upd, if_neg huf]
          obtain ⟨d, hd⟩ := h.timed_has_deadline u (htask ▸ hu)
          refine ⟨d, ?_⟩
          -- waitDeadline u after cancel = if u = t then none else s.waitDeadline u
          simp only [step, hts, hterm, Bool.false_eq_true, if_false]
          rw [if_neg huf]; exact hd
      · -- deadline_is_timed (RFC 040)
        intro u d hd
        by_cases huf : u = t
        · -- cancel sets waitDeadline t = none; with huf:u=t, none=some d → False
          simp [step, hts, hterm, if_false, huf] at hd
        · have hwait : ((step s (.cancel t)).1).waitDeadline u = s.waitDeadline u := by
            simp only [step, hts, hterm, Bool.false_eq_true, if_false]
            rw [if_neg huf]
          have hback := h.deadline_is_timed u d (hwait ▸ hd)
          have htask : s.taskState u = ((step s (.cancel t)).1).taskState u := by
            simp [step, hts, hterm, if_false, upd, if_neg huf]
          exact htask ▸ hback
      · -- timed_has_timer (RFC 040)
        intro u hu
        by_cases huf : u = t
        · subst huf; simp [step, hts, hterm] at *
        · have htask : ((step s (.cancel t)).1).taskState u = s.taskState u := by
            simp [step, hts, hterm, if_false, upd, if_neg huf]
          obtain ⟨e, he, hek⟩ := h.timed_has_timer u (htask ▸ hu)
          have hne : e.task ≠ t := hek ▸ huf
          refine ⟨e, ?_, hek⟩
          simp only [step, hts, hterm, Bool.false_eq_true, if_false]
          exact List.mem_filter.mpr ⟨he, by simp [hne]⟩
      · -- timed_is_waiter (RFC 040)
        intro u hu
        by_cases huf : u = t
        · subst huf; simp [step, hts, hterm] at *
        · have htask : ((step s (.cancel t)).1).taskState u = s.taskState u := by
            simp [step, hts, hterm, if_false, upd, if_neg huf]
          obtain ⟨b, hb⟩ := h.timed_is_waiter u (htask ▸ hu)
          refine ⟨b, ?_⟩
          -- New model: timedMailboxWaiters ac = filter (· ≠ t) ac; u ≠ t so u passes
          simp only [step, hts, hterm, Bool.false_eq_true, if_false]
          exact List.mem_filter.mpr ⟨hb, by simp [huf]⟩
      · -- timed_waiters_valid (RFC 040)
        intro b u hu
        by_cases huf : u = t
        · -- u = t: u is filtered out of timedMailboxWaiters by cancel
          subst huf
          -- hu : u ∈ (s.timedMailboxWaiters b).filter (· ≠ u) → False (filter excludes u)
          simp only [step, hts, hterm, Bool.false_eq_true, if_false, List.mem_filter,
                     decide_eq_true_eq, ne_eq, not_true, and_false] at hu
        · have hmem : u ∈ s.timedMailboxWaiters b := by
            simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hu
            exact (List.mem_filter.mp hu).1
          have hval := h.timed_waiters_valid b u hmem
          have htask : s.taskState u = ((step s (.cancel t)).1).taskState u := by
            simp [step, hts, hterm, if_false, upd, if_neg huf]
          exact htask ▸ hval
      · -- timed_waiters_nodup (RFC 040)
        intro b
        simp only [step, hts, hterm, Bool.false_eq_true, if_false]
        exact nodup_of_sublist (List.filter_sublist _) (h.timed_waiters_nodup b)
      · -- timed_waiters_exclusive (RFC 040): cancel filters t from all lists
        intro a' b' u hab' hma hmb'
        simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hma hmb'
        have hma' : u ∈ s.timedMailboxWaiters a' := (List.mem_filter.mp hma).1
        have hmb'' : u ∈ s.timedMailboxWaiters b' := (List.mem_filter.mp hmb').1
        exact h.timed_waiters_exclusive a' b' u hab' hma' hmb''
      · -- mailbox_within_capacity (RFC 056): cancel filters waiter lists, not mailboxes
        intro a' n mbx hcap hmbx
        exact h.mailbox_within_capacity a' n mbx
          (by simpa [step, hts, hterm, Bool.false_eq_true, if_false] using hcap)
          (by simpa [step, hts, hterm, Bool.false_eq_true, if_false] using hmbx)

-- Helper: key spawnChild proof patterns mirror spawn exactly
-- (spawnChild only adds taskParent; all other WF fields follow the same logic)

/-- `fail` preserves well-formedness (RFC 049). Mirrors `preserves_wf_cancel`:
    identical cleanup, terminal target `.failed` instead of `.cancelled`. -/
theorem preserves_wf_fail (h : WellFormed s) :
    WellFormed ((step s (.fail t)).1) := by
  cases hts : s.taskState t with
  | none => simpa [step, hts] using h
  | some s' =>
    by_cases hterm : s'.isTerminal = true
    · simpa [step, hts, hterm] using h
    · simp at hterm
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [step, hts, hterm]; exact h.readyQ_nodup.filter _
      · intro u hm
        simp [step, hts, hterm] at hm ⊢
        obtain ⟨hm, hu⟩ := hm
        simp only [upd, if_neg hu]; exact h.readyQ_queued u hm
      · intro u hru
        simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hru ⊢
        by_cases hcase : s.running = some t
        · rw [if_pos hcase] at hru; cases hru
        · rw [if_neg hcase] at hru
          have h1 := h.running_runs u hru
          have hu : u ≠ t := fun he => hcase (he ▸ hru)
          simp only [upd, if_neg hu]; exact h1
      · simp [step, hts, hterm]
        exact nodup_of_sublist
          (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup
      · intro e he
        simp [step, hts, hterm] at he ⊢
        obtain ⟨he, hu⟩ := he
        rcases h.timers_sleep e he with h1 | h1
        · exact Or.inl (by simp only [upd, if_neg hu]; exact h1)
        · exact Or.inr (by simp only [upd, if_neg hu]; exact h1)
      · intro u hu
        simp [step, hts, hterm] at hu ⊢
        have h1 : u ≠ t := fun he => by
          rw [← he] at hts; rw [h.fresh_none u hu] at hts; cases hts
        simp only [upd, if_neg h1]; exact h.fresh_none u hu
      · simp [step, hts, hterm]; exact Timer.sorted_filter _ h.timers_sorted
      · intro u st hts'
        simp [step, hts, hterm] at hts' ⊢
        by_cases hu : u = t
        · subst hu; exact h.spawned_has_owner u s' hts
        · simp only [upd, if_neg hu] at hts'; exact h.spawned_has_owner u st hts'
      · intro u b hown
        simp [step, hts, hterm] at hown ⊢; exact h.owned_has_mailbox u b hown
      · intro u st hts' hrun
        simp [step, hts, hterm] at hts' ⊢
        by_cases hu : u = t
        · subst hu; simp only [upd_self] at hts'; cases hts'
          simp [TaskState.isRunnable] at hrun
        · simp only [upd, if_neg hu] at hts'
          exact ⟨h.runnable_queued u st hts' hrun, hu⟩
      · -- waiters_waiting (RFC 031)
        intro a u hm
        simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hm ⊢
        cases hown : s.taskOwner t with
        | none =>
          -- t has no owner → t is not in any waiter list → u ≠ t
          simp only [hown] at hm ⊢
          have ho := h.waiters_owned a u hm
          have hut : u ≠ t := by
            intro he
            have ho := h.waiters_owned a u hm
            rw [he, hown] at ho; cases ho
          simp only [upd, if_neg hut]
          exact h.waiters_waiting a u hm
        | some oa =>
          simp only [hown] at hm ⊢
          by_cases hao : a = oa
          · subst hao; simp only [if_pos rfl] at hm ⊢
            have hmem := (List.mem_filter.mp hm).1
            have hut : u ≠ t := by
              intro he
              have := (List.mem_filter.mp hm).2
              simp [he, decide_eq_true_eq] at this
            have hts_u := h.waiters_waiting a u hmem
            simp only [upd, if_neg hut]; exact hts_u
          · simp only [if_neg hao] at hm ⊢
            have hts_u := h.waiters_waiting a u hm
            have hut : u ≠ t := by
              intro he
              have ho := h.waiters_owned a u hm
              rw [he, hown] at ho
              exact absurd (Option.some.inj ho).symm hao
            simp only [upd, if_neg hut]; exact hts_u
      · -- waiters_owned (RFC 031)
        intro a u hm
        simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hm ⊢
        cases hown : s.taskOwner t with
        | none =>
          simp only [hown] at hm ⊢
          exact h.waiters_owned a u hm
        | some oa =>
          simp only [hown] at hm ⊢
          by_cases hao : a = oa
          · subst hao; simp only [if_pos rfl] at hm ⊢
            exact h.waiters_owned a u (List.mem_filter.mp hm).1
          · simp only [if_neg hao] at hm ⊢
            exact h.waiters_owned a u hm
      · -- waiting_queued (RFC 031)
        intro u hts'
        simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hts' ⊢
        by_cases hut : u = t
        · subst hut; simp only [upd_self] at hts'; cases hts'
        · simp only [upd, if_neg hut] at hts'
          obtain ⟨a, ha, hmem⟩ := h.waiting_queued u hts'
          refine ⟨a, ha, ?_⟩
          cases hown : s.taskOwner t with
          | none => simp only [hown]; exact hmem
          | some oa =>
            simp only [hown]
            by_cases hao : a = oa
            · subst hao; simp only [if_pos rfl]
              exact List.mem_filter.mpr ⟨hmem, by simpa [decide_eq_true_eq] using hut⟩
            · simp only [if_neg hao]; exact hmem
      · -- waiters_nodup (RFC 031)
        intro a
        simp only [step, hts, hterm, Bool.false_eq_true, if_false]
        cases hown : s.taskOwner t with
        | none => simp only [hown]; exact h.waiters_nodup a
        | some oa =>
          simp only [hown]
          by_cases hao : a = oa
          · subst hao; simp only [if_pos rfl]
            exact (h.waiters_nodup a).filter _
          · simp only [if_neg hao]; exact h.waiters_nodup a
      · -- parent_lt (RFC 042)
        intro u p hp
        exact wf_parent_lt_pass h (by simp [step, hts, hterm, Bool.false_eq_true, if_false]) u p hp
      · -- parent_spawned (RFC 042)
        intro u p hp
        obtain ⟨st, hst⟩ := h.parent_spawned u p
          (by simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hp; exact hp)
        exact step_preserves_spawned hst _
      · -- occ_fresh (RFC 042)
        intro a mb env hmb henv
        exact wf_occ_fresh_pass h (by simp [step, hts, hterm, if_false]) (by simp [step, hts, hterm, if_false]) a mb env hmb henv
      · -- occ_nodup (RFC 042)
        intro a mb hmb
        exact wf_occ_nodup_pass h (by simp [step, hts, hterm, if_false]) a mb hmb
      · -- occ_disjoint (RFC 042)
        intro a b mba mbb hab hmba hmbb ea hea eb heb
        exact wf_occ_disjoint_pass h (by simp [step, hts, hterm, if_false]) a b mba mbb hab hmba hmbb ea hea eb heb
      · -- owner_spawned (RFC 038): taskOwner unchanged by cancel
        intro u a' how
        obtain ⟨st, hst⟩ := h.owner_spawned u a'
          (by simp [step, hts, hterm, if_false] at how; exact how)
        exact step_preserves_spawned hst _
      · -- parent_child_spawned (RFC 038): taskParent unchanged by cancel
        intro u p hp
        obtain ⟨st, hst⟩ := h.parent_child_spawned u p
          (by simp [step, hts, hterm, if_false] at hp; exact hp)
        exact step_preserves_spawned hst _
      · -- timed_has_deadline (RFC 040)
        intro u hu
        by_cases huf : u = t
        · subst huf; simp [step, hts, hterm] at *
        · have htask : ((step s (.fail t)).1).taskState u = s.taskState u := by
            simp [step, hts, hterm, if_false, upd, if_neg huf]
          obtain ⟨d, hd⟩ := h.timed_has_deadline u (htask ▸ hu)
          refine ⟨d, ?_⟩
          -- waitDeadline u after cancel = if u = t then none else s.waitDeadline u
          simp only [step, hts, hterm, Bool.false_eq_true, if_false]
          rw [if_neg huf]; exact hd
      · -- deadline_is_timed (RFC 040)
        intro u d hd
        by_cases huf : u = t
        · -- cancel sets waitDeadline t = none; with huf:u=t, none=some d → False
          simp [step, hts, hterm, if_false, huf] at hd
        · have hwait : ((step s (.fail t)).1).waitDeadline u = s.waitDeadline u := by
            simp only [step, hts, hterm, Bool.false_eq_true, if_false]
            rw [if_neg huf]
          have hback := h.deadline_is_timed u d (hwait ▸ hd)
          have htask : s.taskState u = ((step s (.fail t)).1).taskState u := by
            simp [step, hts, hterm, if_false, upd, if_neg huf]
          exact htask ▸ hback
      · -- timed_has_timer (RFC 040)
        intro u hu
        by_cases huf : u = t
        · subst huf; simp [step, hts, hterm] at *
        · have htask : ((step s (.fail t)).1).taskState u = s.taskState u := by
            simp [step, hts, hterm, if_false, upd, if_neg huf]
          obtain ⟨e, he, hek⟩ := h.timed_has_timer u (htask ▸ hu)
          have hne : e.task ≠ t := hek ▸ huf
          refine ⟨e, ?_, hek⟩
          simp only [step, hts, hterm, Bool.false_eq_true, if_false]
          exact List.mem_filter.mpr ⟨he, by simp [hne]⟩
      · -- timed_is_waiter (RFC 040)
        intro u hu
        by_cases huf : u = t
        · subst huf; simp [step, hts, hterm] at *
        · have htask : ((step s (.fail t)).1).taskState u = s.taskState u := by
            simp [step, hts, hterm, if_false, upd, if_neg huf]
          obtain ⟨b, hb⟩ := h.timed_is_waiter u (htask ▸ hu)
          refine ⟨b, ?_⟩
          -- New model: timedMailboxWaiters ac = filter (· ≠ t) ac; u ≠ t so u passes
          simp only [step, hts, hterm, Bool.false_eq_true, if_false]
          exact List.mem_filter.mpr ⟨hb, by simp [huf]⟩
      · -- timed_waiters_valid (RFC 040)
        intro b u hu
        by_cases huf : u = t
        · -- u = t: u is filtered out of timedMailboxWaiters by cancel
          subst huf
          -- hu : u ∈ (s.timedMailboxWaiters b).filter (· ≠ u) → False (filter excludes u)
          simp only [step, hts, hterm, Bool.false_eq_true, if_false, List.mem_filter,
                     decide_eq_true_eq, ne_eq, not_true, and_false] at hu
        · have hmem : u ∈ s.timedMailboxWaiters b := by
            simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hu
            exact (List.mem_filter.mp hu).1
          have hval := h.timed_waiters_valid b u hmem
          have htask : s.taskState u = ((step s (.fail t)).1).taskState u := by
            simp [step, hts, hterm, if_false, upd, if_neg huf]
          exact htask ▸ hval
      · -- timed_waiters_nodup (RFC 040)
        intro b
        simp only [step, hts, hterm, Bool.false_eq_true, if_false]
        exact nodup_of_sublist (List.filter_sublist _) (h.timed_waiters_nodup b)
      · -- timed_waiters_exclusive (RFC 040): cancel filters t from all lists
        intro a' b' u hab' hma hmb'
        simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hma hmb'
        have hma' : u ∈ s.timedMailboxWaiters a' := (List.mem_filter.mp hma).1
        have hmb'' : u ∈ s.timedMailboxWaiters b' := (List.mem_filter.mp hmb').1
        exact h.timed_waiters_exclusive a' b' u hab' hma' hmb''
      · -- mailbox_within_capacity (RFC 056): fail filters waiter lists, not mailboxes
        intro a' n mbx hcap hmbx
        exact h.mailbox_within_capacity a' n mbx
          (by simpa [step, hts, hterm, Bool.false_eq_true, if_false] using hcap)
          (by simpa [step, hts, hterm, Bool.false_eq_true, if_false] using hmbx)

-- Helper: key spawnChild proof patterns mirror spawn exactly
-- (spawnChild only adds taskParent; all other WF fields follow the same logic)

theorem preserves_wf_spawnChild {s : RuntimeState} (h : WellFormed s)
    {t : TaskId} (childA : ActorId) :
    WellFormed ((step s (.spawnChild t childA)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some st => cases st with
      | running =>
        cases how : s.taskOwner t with
        | none => simpa [step, hrt, hts, how] using h
        | some oa =>
          cases hfresh : s.taskState s.nextId with
          | some _ => simpa [step, hrt, hts, how, hfresh] using h
          | none =>
            have hlt : t < s.nextId :=
              Nat.lt_of_not_le (fun hge => absurd hts (by rw [h.fresh_none t hge]; simp))
            have hnq : s.nextId ∉ s.readyQ := fun hm =>
              absurd (h.readyQ_queued s.nextId hm) (by simp [hfresh, Option.any])
            -- Cases on s.mailboxes childA to get a concrete mailboxes field
            cases hma : s.mailboxes childA with
            | none =>
              -- mailboxes field: upd s.mailboxes childA (some Mailbox.empty)
              have hstep_eq : (step s (.spawnChild t childA)).1 = { s with
                  taskState  := upd s.taskState s.nextId (some .new)
                  taskOwner  := upd s.taskOwner s.nextId (some childA)
                  taskParent := upd s.taskParent s.nextId (some t)
                  readyQ     := s.readyQ ++ [s.nextId]
                  mailboxes  := upd s.mailboxes childA (some Mailbox.empty)
                  nextId     := s.nextId + 1 } := by simp [step, hrt, hts, how, hfresh, hma]
              rw [hstep_eq]
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact nodup_append_singleton h.readyQ_nodup hnq
              · intro u hm
                rw [List.mem_append, List.mem_singleton] at hm
                rcases hm with hm | rfl
                · have hun : u ≠ s.nextId := fun he => hnq (he ▸ hm)
                  simp only [upd, if_neg hun, Option.any]; exact h.readyQ_queued u hm
                · simp only [upd_self, Option.any, TaskState.isRunnable]
              · intro u hru
                have hun : u ≠ s.nextId :=
                  fun he => absurd (Option.some.inj ((he ▸ hru).symm.trans hrt)) (Nat.ne_of_lt hlt).symm
                simp only [upd, if_neg hun]; exact h.running_runs u hru
              · exact h.timers_nodup
              · intro e he
                rcases h.timers_sleep e he with hts_e | hts_e
                · have hne : e.task ≠ s.nextId := by
                    intro he2; exact absurd (he2 ▸ hts_e) (by simp [hfresh])
                  exact Or.inl (by simp only [upd, if_neg hne]; exact hts_e)
                · have hne : e.task ≠ s.nextId := by
                    intro he2; exact absurd (he2 ▸ hts_e) (by simp [hfresh])
                  exact Or.inr (by simp only [upd, if_neg hne]; exact hts_e)
              · intro u hnu
                have hlt_u := Nat.lt_of_succ_le hnu
                simp only [upd, if_neg (Nat.ne_of_gt hlt_u)]
                exact h.fresh_none u (Nat.le_of_lt hlt_u)
              · exact h.timers_sorted
              · intro u st' hts'
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hts'
                  exact ⟨childA, by simp only [hun, upd_self]⟩
                · simp only [upd, if_neg hun] at hts'
                  obtain ⟨b, hb⟩ := h.spawned_has_owner u st' hts'
                  exact ⟨b, by simp only [upd, if_neg hun, hb]⟩
              · -- owned_has_mailbox (hma : s.mailboxes childA = none)
                intro u cc hown
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hown
                  have hcc : cc = childA := Option.some.inj hown.symm; subst hcc
                  exact ⟨Mailbox.empty, by simp only [upd_self]⟩
                · simp only [upd, if_neg hun] at hown
                  obtain ⟨mb, hmb⟩ := h.owned_has_mailbox u cc hown
                  have hca : cc ≠ childA := fun hca => absurd (hca ▸ hmb) (by simp [hma])
                  exact ⟨mb, by simp only [upd, if_neg hca, hmb]⟩
              · intro u st' hts' hrun
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hts'
                  rw [List.mem_append, List.mem_singleton]; exact Or.inr hun
                · simp only [upd, if_neg hun] at hts'
                  rw [List.mem_append, List.mem_singleton]
                  exact Or.inl (h.runnable_queued u st' hts' hrun)
              · intro b u hm
                have hun : u ≠ s.nextId := fun he => absurd (he ▸ h.waiters_waiting b u hm) (by simp [hfresh])
                simp only [upd, if_neg hun]; exact h.waiters_waiting b u hm
              · intro b u hm
                have hun : u ≠ s.nextId := fun he => absurd (he ▸ h.waiters_waiting b u hm) (by simp [hfresh])
                simp only [upd, if_neg hun]; exact h.waiters_owned b u hm
              · intro u hts'
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hts'
                  exact absurd (Option.some.inj hts') (by simp)
                · simp only [upd, if_neg hun] at hts'
                  obtain ⟨b, hb, hmem⟩ := h.waiting_queued u hts'
                  exact ⟨b, by simp only [upd, if_neg hun, hb], hmem⟩
              · exact h.waiters_nodup
              · intro u p hp
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hp
                  have hpe : t = p := Option.some.inj hp
                  exact hpe ▸ hun.symm ▸ hlt
                · simp only [upd, if_neg hun] at hp; exact h.parent_lt u p hp
              · intro u p hp
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hp
                  have hpe : t = p := Option.some.inj hp
                  have hpne : p ≠ s.nextId := Nat.ne_of_lt (hpe ▸ hlt)
                  exact ⟨.running, by simp only [upd, if_neg hpne]; exact hpe ▸ hts⟩
                · simp only [upd, if_neg hun] at hp
                  obtain ⟨st', hst'⟩ := h.parent_spawned u p hp
                  by_cases hpn : p = s.nextId
                  · exact ⟨.new, by simp only [hpn, upd_self]⟩
                  · exact ⟨st', by simp only [upd, if_neg hpn]; exact hst'⟩
              · -- occ_fresh (RFC 033): new mailbox is Mailbox.empty
                intro ac mb env hmb henv
                by_cases hac : ac = childA
                · subst hac; simp only [upd_self, Option.some.injEq] at hmb; subst hmb
                  simp [Mailbox.empty] at henv
                · exact h.occ_fresh ac mb env (by simp only [upd, if_neg hac] at hmb; exact hmb) henv
              · -- occ_nodup (RFC 033): new mailbox is Mailbox.empty
                intro ac mb hmb
                by_cases hac : ac = childA
                · subst hac; simp only [upd_self, Option.some.injEq] at hmb; subst hmb
                  simp [Mailbox.empty]
                · exact h.occ_nodup ac mb (by simp only [upd, if_neg hac] at hmb; exact hmb)
              · -- occ_disjoint (RFC 033): new mailbox is Mailbox.empty
                intro ac b mba mbb hab hmba hmbb ea hea eb heb
                have hmba' : s.mailboxes ac = some mba := by
                  by_cases h1 : ac = childA
                  · subst h1; simp only [upd_self, Option.some.injEq] at hmba; subst hmba
                    simp [Mailbox.empty] at hea
                  · simp only [upd, if_neg h1] at hmba; exact hmba
                have hmbb' : s.mailboxes b = some mbb := by
                  by_cases h1 : b = childA
                  · subst h1; simp only [upd_self, Option.some.injEq] at hmbb; subst hmbb
                    simp [Mailbox.empty] at heb
                  · simp only [upd, if_neg h1] at hmbb; exact hmbb
                exact h.occ_disjoint ac b mba mbb hab hmba' hmbb' ea hea eb heb
              · -- owner_spawned (RFC 038): spawnChild-none writes taskOwner at nextId
                intro u a' how
                by_cases hun : u = s.nextId
                · subst hun; exact ⟨.new, by simp [upd_self]⟩
                · obtain ⟨st, hst⟩ := h.owner_spawned u a'
                      (by simp only [upd, if_neg hun] at how; exact how)
                  exact ⟨st, by simp [upd, if_neg hun, hst]⟩
              · -- parent_child_spawned (RFC 038): spawnChild-none writes taskParent at nextId
                intro u p hp
                by_cases hun : u = s.nextId
                · subst hun; exact ⟨.new, by simp [upd_self]⟩
                · obtain ⟨st, hst⟩ := h.parent_child_spawned u p
                      (by simp only [upd, if_neg hun] at hp; exact hp)
                  exact ⟨st, by simp [upd, if_neg hun, hst]⟩
              · -- timed_has_deadline (RFC 040)
                intro u hu
                by_cases huf : u = s.nextId
                · subst huf; simp [upd_self] at hu
                · simp only [upd, if_neg huf] at hu
                  obtain ⟨d, hd⟩ := h.timed_has_deadline u hu
                  exact ⟨d, hd⟩
              · -- deadline_is_timed (RFC 040)
                intro u d hd
                by_cases huf : u = s.nextId
                · -- waitDeadline unchanged; s.taskState s.nextId = none ≠ .waitingTimed
                  have := h.deadline_is_timed u d hd
                  rw [huf] at this; rw [hfresh] at this; cases this
                · have hback := h.deadline_is_timed u d hd
                  simp only [upd, if_neg huf]
                  exact hback
              · -- timed_has_timer (RFC 040)
                intro u hu
                by_cases huf : u = s.nextId
                · subst huf; simp [upd_self] at hu
                · simp only [upd, if_neg huf] at hu
                  obtain ⟨e, he, hek⟩ := h.timed_has_timer u hu
                  exact ⟨e, he, hek⟩
              · -- timed_is_waiter (RFC 040)
                intro u hu
                by_cases huf : u = s.nextId
                · subst huf; simp [upd_self] at hu
                · simp only [upd, if_neg huf] at hu
                  obtain ⟨b, hb⟩ := h.timed_is_waiter u hu
                  exact ⟨b, hb⟩
              · -- timed_waiters_valid (RFC 040)
                intro b u hu
                by_cases huf : u = s.nextId
                · simp only [upd_self]
                  exact absurd (h.timed_waiters_valid b u hu) (by rw [huf]; simp [hfresh])
                · have hval := h.timed_waiters_valid b u hu
                  simp only [upd, if_neg huf]
                  exact hval
              · -- timed_waiters_nodup (RFC 040)
                intro b; exact h.timed_waiters_nodup b
              · -- timed_waiters_exclusive (RFC 040)
                intro a' b' u hab' hma hmb'
                exact h.timed_waiters_exclusive a' b' u hab' hma hmb'
              · -- mailbox_within_capacity (RFC 056): spawnChild adds an empty mailbox for childA
                intro a' n mbx hcap hmbx
                by_cases ha' : a' = childA
                · subst ha'; simp only [upd_self] at hmbx
                  injection hmbx with hmeq; subst hmeq; simp [Mailbox.empty]
                · simp only [upd, if_neg ha'] at hmbx
                  exact h.mailbox_within_capacity a' n mbx hcap hmbx


            | some existingMb =>
              -- mailboxes field: s.mailboxes (unchanged)
              have hstep_eq : (step s (.spawnChild t childA)).1 = { s with
                  taskState  := upd s.taskState s.nextId (some .new)
                  taskOwner  := upd s.taskOwner s.nextId (some childA)
                  taskParent := upd s.taskParent s.nextId (some t)
                  readyQ     := s.readyQ ++ [s.nextId]
                  nextId     := s.nextId + 1 } := by simp [step, hrt, hts, how, hfresh, hma]
              rw [hstep_eq]
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact nodup_append_singleton h.readyQ_nodup hnq
              · intro u hm
                rw [List.mem_append, List.mem_singleton] at hm
                rcases hm with hm | rfl
                · have hun : u ≠ s.nextId := fun he => hnq (he ▸ hm)
                  simp only [upd, if_neg hun, Option.any]; exact h.readyQ_queued u hm
                · simp only [upd_self, Option.any, TaskState.isRunnable]
              · intro u hru
                have hun : u ≠ s.nextId :=
                  fun he => absurd (Option.some.inj ((he ▸ hru).symm.trans hrt)) (Nat.ne_of_lt hlt).symm
                simp only [upd, if_neg hun]; exact h.running_runs u hru
              · exact h.timers_nodup
              · intro e he
                rcases h.timers_sleep e he with hts_e | hts_e
                · have hne : e.task ≠ s.nextId := by
                    intro he2; exact absurd (he2 ▸ hts_e) (by simp [hfresh])
                  exact Or.inl (by simp only [upd, if_neg hne]; exact hts_e)
                · have hne : e.task ≠ s.nextId := by
                    intro he2; exact absurd (he2 ▸ hts_e) (by simp [hfresh])
                  exact Or.inr (by simp only [upd, if_neg hne]; exact hts_e)
              · intro u hnu
                have hlt_u := Nat.lt_of_succ_le hnu
                simp only [upd, if_neg (Nat.ne_of_gt hlt_u)]
                exact h.fresh_none u (Nat.le_of_lt hlt_u)
              · exact h.timers_sorted
              · intro u st' hts'
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hts'
                  exact ⟨childA, by simp only [hun, upd_self]⟩
                · simp only [upd, if_neg hun] at hts'
                  obtain ⟨b, hb⟩ := h.spawned_has_owner u st' hts'
                  exact ⟨b, by simp only [upd, if_neg hun, hb]⟩
              · -- owned_has_mailbox (hma : s.mailboxes childA = some existingMb)
                intro u cc hown
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hown
                  have hcc : cc = childA := Option.some.inj hown.symm; subst hcc
                  exact ⟨existingMb, hma⟩
                · simp only [upd, if_neg hun] at hown
                  obtain ⟨mb, hmb⟩ := h.owned_has_mailbox u cc hown
                  exact ⟨mb, hmb⟩
              · intro u st' hts' hrun
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hts'
                  rw [List.mem_append, List.mem_singleton]; exact Or.inr hun
                · simp only [upd, if_neg hun] at hts'
                  rw [List.mem_append, List.mem_singleton]
                  exact Or.inl (h.runnable_queued u st' hts' hrun)
              · intro b u hm
                have hun : u ≠ s.nextId := fun he => absurd (he ▸ h.waiters_waiting b u hm) (by simp [hfresh])
                simp only [upd, if_neg hun]; exact h.waiters_waiting b u hm
              · intro b u hm
                have hun : u ≠ s.nextId := fun he => absurd (he ▸ h.waiters_waiting b u hm) (by simp [hfresh])
                simp only [upd, if_neg hun]; exact h.waiters_owned b u hm
              · intro u hts'
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hts'
                  exact absurd (Option.some.inj hts') (by simp)
                · simp only [upd, if_neg hun] at hts'
                  obtain ⟨b, hb, hmem⟩ := h.waiting_queued u hts'
                  exact ⟨b, by simp only [upd, if_neg hun, hb], hmem⟩
              · exact h.waiters_nodup
              · intro u p hp
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hp
                  have hpe : t = p := Option.some.inj hp
                  exact hpe ▸ hun.symm ▸ hlt
                · simp only [upd, if_neg hun] at hp; exact h.parent_lt u p hp
              · intro u p hp
                by_cases hun : u = s.nextId
                · simp only [hun, upd_self] at hp
                  have hpe : t = p := Option.some.inj hp
                  have hpne : p ≠ s.nextId := Nat.ne_of_lt (hpe ▸ hlt)
                  exact ⟨.running, by simp only [upd, if_neg hpne]; exact hpe ▸ hts⟩
                · simp only [upd, if_neg hun] at hp
                  obtain ⟨st', hst'⟩ := h.parent_spawned u p hp
                  by_cases hpn : p = s.nextId
                  · exact ⟨.new, by simp only [hpn, upd_self]⟩
                  · exact ⟨st', by simp only [upd, if_neg hpn]; exact hst'⟩
              · -- occ_fresh (RFC 033): mailboxes unchanged
                intro ac mb env hmb henv
                exact h.occ_fresh ac mb env hmb henv
              · -- occ_nodup (RFC 033): mailboxes unchanged
                intro ac mb hmb
                exact h.occ_nodup ac mb hmb
              · -- occ_disjoint (RFC 033): mailboxes unchanged
                intro ac b mba mbb hab hmba hmbb ea hea eb heb
                exact h.occ_disjoint ac b mba mbb hab hmba hmbb ea hea eb heb
              · -- owner_spawned (RFC 038): spawnChild-none writes taskOwner at nextId
                intro u a' how
                by_cases hun : u = s.nextId
                · subst hun; exact ⟨.new, by simp [upd_self]⟩
                · obtain ⟨st, hst⟩ := h.owner_spawned u a'
                      (by simp only [upd, if_neg hun] at how; exact how)
                  exact ⟨st, by simp [upd, if_neg hun, hst]⟩
              · -- parent_child_spawned (RFC 038): spawnChild-none writes taskParent at nextId
                intro u p hp
                by_cases hun : u = s.nextId
                · subst hun; exact ⟨.new, by simp [upd_self]⟩
                · obtain ⟨st, hst⟩ := h.parent_child_spawned u p
                      (by simp only [upd, if_neg hun] at hp; exact hp)
                  exact ⟨st, by simp [upd, if_neg hun, hst]⟩
              · -- timed_has_deadline (RFC 040)
                intro u hu
                by_cases huf : u = s.nextId
                · subst huf; simp [upd_self] at hu
                · simp only [upd, if_neg huf] at hu
                  obtain ⟨d, hd⟩ := h.timed_has_deadline u hu
                  exact ⟨d, hd⟩
              · -- deadline_is_timed (RFC 040)
                intro u d hd
                by_cases huf : u = s.nextId
                · -- waitDeadline unchanged; s.taskState s.nextId = none ≠ .waitingTimed
                  have := h.deadline_is_timed u d hd
                  rw [huf] at this; rw [hfresh] at this; cases this
                · have hback := h.deadline_is_timed u d hd
                  simp only [upd, if_neg huf]
                  exact hback
              · -- timed_has_timer (RFC 040)
                intro u hu
                by_cases huf : u = s.nextId
                · subst huf; simp [upd_self] at hu
                · simp only [upd, if_neg huf] at hu
                  obtain ⟨e, he, hek⟩ := h.timed_has_timer u hu
                  exact ⟨e, he, hek⟩
              · -- timed_is_waiter (RFC 040)
                intro u hu
                by_cases huf : u = s.nextId
                · subst huf; simp [upd_self] at hu
                · simp only [upd, if_neg huf] at hu
                  obtain ⟨b, hb⟩ := h.timed_is_waiter u hu
                  exact ⟨b, hb⟩
              · -- timed_waiters_valid (RFC 040)
                intro b u hu
                by_cases huf : u = s.nextId
                · simp only [upd_self]
                  exact absurd (h.timed_waiters_valid b u hu) (by rw [huf]; simp [hfresh])
                · have hval := h.timed_waiters_valid b u hu
                  simp only [upd, if_neg huf]
                  exact hval
              · -- timed_waiters_nodup (RFC 040)
                intro b; exact h.timed_waiters_nodup b
              · -- timed_waiters_exclusive (RFC 040)
                intro a' b' u hab' hma hmb'
                exact h.timed_waiters_exclusive a' b' u hab' hma hmb'
              · -- mailbox_within_capacity (RFC 056): spawnChild leaves mailboxes unchanged here
                intro a' n mbx hcap hmbx
                exact h.mailbox_within_capacity a' n mbx hcap hmbx


      | new | ready | yielded | sleeping | waitingTimed | waiting | completed | cancelled | failed =>
          simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h

/-- `restartOne` preserves well-formedness (RFC 049). Reduces to
    `preserves_wf_spawnChild`: when valid, the restart's resulting state is
    exactly the `spawnChild` state plus a `restartOf` update, and no
    `WellFormed` field mentions `restartOf` (`WellFormed.restartOf_irrel`). -/
theorem preserves_wf_restartOne {s : RuntimeState} (h : WellFormed s)
    {t failedChild : TaskId} (childA : ActorId) :
    WellFormed ((step s (.restartOne t failedChild childA)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some st => cases st with
      | running =>
        by_cases hpar : s.taskParent failedChild = some t
        · cases hfc : s.taskState failedChild with
          | none => simpa [step, hrt, hts, hpar, hfc] using h
          | some st2 => cases st2 with
            | failed =>
              cases hfresh : s.taskState s.nextId with
              | some _ => simpa [step, hrt, hts, hpar, hfc, hfresh] using h
              | none =>
                obtain ⟨oa, hoa⟩ := h.spawned_has_owner t .running hts
                have heq : (step s (.restartOne t failedChild childA)).1
                    = { (step s (.spawnChild t childA)).1 with
                        restartOf := upd s.restartOf s.nextId (some failedChild) } := by
                  simp [step, hrt, hts, hpar, hfc, hfresh, hoa]
                rw [heq]
                exact (preserves_wf_spawnChild h childA).restartOf_irrel _
            | new | ready | running | yielded | sleeping | waitingTimed
            | waiting | completed | cancelled =>
                simpa [step, hrt, hts, hpar, hfc] using h
        · simpa [step, hrt, hts, hpar] using h
      | new | ready | yielded | sleeping | waitingTimed | waiting | completed | cancelled | failed =>
          simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h

end Henret
