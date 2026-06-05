import Henret.Proofs.Invariants

namespace Henret

-- ─────────────────────────────────────────────────────────────────
-- Per-operation WellFormed preservation: lifecycle operations
-- (spawn, schedule, yield, complete, cancel)   RFC 034
-- ─────────────────────────────────────────────────────────────────

theorem preserves_wf_spawn (h : WellFormed s) (a : ActorId) :
    WellFormed ((step s (.spawn a)).1) := by
  cases hts : s.taskState s.nextId with
  | some _ => simpa [step, hts] using h
  | none =>
    have hnq : s.nextId ∉ s.readyQ := fun hm => by
      have h1 := h.readyQ_queued _ hm; rw [hts] at h1; simp [Option.any] at h1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [step, hts]
      exact nodup_append_singleton h.readyQ_nodup hnq
    · intro u hm
      simp only [step, hts] at hm ⊢
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · have hu : u ≠ s.nextId := fun he => hnq (he ▸ hm)
        simp only [upd, if_neg hu]; exact h.readyQ_queued u hm
      · simp [upd, Option.any, TaskState.isRunnable]
    · intro u hr
      simp only [step, hts] at hr ⊢
      have h1 := h.running_runs u hr
      have hu : u ≠ s.nextId := fun he => by rw [he, hts] at h1; cases h1
      simp only [upd, if_neg hu]; exact h1
    · simp only [step, hts]; exact h.timers_nodup
    · intro e he
      simp only [step, hts] at he ⊢
      have h1 := h.timers_sleep e he
      have hu : e.task ≠ s.nextId := fun heq => by rw [heq, hts] at h1; cases h1
      simp only [upd, if_neg hu]; exact h1
    · intro u hu
      simp only [step, hts] at hu ⊢
      have h1 : u ≠ s.nextId := Nat.ne_of_gt hu
      have h2 : s.nextId ≤ u := Nat.le_of_succ_le hu
      simp only [upd, if_neg h1]; exact h.fresh_none u h2
    · simp only [step, hts]; exact h.timers_sorted
    · intro u st hts'
      simp only [step, hts] at hts' ⊢
      by_cases hu : u = s.nextId
      · subst hu; exact ⟨a, by simp [upd]⟩
      · simp only [upd, if_neg hu] at hts' ⊢; exact h.spawned_has_owner u st hts'
    · intro u b hown
      cases hmb0 : s.mailboxes a with
      | some mba =>
        simp only [step, hts, hmb0] at hown ⊢
        by_cases hu : u = s.nextId
        · subst hu; simp only [upd_self] at hown; injection hown with hab; subst hab
          exact ⟨mba, hmb0⟩
        · simp only [upd, if_neg hu] at hown; exact h.owned_has_mailbox u b hown
      | none =>
        simp only [step, hts, hmb0] at hown ⊢
        by_cases hu : u = s.nextId
        · subst hu; simp only [upd_self] at hown; injection hown with hab; subst hab
          exact ⟨Mailbox.empty, by simp [upd]⟩
        · simp only [upd, if_neg hu] at hown
          obtain ⟨mb', hmb'⟩ := h.owned_has_mailbox u b hown
          by_cases hba : b = a
          · subst hba; rw [hmb'] at hmb0; cases hmb0
          · exact ⟨mb', by simp only [upd, if_neg hba]; exact hmb'⟩
    · intro u st hts' hrun
      simp only [step, hts] at hts' ⊢
      by_cases hu : u = s.nextId
      · subst hu; rw [List.mem_append, List.mem_singleton]; exact Or.inr rfl
      · simp only [upd, if_neg hu] at hts'
        rw [List.mem_append]; exact Or.inl (h.runnable_queued u st hts' hrun)
    · -- waiters_waiting (RFC 031)
      intro a u hm; simp only [step, hts] at hm ⊢
      have hts_u := h.waiters_waiting a u hm
      by_cases hu : u = s.nextId
      · subst hu; simp [h.fresh_none s.nextId (Nat.le_refl _)] at hts_u
      · simp only [upd, if_neg hu]; exact hts_u
    · -- waiters_owned (RFC 031)
      intro a u hm; simp only [step, hts] at hm ⊢
      have hts_u := h.waiters_waiting a u hm
      have ho := h.waiters_owned a u hm
      by_cases hu : u = s.nextId
      · subst hu; simp [h.fresh_none s.nextId (Nat.le_refl _)] at hts_u
      · simp only [upd, if_neg hu]; exact ho
    · -- waiting_queued (RFC 031)
      intro u hts'
      simp only [step, hts] at hts' ⊢
      by_cases hu : u = s.nextId
      · subst hu; simp only [upd_self] at hts'; cases hts'
      · simp only [upd, if_neg hu] at hts'
        obtain ⟨a', ha', hmem⟩ := h.waiting_queued u hts'
        exact ⟨a', by simp only [upd, if_neg hu]; exact ha', hmem⟩
    · -- waiters_nodup (RFC 031)
      intro a; simp only [step, hts]; exact h.waiters_nodup a

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
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          have h1 := h.timers_sleep e he
          have hu : e.task ≠ t := fun heq => by
            rw [heq] at h1; rw [h1] at hrun; simp [Option.any, TaskState.isRunnable] at hrun
          simp only [upd, if_neg hu]; exact h1
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
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          have h1 := h.timers_sleep e he
          have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
          simp only [upd, if_neg hu]; exact h1
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
      | new | ready | yielded | sleeping | completed | cancelled | waiting =>
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
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          have h1 := h.timers_sleep e he
          have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
          simp only [upd, if_neg hu]; exact h1
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
      | new | ready | yielded | sleeping | completed | cancelled | waiting =>
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
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        simp only [upd, if_neg hu]; exact h.timers_sleep e he
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

end Henret
