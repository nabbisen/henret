import Henret.Proofs.Invariants
import Henret.Proofs.Ownership
import Henret.Proofs.StepFields
import Henret.Proofs.Timers

namespace Henret

-- ─────────────────────────────────────────────────────────────────
-- Per-operation WellFormed preservation: time operations
-- (sleep, tick, wake)   RFC 034
-- ─────────────────────────────────────────────────────────────────

theorem preserves_wf_sleep {s : RuntimeState} (h : WellFormed s) :
    WellFormed ((step s (.sleep t d)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some s' =>
      cases s' with
      | running =>
        have hnotin : t ∉ s.timers.map TimerEntry.task := by
          intro hm; rw [List.mem_map] at hm
          obtain ⟨e, he, hee⟩ := hm
          have h1 := h.timers_sleep e he; rw [hee, hts] at h1
          rcases h1 with h1 | h1 <;> simp at h1
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [step, hrt, hts]; exact h.readyQ_nodup
        · intro u hm
          simp [step, hrt, hts] at hm ⊢
          have h1 := h.readyQ_queued u hm
          have hu : u ≠ t := fun he => by
            rw [he, hts] at h1; simp [Option.any, TaskState.isRunnable] at h1
          simp only [upd, if_neg hu]; exact h1
        · intro u hru; simp [step, hrt, hts] at hru
        · simp [step, hrt, hts]; exact insertSorted_task_nodup hnotin h.timers_nodup
        · intro e he
          simp [step, hrt, hts] at he ⊢
          rcases Timer.mem_insertSorted.mp he with rfl | he
          · simp [upd]
          · have h1 := h.timers_sleep e he
            have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; rcases h1 with h1 | h1 <;> simp at h1
            simp only [upd, if_neg hu]; exact h1
        · intro u hu
          simp [step, hrt, hts] at hu ⊢
          have h1 : u ≠ t := fun he => by
            rw [← he] at hts; rw [h.fresh_none u hu] at hts; cases hts
          simp only [upd, if_neg h1]; exact h.fresh_none u hu
        · simp [step, hrt, hts]; exact Timer.insertSorted_sorted h.timers_sorted
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
        · -- waiters_waiting: mailboxWaiters unchanged; t was running so t ∉ waiters
          intro a u hm; simp [step, hrt, hts] at hm ⊢
          have h1 := h.waiters_waiting a u hm
          have hu : u ≠ t := fun he => by
            rw [← he] at hts; rw [h1] at hts; cases hts
          simp only [upd, if_neg hu]; exact h1
        · -- waiters_owned: taskOwner unchanged
          intro a u hm; simp [step, hrt, hts] at hm ⊢; exact h.waiters_owned a u hm
        · -- waiting_queued: taskState[t] := sleeping; t ∉ waiters
          intro u hts'; simp [step, hrt, hts] at hts' ⊢
          by_cases hu : u = t
          · simp only [hu, upd_self] at hts'; cases hts'
          · simp only [upd, if_neg hu] at hts'; exact h.waiting_queued u hts'
        · -- waiters_nodup: mailboxWaiters unchanged
          intro a; simp [step, hrt, hts]; exact h.waiters_nodup a
        · -- parent_lt (RFC 032): taskParent not written by sleep
          intro u p hp
          exact wf_parent_lt_pass h (by simp [step, if_pos hrt, hts]) u p hp
        · -- parent_spawned (RFC 042 → RFC 082 helper): taskParent unchanged by
          --   sleep; a spawned task stays spawned (step_preserves_spawned).
          intro u p hp
          exact wf_parent_spawned_pass h (by simp [step, if_pos hrt, hts])
            (fun _ hv => step_preserves_spawned hv.choose_spec (.sleep t d)) u p hp
        · -- occ_fresh (via bundled wf_occ_pass, RFC 042 → RFC 082): mailboxes/nextMsgId unaffected
          intro a mb env hmb henv
          exact (wf_occ_pass h (by simp [step, if_pos hrt, hts]) (by simp [step, if_pos hrt, hts])).fresh a mb env hmb henv
        · -- occ_nodup (RFC 033 → RFC 042 helper)
          intro a mb hmb
          exact wf_occ_nodup_pass h (by simp [step, if_pos hrt, hts]) a mb hmb
        · -- occ_disjoint (RFC 033 → RFC 042 helper)
          intro a b mba mbb hab hmba hmbb ea hea eb heb
          exact wf_occ_disjoint_pass h (by simp [step, if_pos hrt, hts]) a b mba mbb hab hmba hmbb ea hea eb heb
        · -- owner_spawned (RFC 038): taskOwner unchanged
          intro u a' how'
          obtain ⟨st, hst⟩ := h.owner_spawned u a'
            (by simpa [step, if_pos hrt, hts] using how')
          exact step_preserves_spawned hst _
        · -- parent_child_spawned (RFC 038): taskParent unchanged
          intro u p hp
          obtain ⟨st, hst⟩ := h.parent_child_spawned u p
            (by simpa [step, if_pos hrt, hts] using hp)
          exact step_preserves_spawned hst _
        · -- timed_has_deadline (RFC 040): sleep doesn't change waitDeadline
          intro u hu
          have huf : u ≠ t := by
            intro he; rw [he] at hu
            simp [step, if_pos hrt, hts, upd_self] at hu
          simp only [step, if_pos hrt, hts, upd, if_neg huf] at hu
          obtain ⟨dv, hdv⟩ := h.timed_has_deadline u hu
          have : ((step s (.sleep t d)).1).waitDeadline u = s.waitDeadline u := by simp [step, hrt, hts]
          exact ⟨dv, this.symm ▸ hdv⟩
        · -- deadline_is_timed (RFC 040): sleep doesn't change waitDeadline
          intro u dv hd
          have huf : u ≠ t := by
            intro he; rw [he] at hd
            have hdt : s.waitDeadline t = some dv := by simp [step, hrt, hts] at hd; exact hd
            exact absurd (h.deadline_is_timed t dv hdt) (by rw [hts]; simp)
          simp only [step, if_pos hrt, hts] at hd
          have hback := h.deadline_is_timed u dv hd
          simp [step, hrt, hts, upd, if_neg huf]
          exact hback
        · -- timed_has_timer (RFC 040): timers grows (sleep adds), timed tasks keep their timer
          intro u hu
          have huf : u ≠ t := by
            intro he; rw [he] at hu
            simp [step, if_pos hrt, hts, upd_self] at hu
          simp only [step, if_pos hrt, hts, upd, if_neg huf] at hu
          obtain ⟨e, he, hek⟩ := h.timed_has_timer u hu
          refine ⟨e, ?_, hek⟩
          simp only [step, if_pos hrt, hts]
          rw [Timer.mem_insertSorted]; exact Or.inr he
        · -- timed_is_waiter (RFC 040): timedMailboxWaiters unchanged
          intro u hu
          have huf : u ≠ t := by
            intro he; rw [he] at hu
            simp [step, if_pos hrt, hts, upd_self] at hu
          simp only [step, if_pos hrt, hts, upd, if_neg huf] at hu
          obtain ⟨a, ha⟩ := h.timed_is_waiter u hu
          exact ⟨a, by simp [step, hrt, hts]; exact ha⟩
        · -- timed_waiters_valid (RFC 040): timedMailboxWaiters unchanged
          intro a u hm
          simp only [step, if_pos hrt, hts] at hm
          have huf : u ≠ t := by
            intro he; rw [he] at hm
            exact absurd (h.timed_waiters_valid a t hm) (by simp [hts])
          simp [step, hrt, hts, upd, if_neg huf]
          exact h.timed_waiters_valid a u hm
        · -- timed_waiters_nodup (RFC 040)
          intro a; simpa [step, if_pos hrt, hts] using h.timed_waiters_nodup a
        · -- timed_waiters_exclusive (RFC 040)
          intro a' b' u hab' hma hmb'
          exact h.timed_waiters_exclusive a' b' u hab'
            (by simpa [step, if_pos hrt, hts] using hma)
            (by simpa [step, if_pos hrt, hts] using hmb')
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed | failed =>
        simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h

theorem preserves_wf_tick {s : RuntimeState} (h : WellFormed s) :
    WellFormed ((step s (.tick t)).1) := by
  by_cases hle : s.now ≤ t
  · -- Key helpers
    have hwS : ∀ u ∈ tickWokenSleeping s t, s.taskState u = some .sleeping := by
      intro u hm; simp [tickWokenSleeping] at hm; exact hm.2
    have hwT : ∀ u ∈ tickWokenTimed s t, s.taskState u = some .waitingTimed := by
      intro u hm; simp [tickWokenTimed] at hm; exact hm.2
    have hwoken : ∀ u ∈ tickWoken s t, s.taskState u = some .sleeping
                                      ∨ s.taskState u = some .waitingTimed := by
      intro u hm; rw [tickWoken_def, List.mem_append] at hm
      rcases hm with hS | hT; exact Or.inl (hwS u hS); exact Or.inr (hwT u hT)
    have hwoken_nodup : (tickWoken s t).Nodup := by
      rw [tickWoken_def]
      apply nodup_append
      · exact (nodup_of_sublist (List.Sublist.map _ (List.filter_sublist _)) h.timers_nodup).filter _
      · exact (nodup_of_sublist (List.Sublist.map _ (List.filter_sublist _)) h.timers_nodup).filter _
      · intro u hs ht
        simp [tickWokenSleeping] at hs; simp [tickWokenTimed] at ht
        rw [hs.2] at ht; exact absurd ht.2 (by decide)
    have hnotInWoken : ∀ u, u ∉ tickWoken s t →
        ((step s (.tick t)).1).taskState u = s.taskState u := by
      intro u hm; exact tick_no_early_wake hle hm
    have hnotReadyQ : ∀ a ∈ s.readyQ, a ∉ tickWoken s t := by
      intro a ha hm
      have h1 := h.readyQ_queued a ha
      rcases hwoken a hm with h2 | h2 <;> rw [h2] at h1 <;> simp [Option.any, TaskState.isRunnable] at h1
    have hstep_rq : ((step s (.tick t)).1).readyQ = s.readyQ ++ tickWoken s t :=
      tick_enqueues_woken s hle
    -- Helper: task not in woken keeps its state
    have not_woken_of_not_sleepTimed : ∀ u, s.taskState u ≠ some .sleeping →
        s.taskState u ≠ some .waitingTimed → u ∉ tickWoken s t := by
      intro u hs ht hm
      rcases hwoken u hm with h2 | h2
      · exact hs h2
      · exact ht h2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- readyQ_nodup
      rw [hstep_rq]; exact nodup_append h.readyQ_nodup hwoken_nodup hnotReadyQ
    · -- readyQ_queued
      intro u hm; rw [hstep_rq, List.mem_append] at hm
      rcases hm with hm | hm
      · rw [hnotInWoken u (hnotReadyQ u hm)]; exact h.readyQ_queued u hm
      · have htick : ((step s (.tick t)).1).taskState u = some .ready := by
          simp only [step, if_pos hle]
          exact wakeMany_wakes ((tickWoken_def s t) ▸ hm) (hwoken u hm)
        rw [htick]; simp [Option.any, TaskState.isRunnable]
    · -- running_runs
      intro u hru; simp only [step, if_pos hle] at hru
      have h1 := h.running_runs u hru
      have hnot : u ∉ tickWoken s t := not_woken_of_not_sleepTimed u (by rw [h1]; simp) (by rw [h1]; simp)
      rw [hnotInWoken u hnot]; exact h1
    · -- timers_nodup
      simp only [step, if_pos hle]
      exact nodup_of_sublist (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup
    · -- timers_sleep
      intro e he
      have hmem : e ∈ s.timers := by simp only [step, if_pos hle] at he; exact (Timer.mem_remaining.mp he).1
      have hfut : t < e.deadline := by simp only [step, if_pos hle] at he; exact (Timer.mem_remaining.mp he).2
      have h1 := h.timers_sleep e hmem
      have hnot : e.task ∉ tickWoken s t := by
        intro hm
        have hdue : e.deadline ≤ t := by
          rw [tickWoken_def, List.mem_append] at hm
          rcases hm with hS | hT
          · simp only [tickWokenSleeping, List.mem_filter, decide_eq_true_eq] at hS
            obtain ⟨e', he', hee'⟩ := List.mem_map.mp hS.1
            have heq := nodup_task_inj h.timers_nodup hmem (Timer.mem_expired.mp he').1 hee'.symm
            exact heq ▸ (Timer.mem_expired.mp he').2
          · simp only [tickWokenTimed, List.mem_filter, decide_eq_true_eq] at hT
            obtain ⟨e', he', hee'⟩ := List.mem_map.mp hT.1
            have heq := nodup_task_inj h.timers_nodup hmem (Timer.mem_expired.mp he').1 hee'.symm
            exact heq ▸ (Timer.mem_expired.mp he').2
        exact absurd hdue (Nat.not_le.mpr hfut)
      rw [hnotInWoken e.task hnot]; exact h1
    · -- fresh_none
      intro u hu
      simp only [step, if_pos hle] at hu
      have h1 := h.fresh_none u hu
      have hnot : u ∉ tickWoken s t := not_woken_of_not_sleepTimed u (by rw [h1]; simp) (by rw [h1]; simp)
      rw [hnotInWoken u hnot]; exact h1
    · -- timers_sorted
      simp only [step, if_pos hle]; exact Timer.remaining_sorted h.timers_sorted
    · -- 8. spawned_has_owner: taskOwner unchanged, taskState unchanged for non-woken
      intro u st hts'
      by_cases hpw : u ∈ tickWoken s t
      · rcases hwoken u hpw with h2 | h2
        · obtain ⟨a, ha⟩ := h.spawned_has_owner u .sleeping h2
          exact ⟨a, by simpa [step, if_pos hle] using ha⟩
        · obtain ⟨a, ha⟩ := h.spawned_has_owner u .waitingTimed h2
          exact ⟨a, by simpa [step, if_pos hle] using ha⟩
      · rw [hnotInWoken u hpw] at hts'
        obtain ⟨a, ha⟩ := h.spawned_has_owner u st hts'
        exact ⟨a, by simp only [step, if_pos hle]; exact ha⟩
    · -- 9. owned_has_mailbox: taskOwner and mailboxes both unchanged
      intro u a how
      simp only [step, if_pos hle] at how
      obtain ⟨mb, hmb⟩ := h.owned_has_mailbox u a how
      exact ⟨mb, by simp only [step, if_pos hle]; exact hmb⟩
    · -- 10. runnable_queued
      intro u st hu hrun; rw [hstep_rq]
      by_cases hpw : u ∈ tickWoken s t
      · exact List.mem_append.mpr (Or.inr hpw)
      · rw [hnotInWoken u hpw] at hu
        exact List.mem_append.mpr (Or.inl (h.runnable_queued u st hu hrun))
    · -- 11. waiters_waiting: mailboxWaiters unchanged, .waiting → not woken
      intro a u hm; simp only [step, if_pos hle] at hm
      have h1 := h.waiters_waiting a u hm
      have hnot : u ∉ tickWoken s t := not_woken_of_not_sleepTimed u (by rw [h1]; simp) (by rw [h1]; simp)
      rw [hnotInWoken u hnot]; exact h1
    · -- 12. waiters_owned: taskOwner unchanged
      intro a u hm; simp only [step, if_pos hle] at hm
      have := h.waiters_owned a u hm
      simp only [step, if_pos hle]; exact this
    · -- 13. waiting_queued: .waiting → taskOwner/mailboxWaiters unchanged
      intro u hts'
      have hnot : u ∉ tickWoken s t := by
        intro hm
        have hrdy : ((step s (.tick t)).1).taskState u = some .ready := by
          simp only [step, if_pos hle, tickWokenSleeping, tickWokenTimed]
          exact wakeMany_wakes ((tickWoken_def s t ▸ hm)) (hwoken u hm)
        rw [hrdy] at hts'; exact absurd hts' (by simp)
      rw [hnotInWoken u hnot] at hts'
      obtain ⟨a, ha, hmw⟩ := h.waiting_queued u hts'
      exact ⟨a, by simp only [step, if_pos hle]; exact ha, by simp only [step, if_pos hle]; exact hmw⟩
    · -- 14. waiters_nodup
      intro a; simp only [step, if_pos hle]; exact h.waiters_nodup a
    · -- 15. parent_lt
      intro u p hp; exact wf_parent_lt_pass h (by simp [step, if_pos hle]) u p hp
    · -- 16. parent_spawned
      intro u p hp; simp only [step, if_pos hle] at hp
      obtain ⟨st, hst⟩ := h.parent_spawned u p hp
      by_cases hpw : p ∈ tickWoken s t
      · refine ⟨.ready, ?_⟩
        simp only [step, if_pos hle]
        exact wakeMany_wakes ((tickWoken_def s t) ▸ hpw) (hwoken p hpw)
      · exact ⟨st, by rw [hnotInWoken p hpw]; exact hst⟩
    · intro a mb env hmb henv
      exact wf_occ_fresh_pass h (by simp [step, if_pos hle]) (by simp [step, if_pos hle]) a mb env hmb henv
    · intro a mb hmb; exact wf_occ_nodup_pass h (by simp [step, if_pos hle]) a mb hmb
    · intro a b mba mbb hab hmba hmbb ea hea eb heb
      exact wf_occ_disjoint_pass h (by simp [step, if_pos hle]) a b mba mbb hab hmba hmbb ea hea eb heb
    · intro u a' how'
      obtain ⟨st, hst⟩ := h.owner_spawned u a' (by simpa [step, if_pos hle] using how')
      exact step_preserves_spawned hst _
    · intro u p hp
      obtain ⟨st, hst⟩ := h.parent_child_spawned u p (by simpa [step, if_pos hle] using hp)
      exact step_preserves_spawned hst _
    · -- timed_has_deadline
      -- Helper: all woken tasks become .ready after tick
      have tick_rdy : ∀ v ∈ tickWoken s t, ((step s (.tick t)).1).taskState v = some .ready := by
        intro v hv
        simp only [step, if_pos hle, tickWokenSleeping, tickWokenTimed]
        rcases List.mem_append.mp ((tickWoken_def s t) ▸ hv) with hS | hT
        · exact wakeMany_wakes (List.mem_append.mpr (Or.inl hS)) (Or.inl (hwS v hS))
        · exact wakeMany_wakes (List.mem_append.mpr (Or.inr hT)) (Or.inr (hwT v hT))
      intro u hu
      -- u is .waitingTimed after tick → u ∉ woken (woken → .ready ≠ .waitingTimed)
      have hnot : u ∉ tickWoken s t := fun hm => absurd (tick_rdy u hm) (hu ▸ by simp)
      -- u ∉ wokenTimed specifically
      have hnotT : u ∉ tickWokenTimed s t := fun hm =>
        hnot ((tickWoken_def s t) ▸ List.mem_append.mpr (Or.inr hm))
      -- taskState unchanged
      rw [hnotInWoken u hnot] at hu
      obtain ⟨dv, hdv⟩ := h.timed_has_deadline u hu
      -- waitDeadline unchanged for non-wokenTimed
      have hwd : ((step s (.tick t)).1).waitDeadline u = s.waitDeadline u := by
        simp only [step, if_pos hle, tickWokenTimed]
        exact if_neg hnotT
      exact ⟨dv, hwd.symm ▸ hdv⟩
    · -- deadline_is_timed
      intro u dv hd
      -- waitDeadline u = some dv after tick → u ∉ wokenTimed (wokenTimed → none)
      have hnotT : u ∉ tickWokenTimed s t := by
        intro hm
        simp only [step, if_pos hle, tickWokenTimed] at hd
        have hm_in : u ∈ (List.filter (fun u => decide (s.taskState u = some .waitingTimed))
            ((Timer.expired s.timers t).map TimerEntry.task)) := by
          simpa [tickWokenTimed] using hm
        rw [if_pos hm_in] at hd; exact absurd hd (by simp)
      -- hd simplifies to s.waitDeadline u = some dv
      have hd' : s.waitDeadline u = some dv := by
        have : ((step s (.tick t)).1).waitDeadline u = s.waitDeadline u := by
          simp only [step, if_pos hle, tickWokenTimed]; exact if_neg hnotT
        rwa [← this]
      -- h.deadline_is_timed gives s.taskState u = .waitingTimed
      have hback := h.deadline_is_timed u dv hd'
      -- u ∉ tickWoken (since .waitingTimed tasks aren't in wokenSleeping)
      have hnot : u ∉ tickWoken s t := by
        rw [tickWoken_def, List.mem_append, not_or]
        exact ⟨fun hS => absurd (hwS u hS) (by rw [hback]; simp), hnotT⟩
      rw [hnotInWoken u hnot]; exact hback
    · -- timed_has_timer
      have tick_rdy : ∀ v ∈ tickWoken s t, ((step s (.tick t)).1).taskState v = some .ready := by
        intro v hv; simp only [step, if_pos hle, tickWokenSleeping, tickWokenTimed]
        rcases List.mem_append.mp ((tickWoken_def s t) ▸ hv) with hS | hT
        · exact wakeMany_wakes (List.mem_append.mpr (Or.inl hS)) (Or.inl (hwS v hS))
        · exact wakeMany_wakes (List.mem_append.mpr (Or.inr hT)) (Or.inr (hwT v hT))
      intro u hu
      have hnot : u ∉ tickWoken s t := fun hm => absurd (tick_rdy u hm) (hu ▸ by simp)
      rw [hnotInWoken u hnot] at hu
      obtain ⟨e, he, hek⟩ := h.timed_has_timer u hu
      refine ⟨e, ?_, hek⟩
      -- e ∈ remaining iff e ∈ timers ∧ t < e.deadline
      simp only [step, if_pos hle]
      apply Timer.mem_remaining.mpr; refine ⟨he, ?_⟩
      -- prove t < e.deadline: if not, e.task would be woken → contradicts hnot
      rcases Nat.lt_or_ge t e.deadline with hlt | hge
      · exact hlt
      · exfalso
        have hmem : e.task ∈ tickWoken s t := by
          rw [tickWoken_def]
          exact List.mem_append.mpr (Or.inr (by
            simp only [tickWokenTimed, List.mem_filter, decide_eq_true_eq]
            exact ⟨List.mem_map_of_mem TimerEntry.task (Timer.mem_expired.mpr ⟨he, hge⟩), hek ▸ hu⟩))
        exact absurd hmem (hek ▸ hnot)
    · -- timed_is_waiter
      have tick_rdy : ∀ v ∈ tickWoken s t, ((step s (.tick t)).1).taskState v = some .ready := by
        intro v hv; simp only [step, if_pos hle, tickWokenSleeping, tickWokenTimed]
        rcases List.mem_append.mp ((tickWoken_def s t) ▸ hv) with hS | hT
        · exact wakeMany_wakes (List.mem_append.mpr (Or.inl hS)) (Or.inl (hwS v hS))
        · exact wakeMany_wakes (List.mem_append.mpr (Or.inr hT)) (Or.inr (hwT v hT))
      intro u hu
      have hnot : u ∉ tickWoken s t := fun hm => absurd (tick_rdy u hm) (hu ▸ by simp)
      have hnotT : u ∉ tickWokenTimed s t := fun hm =>
        hnot ((tickWoken_def s t) ▸ List.mem_append.mpr (Or.inr hm))
      rw [hnotInWoken u hnot] at hu
      obtain ⟨a, ha⟩ := h.timed_is_waiter u hu
      refine ⟨a, ?_⟩
      simp only [step, if_pos hle, tickWokenTimed, List.mem_filter, decide_eq_true_eq]
      refine ⟨ha, ?_⟩
      exact fun ⟨hmem, htst⟩ => hnot (show u ∈ tickWoken s t from by
        rw [tickWoken_def]; exact List.mem_append.mpr (Or.inr (
          by simp [tickWokenTimed, hmem, htst])))
    · -- timed_waiters_valid
      intro a u hm; simp only [step, if_pos hle, List.mem_filter] at hm
      obtain ⟨hmem, hun⟩ := hm
      have hnotT : u ∉ tickWokenTimed s t := by simpa [tickWokenTimed] using hun
      have hnot : u ∉ tickWoken s t := by
        rw [tickWoken_def, List.mem_append, not_or]
        exact ⟨fun hS => absurd (hwS u hS) (by rw [h.timed_waiters_valid a u hmem]; simp), hnotT⟩
      rw [hnotInWoken u hnot]; exact h.timed_waiters_valid a u hmem
    · -- timed_waiters_nodup
      intro a; simp only [step, if_pos hle]; exact nodup_of_sublist (List.filter_sublist _) (h.timed_waiters_nodup a)
    · -- timed_waiters_exclusive: tick filters from each list
      intro a' b' u hab' hma hmb'
      simp only [step, if_pos hle] at hma hmb'
      exact h.timed_waiters_exclusive a' b' u hab'
        (List.mem_filter.mp hma).1 (List.mem_filter.mp hmb').1
  · simpa [step, hle] using h

theorem preserves_wf_wake {s : RuntimeState} (h : WellFormed s) :
    WellFormed ((step s (.wake t)).1) := by
  cases hts : s.taskState t with
  | none => simpa [step, hts] using h
  | some s' =>
    cases s' with
    | sleeping =>
      have hnq : t ∉ s.readyQ := fun hm => by
        have h1 := h.readyQ_queued t hm; rw [hts] at h1
        simp [Option.any, TaskState.isRunnable] at h1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [step, hts]; exact nodup_append_singleton h.readyQ_nodup hnq
      · intro u hm
        simp [step, hts] at hm ⊢; rcases hm with hm | rfl
        · have hu : u ≠ t := fun he => hnq (he ▸ hm)
          simp only [upd, if_neg hu]; exact h.readyQ_queued u hm
        · simp [upd, Option.any, TaskState.isRunnable]
      · intro u hru
        simp [step, hts] at hru ⊢
        have h1 := h.running_runs u hru
        have hu : u ≠ t := fun he => by rw [he, hts] at h1; cases h1
        simp only [upd, if_neg hu]; exact h1
      · simp [step, hts]
        exact nodup_of_sublist
          (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup
      · intro e he
        simp [step, hts] at he ⊢; obtain ⟨he, hu⟩ := he
        simp only [upd, if_neg hu]; exact h.timers_sleep e he
      · intro u hu
        simp [step, hts] at hu ⊢
        have h1 : u ≠ t := fun he => by
          rw [← he] at hts; rw [h.fresh_none u hu] at hts; cases hts
        simp only [upd, if_neg h1]; exact h.fresh_none u hu
      · simp [step, hts]; exact Timer.sorted_filter _ h.timers_sorted
      · intro u st hts'
        simp [step, hts] at hts' ⊢
        by_cases hu : u = t
        · subst hu; exact h.spawned_has_owner u .sleeping hts
        · simp only [upd, if_neg hu] at hts'; exact h.spawned_has_owner u st hts'
      · intro u b hown
        simp [step, hts] at hown ⊢; exact h.owned_has_mailbox u b hown
      · intro u st hts' hrun
        simp [step, hts] at hts' ⊢
        by_cases hu : u = t
        · subst hu; exact Or.inr rfl
        · simp only [upd, if_neg hu] at hts'
          exact Or.inl (h.runnable_queued u st hts' hrun)
      · -- waiters_waiting: t was sleeping so t ∉ waiters; upd only changes t
        intro a u hm; simp [step, hts] at hm ⊢
        have h1 := h.waiters_waiting a u hm
        have hu : u ≠ t := fun he => by
          rw [← he] at hts; rw [h1] at hts; cases hts
        simp only [upd, if_neg hu]; exact h1
      · -- waiters_owned: taskOwner unchanged
        intro a u hm; simp [step, hts] at hm ⊢; exact h.waiters_owned a u hm
      · -- waiting_queued: taskState[t] := ready; t was sleeping not waiting
        intro u hts'; simp [step, hts] at hts' ⊢
        by_cases hu : u = t
        · simp only [hu, upd_self] at hts'; cases hts'
        · simp only [upd, if_neg hu] at hts'; exact h.waiting_queued u hts'
      · -- waiters_nodup
        intro a; simp [step, hts]; exact h.waiters_nodup a
      · -- parent_lt (RFC 032)
        intro u p hp
        exact wf_parent_lt_pass h (by simp [step, hts]) u p hp
      · -- parent_spawned: wake sets t → .ready; still some _
        intro u p hp
        have hpar : s.taskParent u = some p := by simp only [step, hts] at hp; exact hp
        obtain ⟨st, hst⟩ := h.parent_spawned u p hpar
        by_cases hpt : p = t
        · exact ⟨.ready, by simp [step, hts, upd_self, hpt]⟩
        · exact ⟨st, by simp [step, hts, upd, if_neg hpt]; exact hst⟩
      · -- occ_fresh (RFC 033 → RFC 042 helper): mailboxes unaffected by wake
        intro a mb env hmb henv
        exact wf_occ_fresh_pass h (by simp [step, hts]) (by simp [step, hts]) a mb env hmb henv
      · -- occ_nodup (RFC 033 → RFC 042 helper)
        intro a mb hmb
        exact wf_occ_nodup_pass h (by simp [step, hts]) a mb hmb
      · -- occ_disjoint (RFC 033 → RFC 042 helper)
        intro a b mba mbb hab hmba hmbb ea hea eb heb
        exact wf_occ_disjoint_pass h (by simp [step, hts]) a b mba mbb hab hmba hmbb ea hea eb heb
      · -- owner_spawned (RFC 038): taskOwner unchanged
        intro u a' how'
        obtain ⟨st, hst⟩ := h.owner_spawned u a'
          (by simpa [step, hts] using how')
        exact step_preserves_spawned hst _
      · -- parent_child_spawned (RFC 038): taskParent unchanged
        intro u p hp
        obtain ⟨st, hst⟩ := h.parent_child_spawned u p
          (by simpa [step, hts] using hp)
        exact step_preserves_spawned hst _
      · -- timed_has_deadline (RFC 040): wake doesn't change waitDeadline
        intro u hu
        have huf : u ≠ t := by
          intro he; rw [he] at hu; simp [step, hts, upd_self] at hu
        simp only [step, hts, upd, if_neg huf] at hu
        obtain ⟨dv, hdv⟩ := h.timed_has_deadline u hu
        exact ⟨dv, by simpa [step, hts] using hdv⟩
      · -- deadline_is_timed (RFC 040): wake doesn't change waitDeadline
        intro u dv hd
        have huf : u ≠ t := by
          intro he; rw [he] at hd; simp only [step, hts] at hd
          exact absurd (h.deadline_is_timed _ dv hd) (by rw [hts]; simp)
        simp only [step, hts] at hd
        have hback := h.deadline_is_timed u dv hd
        simp only [step, hts, upd, if_neg huf]; exact hback
      · -- timed_has_timer (RFC 040): wake doesn't change non-t timers
        intro u hu
        have huf : u ≠ t := by
          intro he; rw [he] at hu; simp [step, hts, upd_self] at hu
        simp only [step, hts, upd, if_neg huf] at hu
        obtain ⟨e, he, hek⟩ := h.timed_has_timer u hu
        refine ⟨e, ?_, hek⟩
        simp only [step, hts, List.mem_filter]
        exact ⟨he, by simp [hek, huf]⟩
      · -- timed_is_waiter (RFC 040): timedMailboxWaiters unchanged
        intro u hu
        have huf : u ≠ t := by
          intro he; rw [he] at hu; simp [step, hts, upd_self] at hu
        simp only [step, hts, upd, if_neg huf] at hu
        obtain ⟨a, ha⟩ := h.timed_is_waiter u hu
        exact ⟨a, by simpa [step, hts] using ha⟩
      · -- timed_waiters_valid (RFC 040): timedMailboxWaiters unchanged
        intro a u hm
        simp only [step, hts] at hm
        have huf : u ≠ t := by
          intro he; rw [he] at hm
          exact absurd (h.timed_waiters_valid a t hm) (by simp [hts])
        simp only [step, hts, upd, if_neg huf]
        exact h.timed_waiters_valid a u hm
      · -- timed_waiters_nodup (RFC 040)
        intro a; simpa [step, hts] using h.timed_waiters_nodup a
      · -- timed_waiters_exclusive (RFC 040)
        intro a' b' u hab' hma hmb'
        exact h.timed_waiters_exclusive a' b' u hab'
          (by simpa [step, hts] using hma) (by simpa [step, hts] using hmb')
    | new | ready | running | yielded | completed | cancelled | waiting | waitingTimed | failed =>
      simpa [step, hts] using h

end Henret
