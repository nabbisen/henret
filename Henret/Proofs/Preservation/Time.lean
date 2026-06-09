import Henret.Proofs.Invariants
import Henret.Proofs.Ownership

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
          have h1 := h.timers_sleep e he; rw [hee, hts] at h1; cases h1
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
            have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
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
          exact h.parent_lt u p (by simp only [step, if_pos hrt, hts] at hp; exact hp)
        · -- parent_spawned: sleep sets t → .sleeping; p still in some state
          intro u p hp
          have hpar : s.taskParent u = some p := by
            simp only [step, if_pos hrt, hts] at hp; exact hp
          obtain ⟨st, hst⟩ := h.parent_spawned u p hpar
          by_cases hpt : p = t
          · exact ⟨.sleeping, by simp only [step, if_pos hrt, hts, upd_self, hpt]⟩
          · exact ⟨st, by simp only [step, if_pos hrt, hts, upd, if_neg hpt]; exact hst⟩
        · -- occ_fresh (RFC 033): mailboxes unaffected
          intro a mb env hmb henv; simp only [step, if_pos hrt, hts] at hmb ⊢
          exact h.occ_fresh a mb env hmb henv
        · -- occ_nodup (RFC 033): mailboxes unaffected
          intro a mb hmb; simp only [step, if_pos hrt, hts] at hmb
          exact h.occ_nodup a mb hmb
        · -- occ_disjoint (RFC 033): mailboxes unaffected
          intro a b mba mbb hab hmba hmbb ea hea eb heb
          simp only [step, if_pos hrt, hts] at hmba hmbb
          exact h.occ_disjoint a b mba mbb hab hmba hmbb ea hea eb heb
      | new | ready | yielded | sleeping | completed | cancelled | waiting =>
        simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h

theorem preserves_wf_tick {s : RuntimeState} (h : WellFormed s) :
    WellFormed ((step s (.tick t)).1) := by
  by_cases hle : s.now ≤ t
  · obtain ⟨woken, hwdef⟩ : ∃ w, w = ((Timer.expired s.timers t).map TimerEntry.task).filter
        (fun u => s.taskState u = some .sleeping) := ⟨_, rfl⟩
    have hwoken_sleep : ∀ u ∈ woken, s.taskState u = some .sleeping := by
      intro u hm; rw [hwdef] at hm; exact by simpa using (List.mem_filter.mp hm).2
    have hwoken_nodup : woken.Nodup := by
      rw [hwdef]
      exact (nodup_of_sublist
        (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup).filter _
    have hdisj : ∀ a ∈ s.readyQ, a ∉ woken := by
      intro a ha hm
      have h1 := h.readyQ_queued a ha
      rw [hwoken_sleep a hm] at h1; simp [Option.any, TaskState.isRunnable] at h1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [step, if_pos hle]; rw [← hwdef]
      exact nodup_append h.readyQ_nodup hwoken_nodup hdisj
    · intro u hm
      simp only [step, if_pos hle] at hm ⊢; rw [← hwdef] at hm ⊢
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · rw [wakeMany_preserves_other (hdisj u hm)]; exact h.readyQ_queued u hm
      · rw [wakeMany_wakes hm (hwoken_sleep u hm)]; simp [Option.any, TaskState.isRunnable]
    · intro u hru
      simp only [step, if_pos hle] at hru ⊢; rw [← hwdef]
      have h1 := h.running_runs u hru
      have hnot : u ∉ woken := by
        intro hm; rw [hwoken_sleep u hm] at h1; cases h1
      rw [wakeMany_preserves_of_ne_sleeping h1 (by simp) woken]
    · simp only [step, if_pos hle]
      exact nodup_of_sublist
        (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup
    · intro e he
      simp only [step, if_pos hle] at he ⊢; rw [← hwdef]
      have hmem : e ∈ s.timers := (Timer.mem_remaining.mp he).1
      have hfut : t < e.deadline := (Timer.mem_remaining.mp he).2
      have h1 := h.timers_sleep e hmem
      have hnot : e.task ∉ woken := by
        intro hm; rw [hwdef] at hm
        have hmm := (List.mem_filter.mp hm).1; rw [List.mem_map] at hmm
        obtain ⟨e', he', hee⟩ := hmm
        have he'mem : e' ∈ s.timers := (Timer.mem_expired.mp he').1
        have he'due : e'.deadline ≤ t := (Timer.mem_expired.mp he').2
        have : e = e' := nodup_task_inj h.timers_nodup hmem he'mem hee.symm
        rw [this] at hfut; omega
      rw [wakeMany_preserves_other hnot]; exact h1
    · intro u hu
      simp only [step, if_pos hle] at hu ⊢; rw [← hwdef]
      have h1 := h.fresh_none u hu
      have hnot : u ∉ woken := by
        intro hm; rw [hwoken_sleep u hm] at h1; cases h1
      rw [wakeMany_preserves_other hnot]; exact h1
    · simp only [step, if_pos hle]; exact Timer.remaining_sorted h.timers_sorted
    · intro u st hts'
      simp only [step, if_pos hle] at hts' ⊢; rw [← hwdef] at hts'
      cases hts0 : s.taskState u with
      | none => rw [wakeMany_none hts0] at hts'; cases hts'
      | some st0 => exact h.spawned_has_owner u st0 hts0
    · intro u b hown
      simp only [step, if_pos hle] at hown ⊢; exact h.owned_has_mailbox u b hown
    · intro u st hts' hrun
      simp only [step, if_pos hle] at hts' ⊢; rw [← hwdef] at hts' ⊢
      rw [List.mem_append]
      by_cases hw : u ∈ woken
      · exact Or.inr hw
      · rw [wakeMany_preserves_other hw] at hts'
        exact Or.inl (h.runnable_queued u st hts' hrun)
    · -- waiters_waiting: mailboxWaiters unchanged; woken tasks were sleeping not waiting
      intro a u hm
      simp only [step, if_pos hle] at hm ⊢
      rw [← hwdef]
      have h1 := h.waiters_waiting a u hm
      have hnot : u ∉ woken := fun hmw => absurd (hwoken_sleep u hmw) (by rw [h1]; simp)
      rw [wakeMany_preserves_other hnot]; exact h1
    · -- waiters_owned: taskOwner unchanged
      intro a u hm; simp only [step, if_pos hle] at hm ⊢; exact h.waiters_owned a u hm
    · -- waiting_queued: wakeMany doesn't affect .waiting tasks
      intro u hts'
      simp only [step, if_pos hle] at hts' ⊢; rw [← hwdef] at hts'
      have hnot : u ∉ woken := fun hmw => by
        rw [wakeMany_wakes hmw (hwoken_sleep u hmw)] at hts'; cases hts'
      rw [wakeMany_preserves_other hnot] at hts'
      exact h.waiting_queued u hts'
    · -- waiters_nodup
      intro a; simp only [step, if_pos hle]; exact h.waiters_nodup a
    · -- parent_lt (RFC 032): taskParent unchanged by tick
      intro u p hp
      exact h.parent_lt u p (by simp only [step, if_pos hle] at hp; exact hp)
    · -- parent_spawned: tick may wake p → .ready; still some _
      intro u p hp
      simp only [step, if_pos hle] at hp
      obtain ⟨st, hst⟩ := h.parent_spawned u p hp
      by_cases hpw : p ∈ woken
      · exact ⟨.ready, by simp only [step, if_pos hle]; rw [← hwdef]; exact wakeMany_wakes hpw (hwoken_sleep p hpw)⟩
      · exact ⟨st, by simp only [step, if_pos hle]; rw [← hwdef]; rw [wakeMany_preserves_other hpw]; exact hst⟩
    · -- occ_fresh (RFC 033): mailboxes unaffected
      intro a mb env hmb henv; simp only [step, if_pos hle] at hmb ⊢
      exact h.occ_fresh a mb env hmb henv
    · -- occ_nodup (RFC 033): mailboxes unaffected
      intro a mb hmb; simp only [step, if_pos hle] at hmb
      exact h.occ_nodup a mb hmb
    · -- occ_disjoint (RFC 033): mailboxes unaffected
      intro a b mba mbb hab hmba hmbb ea hea eb heb
      simp only [step, if_pos hle] at hmba hmbb
      exact h.occ_disjoint a b mba mbb hab hmba hmbb ea hea eb heb
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
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        exact h.parent_lt u p (by simp only [step, hts] at hp; exact hp)
      · -- parent_spawned: wake sets t → .ready; still some _
        intro u p hp
        have hpar : s.taskParent u = some p := by simp only [step, hts] at hp; exact hp
        obtain ⟨st, hst⟩ := h.parent_spawned u p hpar
        by_cases hpt : p = t
        · exact ⟨.ready, by simp [step, hts, upd_self, hpt]⟩
        · exact ⟨st, by simp [step, hts, upd, if_neg hpt]; exact hst⟩
      · -- occ_fresh (RFC 033): mailboxes unaffected
        intro a mb env hmb henv; simp only [step, hts] at hmb ⊢
        exact h.occ_fresh a mb env hmb henv
      · -- occ_nodup (RFC 033): mailboxes unaffected
        intro a mb hmb; simp only [step, hts] at hmb
        exact h.occ_nodup a mb hmb
      · -- occ_disjoint (RFC 033): mailboxes unaffected
        intro a b mba mbb hab hmba hmbb ea hea eb heb
        simp only [step, hts] at hmba hmbb
        exact h.occ_disjoint a b mba mbb hab hmba hmbb ea hea eb heb
    | new | ready | running | yielded | completed | cancelled | waiting =>
      simpa [step, hts] using h

end Henret
