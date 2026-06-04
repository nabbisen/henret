import Henret.Proofs.Invariants
import Henret.Proofs.Ownership
import Henret.Proofs.Messaging

namespace Henret

/-! ## Invariant preservation (RFC 013)

`step_preserves_wf` walks all eleven operations and shows the
`WellFormed` discipline survives each.  `run_preserves_wf` lifts it to
programs, and `reachable_wf` instantiates at `init`: **every reachable
state is well-formed**. -/

/-- Every operation preserves well-formedness. -/
theorem step_preserves_wf {s : RuntimeState} (h : WellFormed s)
    (op : RuntimeOp) : WellFormed ((step s op).1) := by
  cases op with
  | spawn a =>
    cases hts : s.taskState s.nextId with
    | some _ => simpa [step, hts] using h
    | none =>
      have hnq : s.nextId ∉ s.readyQ := fun hm => by
        have h1 := h.readyQ_queued _ hm
        rw [hts] at h1
        simp [Option.any] at h1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- readyQ_nodup
        simp only [step, hts]
        exact nodup_append_singleton h.readyQ_nodup hnq
      · -- readyQ_queued
        intro u hm
        simp only [step, hts] at hm ⊢
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · have hu : u ≠ s.nextId := fun he => hnq (he ▸ hm)
          simp only [upd, if_neg hu]
          exact h.readyQ_queued u hm
        · simp [upd, Option.any, TaskState.isRunnable]
      · -- running_runs
        intro u hr
        simp only [step, hts] at hr ⊢
        have h1 := h.running_runs u hr
        have hu : u ≠ s.nextId := fun he => by rw [he, hts] at h1; cases h1
        simp only [upd, if_neg hu]
        exact h1
      · -- timers_nodup
        simp only [step, hts]
        exact h.timers_nodup
      · -- timers_sleep
        intro e he
        simp only [step, hts] at he ⊢
        have h1 := h.timers_sleep e he
        have hu : e.task ≠ s.nextId := fun heq => by rw [heq, hts] at h1; cases h1
        simp only [upd, if_neg hu]
        exact h1
      · -- fresh_none
        intro u hu
        simp only [step, hts] at hu ⊢
        have h1 : u ≠ s.nextId := Nat.ne_of_gt hu
        have h2 : s.nextId ≤ u := Nat.le_of_succ_le hu
        simp only [upd, if_neg h1]
        exact h.fresh_none u h2
      · -- timers_sorted
        simp only [step, hts]
        exact h.timers_sorted
      · -- spawned_has_owner
        intro u st hts'
        simp only [step, hts] at hts' ⊢
        by_cases hu : u = s.nextId
        · subst hu
          exact ⟨a, by simp [upd]⟩
        · simp only [upd, if_neg hu] at hts' ⊢
          exact h.spawned_has_owner u st hts'
      · -- owned_has_mailbox
        intro u b hown
        cases hmb0 : s.mailboxes a with
        | some mba =>
          simp only [step, hts, hmb0] at hown ⊢
          by_cases hu : u = s.nextId
          · subst hu
            simp only [upd_self] at hown
            injection hown with hab
            subst hab
            exact ⟨mba, hmb0⟩
          · simp only [upd, if_neg hu] at hown
            exact h.owned_has_mailbox u b hown
        | none =>
          simp only [step, hts, hmb0] at hown ⊢
          by_cases hu : u = s.nextId
          · subst hu
            simp only [upd_self] at hown
            injection hown with hab
            subst hab
            exact ⟨Mailbox.empty, by simp [upd]⟩
          · simp only [upd, if_neg hu] at hown
            obtain ⟨mb', hmb'⟩ := h.owned_has_mailbox u b hown
            by_cases hba : b = a
            · subst hba
              rw [hmb'] at hmb0
              cases hmb0
            · exact ⟨mb', by simp only [upd, if_neg hba]; exact hmb'⟩
      · -- runnable_queued (RFC 028)
        intro u st hts' hrun
        simp only [step, hts] at hts' ⊢
        by_cases hu : u = s.nextId
        · subst hu
          rw [List.mem_append, List.mem_singleton]
          exact Or.inr rfl
        · simp only [upd, if_neg hu] at hts'
          rw [List.mem_append]
          exact Or.inl (h.runnable_queued u st hts' hrun)
  | schedule =>
    cases hr : s.running with
    | some _ => simpa [step, hr] using h
    | none =>
      cases hq : s.readyQ with
      | nil => simpa [step, hr, hq] using h
      | cons t q =>
        by_cases hrun : (s.taskState t).any TaskState.isRunnable = true
        · have hnodup := h.readyQ_nodup
          rw [hq, List.nodup_cons] at hnodup
          have htsome : ∃ x, s.taskState t = some x := by
            cases hto : s.taskState t with
            | none => rw [hto] at hrun; simp [Option.any] at hrun
            | some x => exact ⟨x, rfl⟩
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [step, hr, hq, if_pos hrun]
            exact hnodup.2
          · intro u hm
            simp only [step, hr, hq, if_pos hrun] at hm ⊢
            have hu : u ≠ t := fun he => hnodup.1 (he ▸ hm)
            simp only [upd, if_neg hu]
            exact h.readyQ_queued u (by rw [hq]; exact List.mem_cons_of_mem t hm)
          · intro u hru
            simp only [step, hr, hq, if_pos hrun] at hru ⊢
            cases hru
            simp [upd]
          · simp only [step, hr, hq, if_pos hrun]
            exact h.timers_nodup
          · intro e he
            simp only [step, hr, hq, if_pos hrun] at he ⊢
            have h1 := h.timers_sleep e he
            have hu : e.task ≠ t := fun heq => by
              rw [heq] at h1
              rw [h1] at hrun
              simp [Option.any, TaskState.isRunnable] at hrun
            simp only [upd, if_neg hu]
            exact h1
          · intro u hu
            simp only [step, hr, hq, if_pos hrun] at hu ⊢
            obtain ⟨x, hx⟩ := htsome
            have h1 : u ≠ t := fun he => by
              rw [← he] at hx
              rw [h.fresh_none u hu] at hx
              cases hx
            simp only [upd, if_neg h1]
            exact h.fresh_none u hu
          · simp only [step, hr, hq, if_pos hrun]
            exact h.timers_sorted
          · intro u st hts'
            simp only [step, hr, hq, if_pos hrun] at hts' ⊢
            by_cases hu : u = t
            · subst hu
              obtain ⟨x, hx⟩ := htsome
              exact h.spawned_has_owner u x hx
            · simp only [upd, if_neg hu] at hts'
              exact h.spawned_has_owner u st hts'
          · intro u b hown
            simp only [step, hr, hq, if_pos hrun] at hown ⊢
            exact h.owned_has_mailbox u b hown
          · -- runnable_queued (RFC 028)
            intro u st hts' hrun'
            simp only [step, hr, hq, if_pos hrun] at hts' ⊢
            by_cases hu : u = t
            · subst hu
              simp only [upd_self] at hts'
              cases hts'
              simp [TaskState.isRunnable] at hrun'
            · simp only [upd, if_neg hu] at hts'
              have hmem := h.runnable_queued u st hts' hrun'
              rw [hq, List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact absurd rfl hu
              · exact hmem
        · simp at hrun; simpa [step, hr, hq, hrun] using h
  | yield t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simpa [step, hrt, hts] using h
      | some s' =>
        cases s' with
        | running =>
          have hnq : t ∉ s.readyQ := fun hm => by
            have h1 := h.readyQ_queued t hm
            rw [hts] at h1
            simp [Option.any, TaskState.isRunnable] at h1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [step, hrt, hts, if_pos rfl]
            simp only [if_pos]
            exact nodup_append_singleton h.readyQ_nodup hnq
          · intro u hm
            simp [step, hrt, hts] at hm ⊢
            rcases hm with hm | rfl
            · have hu : u ≠ t := fun he => hnq (he ▸ hm)
              simp only [upd, if_neg hu]
              exact h.readyQ_queued u hm
            · simp [upd, Option.any, TaskState.isRunnable]
          · intro u hru
            simp [step, hrt, hts] at hru
          · simp only [step]
            simp [hrt, hts]
            exact h.timers_nodup
          · intro e he
            simp [step, hrt, hts] at he ⊢
            have h1 := h.timers_sleep e he
            have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
            simp only [upd, if_neg hu]
            exact h1
          · intro u hu
            simp [step, hrt, hts] at hu ⊢
            have h1 : u ≠ t := fun he => by
              rw [← he] at hts
              rw [h.fresh_none u hu] at hts
              cases hts
            simp only [upd, if_neg h1]
            exact h.fresh_none u hu
          · simp [step, hrt, hts]
            exact h.timers_sorted
          · intro u st hts'
            simp [step, hrt, hts] at hts' ⊢
            by_cases hu : u = t
            · subst hu
              exact h.spawned_has_owner u .running hts
            · simp only [upd, if_neg hu] at hts'
              exact h.spawned_has_owner u st hts'
          · intro u b hown
            simp [step, hrt, hts] at hown ⊢
            exact h.owned_has_mailbox u b hown
          · -- runnable_queued (RFC 028)
            intro u st hts' hrun
            simp [step, hrt, hts] at hts' ⊢
            by_cases hu : u = t
            · subst hu
              exact Or.inr rfl
            · simp only [upd, if_neg hu] at hts'
              exact Or.inl (h.runnable_queued u st hts' hrun)
        | new => simpa [step, hrt, hts] using h
        | ready => simpa [step, hrt, hts] using h
        | yielded => simpa [step, hrt, hts] using h
        | sleeping => simpa [step, hrt, hts] using h
        | completed => simpa [step, hrt, hts] using h
        | cancelled => simpa [step, hrt, hts] using h
    · simpa [step, hrt] using h
  | complete t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simpa [step, hrt, hts] using h
      | some s' =>
        cases s' with
        | running =>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [step, hrt, hts]
            exact h.readyQ_nodup
          · intro u hm
            simp [step, hrt, hts] at hm ⊢
            have h1 := h.readyQ_queued u hm
            have hu : u ≠ t := fun he => by
              rw [he, hts] at h1
              simp [Option.any, TaskState.isRunnable] at h1
            simp only [upd, if_neg hu]
            exact h1
          · intro u hru
            simp [step, hrt, hts] at hru
          · simp [step, hrt, hts]
            exact h.timers_nodup
          · intro e he
            simp [step, hrt, hts] at he ⊢
            have h1 := h.timers_sleep e he
            have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
            simp only [upd, if_neg hu]
            exact h1
          · intro u hu
            simp [step, hrt, hts] at hu ⊢
            have h1 : u ≠ t := fun he => by
              rw [← he] at hts
              rw [h.fresh_none u hu] at hts
              cases hts
            simp only [upd, if_neg h1]
            exact h.fresh_none u hu
          · simp [step, hrt, hts]
            exact h.timers_sorted
          · intro u st hts'
            simp [step, hrt, hts] at hts' ⊢
            by_cases hu : u = t
            · subst hu
              exact h.spawned_has_owner u .running hts
            · simp only [upd, if_neg hu] at hts'
              exact h.spawned_has_owner u st hts'
          · intro u b hown
            simp [step, hrt, hts] at hown ⊢
            exact h.owned_has_mailbox u b hown
          · -- runnable_queued (RFC 028)
            intro u st hts' hrun
            simp [step, hrt, hts] at hts' ⊢
            by_cases hu : u = t
            · subst hu
              simp only [upd_self] at hts'
              cases hts'
              simp [TaskState.isRunnable] at hrun
            · simp only [upd, if_neg hu] at hts'
              exact h.runnable_queued u st hts' hrun
        | new => simpa [step, hrt, hts] using h
        | ready => simpa [step, hrt, hts] using h
        | yielded => simpa [step, hrt, hts] using h
        | sleeping => simpa [step, hrt, hts] using h
        | completed => simpa [step, hrt, hts] using h
        | cancelled => simpa [step, hrt, hts] using h
    · simpa [step, hrt] using h
  | cancel t =>
    cases hts : s.taskState t with
    | none => simpa [step, hts] using h
    | some s' =>
      by_cases hterm : s'.isTerminal = true
      · simpa [step, hts, hterm] using h
      · simp at hterm
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [step, hts, hterm]
          exact h.readyQ_nodup.filter _
        · intro u hm
          simp [step, hts, hterm] at hm ⊢
          obtain ⟨hm, hu⟩ := hm
          simp only [upd, if_neg hu]
          exact h.readyQ_queued u hm
        · intro u hru
          simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hru ⊢
          by_cases hcase : s.running = some t
          · rw [if_pos hcase] at hru; cases hru
          · rw [if_neg hcase] at hru
            have h1 := h.running_runs u hru
            have hu : u ≠ t := fun he => hcase (he ▸ hru)
            simp only [upd, if_neg hu]
            exact h1
        · simp [step, hts, hterm]
          exact nodup_of_sublist
            (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup
        · intro e he
          simp [step, hts, hterm] at he ⊢
          obtain ⟨he, hu⟩ := he
          simp only [upd, if_neg hu]
          exact h.timers_sleep e he
        · intro u hu
          simp [step, hts, hterm] at hu ⊢
          have h1 : u ≠ t := fun he => by
            rw [← he] at hts
            rw [h.fresh_none u hu] at hts
            cases hts
          simp only [upd, if_neg h1]
          exact h.fresh_none u hu
        · simp [step, hts, hterm]
          exact Timer.sorted_filter _ h.timers_sorted
        · intro u st hts'
          simp [step, hts, hterm] at hts' ⊢
          by_cases hu : u = t
          · subst hu
            exact h.spawned_has_owner u s' hts
          · simp only [upd, if_neg hu] at hts'
            exact h.spawned_has_owner u st hts'
        · intro u b hown
          simp [step, hts, hterm] at hown ⊢
          exact h.owned_has_mailbox u b hown
        · -- runnable_queued (RFC 028)
          intro u st hts' hrun
          simp [step, hts, hterm] at hts' ⊢
          by_cases hu : u = t
          · subst hu
            simp only [upd_self] at hts'
            cases hts'
            simp [TaskState.isRunnable] at hrun
          · simp only [upd, if_neg hu] at hts'
            exact ⟨h.runnable_queued u st hts' hrun, hu⟩
  | send t b m =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using h.readyQ_nodup
    · intro u hm
      simp at hm ⊢
      exact h.readyQ_queued u hm
    · intro u hru
      simp at hru ⊢
      exact h.running_runs u hru
    · simpa using h.timers_nodup
    · intro e he
      simp at he ⊢
      exact h.timers_sleep e he
    · intro u hu
      simp at hu ⊢
      exact h.fresh_none u hu
    · simpa using h.timers_sorted
    · intro u st hts'
      simp at hts' ⊢
      exact h.spawned_has_owner u st hts'
    · intro u cc hown
      simp at hown
      obtain ⟨mb, hmb⟩ := h.owned_has_mailbox u cc hown
      exact send_mailbox_isSome hmb m
    · -- runnable_queued (RFC 028)
      intro u st hts' hrun
      simp at hts' ⊢
      exact h.runnable_queued u st hts' hrun
  | receive t =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using h.readyQ_nodup
    · intro u hm
      simp at hm ⊢
      exact h.readyQ_queued u hm
    · intro u hru
      simp at hru ⊢
      exact h.running_runs u hru
    · simpa using h.timers_nodup
    · intro e he
      simp at he ⊢
      exact h.timers_sleep e he
    · intro u hu
      simp at hu ⊢
      exact h.fresh_none u hu
    · simpa using h.timers_sorted
    · intro u st hts'
      simp at hts' ⊢
      exact h.spawned_has_owner u st hts'
    · intro u cc hown
      simp at hown
      obtain ⟨mb, hmb⟩ := h.owned_has_mailbox u cc hown
      exact receive_mailbox_isSome hmb
    · -- runnable_queued (RFC 028)
      intro u st hts' hrun
      simp at hts' ⊢
      exact h.runnable_queued u st hts' hrun
  | inject a m =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using h.readyQ_nodup
    · intro u hm
      simp at hm ⊢
      exact h.readyQ_queued u hm
    · intro u hru
      simp at hru ⊢
      exact h.running_runs u hru
    · simpa using h.timers_nodup
    · intro e he
      simp at he ⊢
      exact h.timers_sleep e he
    · intro u hu
      simp at hu ⊢
      exact h.fresh_none u hu
    · simpa using h.timers_sorted
    · intro u st hts'
      simp at hts' ⊢
      exact h.spawned_has_owner u st hts'
    · intro u cc hown
      simp at hown
      obtain ⟨mb, hmb⟩ := h.owned_has_mailbox u cc hown
      exact inject_mailbox_isSome hmb m
    · -- runnable_queued (RFC 028)
      intro u st hts' hrun
      simp at hts' ⊢
      exact h.runnable_queued u st hts' hrun
  | sleep t d =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simpa [step, hrt, hts] using h
      | some s' =>
        cases s' with
        | running =>
          have hnotin : t ∉ s.timers.map TimerEntry.task := by
            intro hm
            rw [List.mem_map] at hm
            obtain ⟨e, he, hee⟩ := hm
            have h1 := h.timers_sleep e he
            rw [hee, hts] at h1
            cases h1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [step, hrt, hts]
            exact h.readyQ_nodup
          · intro u hm
            simp [step, hrt, hts] at hm ⊢
            have h1 := h.readyQ_queued u hm
            have hu : u ≠ t := fun he => by
              rw [he, hts] at h1
              simp [Option.any, TaskState.isRunnable] at h1
            simp only [upd, if_neg hu]
            exact h1
          · intro u hru
            simp [step, hrt, hts] at hru
          · simp [step, hrt, hts]
            exact insertSorted_task_nodup hnotin h.timers_nodup
          · intro e he
            simp [step, hrt, hts] at he ⊢
            rcases Timer.mem_insertSorted.mp he with rfl | he
            · simp [upd]
            · have h1 := h.timers_sleep e he
              have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
              simp only [upd, if_neg hu]
              exact h1
          · intro u hu
            simp [step, hrt, hts] at hu ⊢
            have h1 : u ≠ t := fun he => by
              rw [← he] at hts
              rw [h.fresh_none u hu] at hts
              cases hts
            simp only [upd, if_neg h1]
            exact h.fresh_none u hu
          · simp [step, hrt, hts]
            exact Timer.insertSorted_sorted h.timers_sorted
          · intro u st hts'
            simp [step, hrt, hts] at hts' ⊢
            by_cases hu : u = t
            · subst hu
              exact h.spawned_has_owner u .running hts
            · simp only [upd, if_neg hu] at hts'
              exact h.spawned_has_owner u st hts'
          · intro u b hown
            simp [step, hrt, hts] at hown ⊢
            exact h.owned_has_mailbox u b hown
          · -- runnable_queued (RFC 028)
            intro u st hts' hrun
            simp [step, hrt, hts] at hts' ⊢
            by_cases hu : u = t
            · subst hu
              simp only [upd_self] at hts'
              cases hts'
              simp [TaskState.isRunnable] at hrun
            · simp only [upd, if_neg hu] at hts'
              exact h.runnable_queued u st hts' hrun
        | new => simpa [step, hrt, hts] using h
        | ready => simpa [step, hrt, hts] using h
        | yielded => simpa [step, hrt, hts] using h
        | sleeping => simpa [step, hrt, hts] using h
        | completed => simpa [step, hrt, hts] using h
        | cancelled => simpa [step, hrt, hts] using h
    · simpa [step, hrt] using h
  | tick t =>
    by_cases hle : s.now ≤ t
    · obtain ⟨woken, hwdef⟩ : ∃ w, w = ((Timer.expired s.timers t).map TimerEntry.task).filter
          (fun u => s.taskState u = some .sleeping) := ⟨_, rfl⟩
      have hwoken_sleep : ∀ u ∈ woken, s.taskState u = some .sleeping := by
        intro u hm
        rw [hwdef] at hm
        have := (List.mem_filter.mp hm).2
        simpa using this
      have hwoken_nodup : woken.Nodup := by
        rw [hwdef]
        exact (nodup_of_sublist
          (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup).filter _
      have hdisj : ∀ a ∈ s.readyQ, a ∉ woken := by
        intro a ha hm
        have h1 := h.readyQ_queued a ha
        rw [hwoken_sleep a hm] at h1
        simp [Option.any, TaskState.isRunnable] at h1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [step, if_pos hle]
        rw [← hwdef]
        exact nodup_append h.readyQ_nodup hwoken_nodup hdisj
      · intro u hm
        simp only [step, if_pos hle] at hm ⊢
        rw [← hwdef] at hm ⊢
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · rw [wakeMany_preserves_other (hdisj u hm)]
          exact h.readyQ_queued u hm
        · rw [wakeMany_wakes hm (hwoken_sleep u hm)]
          simp [Option.any, TaskState.isRunnable]
      · intro u hru
        simp only [step, if_pos hle] at hru ⊢
        rw [← hwdef]
        have h1 := h.running_runs u hru
        rw [wakeMany_preserves_of_ne_sleeping h1 (by simp) woken]
      · simp only [step, if_pos hle]
        exact nodup_of_sublist
          (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup
      · intro e he
        simp only [step, if_pos hle] at he ⊢
        rw [← hwdef]
        have hmem : e ∈ s.timers := (Timer.mem_remaining.mp he).1
        have hfut : t < e.deadline := (Timer.mem_remaining.mp he).2
        have h1 := h.timers_sleep e hmem
        have hnot : e.task ∉ woken := by
          intro hm
          rw [hwdef] at hm
          have hmm := (List.mem_filter.mp hm).1
          rw [List.mem_map] at hmm
          obtain ⟨e', he', hee⟩ := hmm
          have he'mem : e' ∈ s.timers := (Timer.mem_expired.mp he').1
          have he'due : e'.deadline ≤ t := (Timer.mem_expired.mp he').2
          have : e = e' := nodup_task_inj h.timers_nodup hmem he'mem hee.symm
          rw [this] at hfut
          omega
        rw [wakeMany_preserves_other hnot]
        exact h1
      · intro u hu
        simp only [step, if_pos hle] at hu ⊢
        rw [← hwdef]
        have h1 := h.fresh_none u hu
        have hnot : u ∉ woken := by
          intro hm
          rw [hwoken_sleep u hm] at h1
          cases h1
        rw [wakeMany_preserves_other hnot]
        exact h1
      · simp only [step, if_pos hle]
        exact Timer.remaining_sorted h.timers_sorted
      · intro u st hts'
        simp only [step, if_pos hle] at hts' ⊢
        rw [← hwdef] at hts'
        cases hts0 : s.taskState u with
        | none => rw [wakeMany_none hts0] at hts'; cases hts'
        | some st0 => exact h.spawned_has_owner u st0 hts0
      · intro u b hown
        simp only [step, if_pos hle] at hown ⊢
        exact h.owned_has_mailbox u b hown
      · -- runnable_queued (RFC 028)
        intro u st hts' hrun
        simp only [step, if_pos hle] at hts' ⊢
        rw [← hwdef] at hts' ⊢
        rw [List.mem_append]
        by_cases hw : u ∈ woken
        · exact Or.inr hw
        · rw [wakeMany_preserves_other hw] at hts'
          exact Or.inl (h.runnable_queued u st hts' hrun)
    · simpa [step, hle] using h
  | wake t =>
    cases hts : s.taskState t with
    | none => simpa [step, hts] using h
    | some s' =>
      cases s' with
      | sleeping =>
        have hnq : t ∉ s.readyQ := fun hm => by
          have h1 := h.readyQ_queued t hm
          rw [hts] at h1
          simp [Option.any, TaskState.isRunnable] at h1
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [step, hts]
          exact nodup_append_singleton h.readyQ_nodup hnq
        · intro u hm
          simp [step, hts] at hm ⊢
          rcases hm with hm | rfl
          · have hu : u ≠ t := fun he => hnq (he ▸ hm)
            simp only [upd, if_neg hu]
            exact h.readyQ_queued u hm
          · simp [upd, Option.any, TaskState.isRunnable]
        · intro u hru
          simp [step, hts] at hru ⊢
          have h1 := h.running_runs u hru
          have hu : u ≠ t := fun he => by rw [he, hts] at h1; cases h1
          simp only [upd, if_neg hu]
          exact h1
        · simp [step, hts]
          exact nodup_of_sublist
            (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup
        · intro e he
          simp [step, hts] at he ⊢
          obtain ⟨he, hu⟩ := he
          simp only [upd, if_neg hu]
          exact h.timers_sleep e he
        · intro u hu
          simp [step, hts] at hu ⊢
          have h1 : u ≠ t := fun he => by
            rw [← he] at hts
            rw [h.fresh_none u hu] at hts
            cases hts
          simp only [upd, if_neg h1]
          exact h.fresh_none u hu
        · simp [step, hts]
          exact Timer.sorted_filter _ h.timers_sorted
        · intro u st hts'
          simp [step, hts] at hts' ⊢
          by_cases hu : u = t
          · subst hu
            exact h.spawned_has_owner u .sleeping hts
          · simp only [upd, if_neg hu] at hts'
            exact h.spawned_has_owner u st hts'
        · intro u b hown
          simp [step, hts] at hown ⊢
          exact h.owned_has_mailbox u b hown
        · -- runnable_queued (RFC 028)
          intro u st hts' hrun
          simp [step, hts] at hts' ⊢
          by_cases hu : u = t
          · subst hu
            exact Or.inr rfl
          · simp only [upd, if_neg hu] at hts'
            exact Or.inl (h.runnable_queued u st hts' hrun)
      | new => simpa [step, hts] using h
      | ready => simpa [step, hts] using h
      | running => simpa [step, hts] using h
      | yielded => simpa [step, hts] using h
      | completed => simpa [step, hts] using h
      | cancelled => simpa [step, hts] using h

/-- Whole-program invariant preservation. -/
theorem run_preserves_wf {s : RuntimeState} (h : WellFormed s) :
    ∀ ops : List RuntimeOp, WellFormed (run s ops) := by
  intro ops
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih => exact ih (step_preserves_wf h op)

/-- **Every reachable state is well-formed** (RFC 013 headline).
In particular: the ready queue never contains duplicates, every queued
task is runnable, every timer task is sleeping, and the
ownership-location disjointness corollaries hold throughout every
program. -/
theorem reachable_wf (ops : List RuntimeOp) :
    WellFormed (run RuntimeState.init ops) :=
  run_preserves_wf wf_init ops

/-- Every reachable spawned task has an owning actor (RFC 014/019
headline): ownership is not merely stable when present — it is always
present. -/
theorem reachable_spawned_has_owner (ops : List RuntimeOp)
    {t : TaskId} {st : TaskState}
    (h : (run RuntimeState.init ops).taskState t = some st) :
    ∃ a, (run RuntimeState.init ops).taskOwner t = some a :=
  (reachable_wf ops).spawned_has_owner t st h

/-- Every reachable owning actor exists: it has a mailbox (RFC 019). -/
theorem reachable_owner_has_mailbox (ops : List RuntimeOp)
    {t : TaskId} {a : ActorId}
    (h : (run RuntimeState.init ops).taskOwner t = some a) :
    ∃ mb, (run RuntimeState.init ops).mailboxes a = some mb :=
  (reachable_wf ops).owned_has_mailbox t a h

/-- The timer queue is sorted in every reachable state — now a field of
the single reachability invariant rather than a separate theorem
(RFC 019). -/
theorem reachable_timers_sorted (ops : List RuntimeOp) :
    Timer.Sorted (run RuntimeState.init ops).timers :=
  (reachable_wf ops).timers_sorted

/-- **Schedulable completeness** (RFC 028 headline): in every reachable
state, every runnable task is in the ready queue — the runtime never
loses a runnable task. -/
theorem reachable_runnable_is_queued (ops : List RuntimeOp)
    {t : TaskId} {st : TaskState}
    (h : (run RuntimeState.init ops).taskState t = some st)
    (hrun : st.isRunnable = true) :
    t ∈ (run RuntimeState.init ops).readyQ :=
  (reachable_wf ops).runnable_queued t st h hrun

/-- **Exact queue characterization** (RFC 028): in every reachable
state, the ready queue contains *exactly* the runnable tasks —
membership in the queue is equivalent to being spawned in a runnable
state. Combines `readyQ_queued` (soundness: queued ⇒ runnable) with
`runnable_queued` (completeness: runnable ⇒ queued). -/
theorem reachable_queue_exact (ops : List RuntimeOp) (t : TaskId) :
    t ∈ (run RuntimeState.init ops).readyQ ↔
      ∃ st, (run RuntimeState.init ops).taskState t = some st ∧
        st.isRunnable = true := by
  constructor
  · intro hm
    have h1 := (reachable_wf ops).readyQ_queued t hm
    cases hts : (run RuntimeState.init ops).taskState t with
    | none => rw [hts] at h1; simp [Option.any] at h1
    | some st =>
      rw [hts] at h1
      exact ⟨st, rfl, by simpa [Option.any] using h1⟩
  · rintro ⟨st, hts, hrun⟩
    exact (reachable_wf ops).runnable_queued t st hts hrun

end Henret

/-!
# Henret.Proofs.InvariantsPreservation

Preservation of the `WellFormed` invariant (RFC 013).

* `step_preserves_wf` — all eleven operations preserve well-formedness.
* `run_preserves_wf` / `reachable_wf` — every reachable state is
  well-formed.  Corollaries via `Henret.Proofs.Invariants`:
  no duplicate ready entries, location disjointness (a task is queued,
  running, or sleeping-with-timer — never two at once).
-/
