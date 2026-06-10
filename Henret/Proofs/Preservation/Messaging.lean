import Henret.Proofs.Invariants
import Henret.Proofs.Messaging
import Henret.Proofs.Ownership
import Henret.Proofs.StepFields
import Henret.Proofs.StepFields

namespace Henret

-- Per-operation WellFormed preservation: messaging (RFC 034 / RFC 031 / RFC 033)

private theorem waiting_not_in_readyQ {s : RuntimeState} (h : WellFormed s)
    {w : TaskId} (hw : s.taskState w = some .waiting) : w ∉ s.readyQ :=
  fun hmem => by have := h.readyQ_queued w hmem; rw [hw] at this; simp [Option.any, TaskState.isRunnable] at this

private theorem waiter_ne_running {s : RuntimeState} (h : WellFormed s)
    {w u : TaskId} (hw : s.taskState w = some .waiting) (hrun : s.running = some u) : w ≠ u :=
  fun he => by subst he; exact absurd (h.running_runs w hrun) (by rw [hw]; simp)

private theorem waiter_in_tail {s : RuntimeState} (_ : WellFormed s)
    {a : ActorId} {w u : TaskId} {ws : List TaskId}
    (hlist : s.mailboxWaiters a = w :: ws) (hmem : u ∈ s.mailboxWaiters a) (hne : u ≠ w) : u ∈ ws :=
  (List.mem_cons.mp (hlist ▸ hmem)).resolve_left hne

-- nextMsgId is not the occurrence id of any existing envelope
private theorem nextMsgId_fresh {s : RuntimeState} (h : WellFormed s)
    {a : ActorId} {mb : Mailbox}
    (hmb : s.mailboxes a = some mb) : s.nextMsgId ∉ mb.messages.map Envelope.occurrence := by
  intro hmem
  obtain ⟨e, he, hocc⟩ := List.mem_map.mp hmem
  exact Nat.lt_irrefl _ (hocc ▸ h.occ_fresh a mb e hmb he)

-- ─── send: WellFormed preservation ────────────────────────────────────────

theorem preserves_wf_send {s : RuntimeState} (h : WellFormed s)
    {t : TaskId} {b : ActorId} {m : Message} :
    WellFormed ((step s (.send t b m)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some st => cases st with
      | running => cases how : s.taskOwner t with
        | none => simpa [step, hrt, hts, how] using h
        | some o => cases hmb : s.mailboxes b with
          | none => simpa [step, hrt, hts, how, hmb] using h
          | some mb => cases hw : s.mailboxWaiters b with
            | nil =>
              by_cases htw : s.timedMailboxWaiters b = []
              · -- No waiter at all: only mailboxes and nextMsgId change
                have hstep : (step s (.send t b m)).1 =
                    { s with
                      mailboxes := upd s.mailboxes b (some (mb.enqueue ⟨s.nextMsgId, s.taskOwner t, m⟩))
                      nextMsgId := s.nextMsgId + 1 } := by
                  simp [step, hrt, hts, how, hmb, hw, htw]
                rw [hstep]
                refine ⟨h.readyQ_nodup, fun u hm => h.readyQ_queued u hm, h.running_runs,
                  h.timers_nodup, h.timers_sleep, h.fresh_none, h.timers_sorted,
                  h.spawned_has_owner, ?_, fun u st hts' hrun => h.runnable_queued u st hts' hrun,
                  h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                  ?_, ?_, ?_, ?_, ?_, ?_, h.timed_waiters_exclusive⟩
                · intro u cc hown
                  obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
                  by_cases hcc : cc = b
                  · subst hcc; exact ⟨mb.enqueue ⟨s.nextMsgId, s.taskOwner t, m⟩, by simp [upd_self]⟩
                  · exact ⟨mbc, by simp [upd, if_neg hcc, hmbc]⟩
                · intro u p hp; exact h.parent_lt u p (by simpa [step, hrt, hts, how, hmb, hw] using hp)
                · intro u p hp
                  obtain ⟨st, hst⟩ := h.parent_spawned u p
                    (by simpa [step, hrt, hts, how, hmb, hw] using hp)
                  exact ⟨st, by simpa [step, hrt, hts, how, hmb, hw] using hst⟩
                · -- occ_fresh
                  intro ac mc env hmbc henv
                  by_cases hac : ac = b
                  · subst hac; simp only [upd_self] at hmbc
                    have hmc := Option.some.inj hmbc; subst hmc
                    simp only [Mailbox.enqueue, List.mem_append, List.mem_singleton] at henv
                    rcases henv with henv | rfl
                    · exact Nat.lt_succ_of_lt (h.occ_fresh _ mb env hmb henv)
                    · exact Nat.lt_succ_self _
                  · simp only [upd, if_neg hac] at hmbc
                    exact Nat.lt_succ_of_lt (h.occ_fresh ac mc env hmbc henv)
                · -- occ_nodup
                  intro ac mc hmbc
                  by_cases hac : ac = b
                  · subst hac; simp only [upd_self] at hmbc
                    have hmc := Option.some.inj hmbc; subst hmc
                    simp only [Mailbox.enqueue, List.map_append, List.map_singleton]
                    exact nodup_append_singleton (h.occ_nodup _ mb hmb) (nextMsgId_fresh h hmb)
                  · simp only [upd, if_neg hac] at hmbc; exact h.occ_nodup ac mc hmbc
                · -- occ_disjoint (RFC 033): send nil
                  intro ac bc mba mbb hab hmba hmbb ea hea eb heb
                  by_cases hac : ac = b <;> by_cases hbc : bc = b
                  · exact absurd (hac.trans hbc.symm) hab
                  · simp only [hac, upd_self] at hmba
                    have hv := Option.some.inj hmba; subst hv
                    simp only [upd, if_neg hbc] at hmbb
                    simp only [Mailbox.enqueue, List.mem_append, List.mem_singleton] at hea
                    rcases hea with hea | rfl
                    · exact h.occ_disjoint ac bc mb mbb hab (hac ▸ hmb) hmbb ea hea eb heb
                    · intro heq; exact Nat.lt_irrefl _ (heq ▸ h.occ_fresh bc mbb eb hmbb heb)
                  · simp only [hbc, upd_self] at hmbb
                    have hv := Option.some.inj hmbb; subst hv
                    simp only [upd, if_neg hac] at hmba
                    simp only [Mailbox.enqueue, List.mem_append, List.mem_singleton] at heb
                    rcases heb with heb | rfl
                    · exact h.occ_disjoint ac bc mba mb hab hmba (hbc ▸ hmb) ea hea eb heb
                    · intro heq; exact Nat.lt_irrefl _ (heq.symm ▸ h.occ_fresh ac mba ea hmba hea)
                  · simp only [upd, if_neg hac] at hmba; simp only [upd, if_neg hbc] at hmbb
                    exact h.occ_disjoint ac bc mba mbb hab hmba hmbb ea hea eb heb
                · -- owner_spawned (RFC 038): taskOwner unchanged; taskState = s.taskState
                  intro u a' how'
                  exact h.owner_spawned u a' how'
                · -- parent_child_spawned (RFC 038): taskParent unchanged; taskState = s.taskState
                  intro u p hp
                  exact h.parent_child_spawned u p hp
                · intro u hu; exact h.timed_has_deadline u hu
                · intro u dv hd; exact h.deadline_is_timed u dv hd
                · intro u hu; exact h.timed_has_timer u hu
                · intro u hu; exact h.timed_is_waiter u hu
                · intro a' u hm; exact h.timed_waiters_valid a' u hm
                · intro a'; exact h.timed_waiters_nodup a'
              · -- Timed waiter (hwws: timedMailboxWaiters b = w :: ws)
                obtain ⟨w, ws, hwws⟩ : ∃ w ws, s.timedMailboxWaiters b = w :: ws := by
                  cases h' : s.timedMailboxWaiters b with
                  | nil => exact absurd h' htw
                  | cons w ws => exact ⟨w, ws, rfl⟩
                have hwtt : s.taskState w = some .waitingTimed :=
                  h.timed_waiters_valid b w (hwws ▸ List.mem_cons_self w ws)
                have hwq : w ∉ s.readyQ := fun hm =>
                  absurd (h.readyQ_queued w hm) (by simp [hwtt, Option.any, TaskState.isRunnable])
                have hwne : w ≠ t := by
                  intro he; subst he; exact absurd hwtt (by rw [h.running_runs w hrt]; simp)
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
               ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · -- readyQ_nodup
                  simp [step, hrt, hts, how, hmb, hw, hwws]
                  exact nodup_append_singleton h.readyQ_nodup hwq
                · -- readyQ_queued
                  intro u hm; simp [step, hrt, hts, how, hmb, hw, hwws] at hm ⊢
                  rcases hm with hm | rfl
                  · by_cases hue : u = w
                    · simp [upd_self, hue, Option.any, TaskState.isRunnable]
                    · simp [upd_ne _ _ hue]; exact h.readyQ_queued u hm
                  · simp [upd_self, Option.any, TaskState.isRunnable]
                · -- running_runs
                  intro u hru; simp [step, hrt, hts, how, hmb, hw, hwws] at hru ⊢
                  by_cases hue : u = w
                  · exact False.elim (hwne (hue ▸ hru : t = w).symm)
                  · simp [upd_ne _ _ hue]; exact h.running_runs u (by rw [← hru]; exact hrt)
                · -- timers_nodup
                  simp [step, hrt, hts, how, hmb, hw, hwws]
                  exact nodup_of_sublist
                    (List.Sublist.map TimerEntry.task (List.filter_sublist _)) h.timers_nodup
                · -- timers_sleep
                  intro e he; simp [step, hrt, hts, how, hmb, hw, hwws] at he ⊢
                  -- After simp, he : e ∈ s.timers ∧ ¬(e.task = w)
                  have hne' : e.task ≠ w := by simpa using he.2
                  simp [upd_ne _ _ hne']; exact h.timers_sleep e he.1
                · -- fresh_none
                  intro u hu; simp [step, hrt, hts, how, hmb, hw, hwws] at hu ⊢
                  have huw : u ≠ w := fun he => by
                    have := h.fresh_none u hu; rw [he] at this; rw [this] at hwtt; simp at hwtt
                  simp [upd_ne _ _ huw]; exact h.fresh_none u hu
                · -- timers_sorted
                  simp [step, hrt, hts, how, hmb, hw, hwws]
                  exact h.timers_sorted.sublist (List.filter_sublist _)
                · -- spawned_has_owner
                  intro u st hts'; simp [step, hrt, hts, how, hmb, hw, hwws] at hts' ⊢
                  by_cases hue : u = w
                  · simp [upd_self, hue] at hts'; exact h.spawned_has_owner u .waitingTimed (hue ▸ hwtt)
                  · simp [upd_ne _ _ hue] at hts' ⊢; exact h.spawned_has_owner u st hts'
                · -- owned_has_mailbox
                  intro u cc hown; simp only [send_taskOwner] at hown
                  obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
                  exact send_mailbox_isSome hmbc m
                · -- runnable_queued
                  intro u st hts' hrun; simp [step, hrt, hts, how, hmb, hw, hwws] at hts' ⊢
                  by_cases hue : u = w
                  · simp [hue, upd_self] at hts'; exact Or.inr hue
                  · simp [upd_ne _ _ hue] at hts'; exact Or.inl (h.runnable_queued u st hts' hrun)
                · -- waiters_waiting: mailboxWaiters unchanged (we changed timedMailboxWaiters)
                  intro a' u hm; simp [step, hrt, hts, how, hmb, hw, hwws] at hm ⊢
                  have huw : u ≠ w := fun he => by
                    have hw_wait := h.waiters_waiting a' u hm
                    rw [he] at hw_wait
                    rw [hw_wait] at hwtt; simp at hwtt
                  simp [upd_ne _ _ huw]; exact h.waiters_waiting a' u hm
                · -- waiters_owned
                  intro a' u hm; simp [step, hrt, hts, how, hmb, hw, hwws] at hm ⊢
                  exact h.waiters_owned a' u hm
                · -- waiting_queued
                  intro u hts'; simp [step, hrt, hts, how, hmb, hw, hwws] at hts' ⊢
                  by_cases hue : u = w
                  · simp [hue, upd_self] at hts'
                  · simp [upd_ne _ _ hue] at hts'
                    obtain ⟨a, ha, hmw⟩ := h.waiting_queued u hts'
                    exact ⟨a, ha, hmw⟩
                · -- waiters_nodup
                  intro a'; simp [step, hrt, hts, how, hmb, hw, hwws]
                  exact h.waiters_nodup a'
                · -- parent_lt
                  intro u p hp
                  exact h.parent_lt u p (by simpa [step, hrt, hts, how, hmb, hw, hwws] using hp)
                · -- parent_spawned
                  intro u p hp
                  obtain ⟨st, hst⟩ := h.parent_spawned u p (by simpa [step, hrt, hts, how, hmb, hw, hwws] using hp)
                  exact step_preserves_spawned hst _
                · -- occ_fresh: nextMsgId + 1; mailbox b updated
                  intro ac mc env hmbc henv
                  have hmi : ((step s (.send t b m)).1).nextMsgId = s.nextMsgId + 1 := by
                    simp [step, hrt, hts, how, hmb, hw, hwws]
                  rw [hmi]
                  by_cases hac : ac = b
                  · rw [hac, send_appends hrt hts how hmb m] at hmbc
                    have hv := Option.some.inj hmbc; subst hv
                    simp only [List.mem_append, List.mem_singleton] at henv
                    rcases henv with henv | rfl
                    · exact Nat.lt_succ_of_lt (h.occ_fresh _ mb env hmb henv)
                    · exact Nat.lt_succ_self _
                  · rw [send_preserves_other hac m] at hmbc
                    exact Nat.lt_succ_of_lt (h.occ_fresh ac mc env hmbc henv)
                · -- occ_nodup
                  intro ac mc hmbc
                  by_cases hac : ac = b
                  · rw [hac, send_appends hrt hts how hmb m] at hmbc
                    have hv := Option.some.inj hmbc; subst hv
                    simp only [List.map_append, List.map_singleton]
                    exact nodup_append_singleton (h.occ_nodup _ mb hmb) (nextMsgId_fresh h hmb)
                  · rw [send_preserves_other hac m] at hmbc
                    exact h.occ_nodup ac mc hmbc
                · -- occ_disjoint
                  intro ac bc mba mbb hab hmba hmbb ea hea eb heb
                  by_cases hac : ac = b <;> by_cases hbc : bc = b
                  · exact absurd (hac.trans hbc.symm) hab
                  · rw [hac, send_appends hrt hts how hmb m] at hmba
                    have hv := Option.some.inj hmba; subst hv
                    rw [send_preserves_other hbc m] at hmbb
                    simp only [List.mem_append, List.mem_singleton] at hea
                    rcases hea with hea | rfl
                    · exact h.occ_disjoint ac bc mb mbb hab (hac ▸ hmb) hmbb ea hea eb heb
                    · intro heq; exact Nat.lt_irrefl _ (heq ▸ h.occ_fresh bc mbb eb hmbb heb)
                  · rw [hbc, send_appends hrt hts how hmb m] at hmbb
                    have hv := Option.some.inj hmbb; subst hv
                    rw [send_preserves_other hac m] at hmba
                    simp only [List.mem_append, List.mem_singleton] at heb
                    rcases heb with heb | rfl
                    · exact h.occ_disjoint ac bc mba mb hab hmba (hbc ▸ hmb) ea hea eb heb
                    · intro heq; exact Nat.lt_irrefl _ (heq.symm ▸ h.occ_fresh ac mba ea hmba hea)
                  · rw [send_preserves_other hac m] at hmba
                    rw [send_preserves_other hbc m] at hmbb
                    exact h.occ_disjoint ac bc mba mbb hab hmba hmbb ea hea eb heb
                · -- owner_spawned
                  intro u a' how'
                  obtain ⟨st, hst⟩ := h.owner_spawned u a'
                    (by simpa [step, hrt, hts, how, hmb, hw, hwws] using how')
                  exact step_preserves_spawned hst _
                · -- parent_child_spawned
                  intro u p hp
                  obtain ⟨st, hst⟩ := h.parent_child_spawned u p
                    (by simpa [step, hrt, hts, how, hmb, hw, hwws] using hp)
                  exact step_preserves_spawned hst _
                · -- timed_has_deadline
                  intro u hu
                  have huw : u ≠ w := fun he => by
                    simp [step, hrt, hts, how, hmb, hw, hwws, he, upd_self] at hu
                  have hu' : s.taskState u = some .waitingTimed := by
                    simpa [step, hrt, hts, how, hmb, hw, hwws, upd_ne _ _ huw] using hu
                  obtain ⟨dv, hdv⟩ := h.timed_has_deadline u hu'
                  exact ⟨dv, by simpa [step, hrt, hts, how, hmb, hw, hwws, if_neg huw] using hdv⟩
                · -- deadline_is_timed
                  intro u dv hd
                  have huw : u ≠ w := fun he => by
                    simp [step, hrt, hts, how, hmb, hw, hwws, he] at hd
                  have hd' : s.waitDeadline u = some dv := by
                    simpa [step, hrt, hts, how, hmb, hw, hwws, if_neg huw] using hd
                  simpa [step, hrt, hts, how, hmb, hw, hwws, upd_ne _ _ huw] using
                    h.deadline_is_timed u dv hd'
                · -- timed_has_timer
                  intro u hu
                  have huw : u ≠ w := fun he => by
                    simp [step, hrt, hts, how, hmb, hw, hwws, he, upd_self] at hu
                  have hu' : s.taskState u = some .waitingTimed := by
                    simpa [step, hrt, hts, how, hmb, hw, hwws, upd_ne _ _ huw] using hu
                  obtain ⟨e, he, hek⟩ := h.timed_has_timer u hu'
                  have hewne : e.task ≠ w := fun heq => huw (hek ▸ heq)
                  exact ⟨e, by simpa [step, hrt, hts, how, hmb, hw, hwws, hewne] using he, hek⟩
                · -- timed_is_waiter
                  intro u hu
                  have huw : u ≠ w := fun he => by
                    simp [step, hrt, hts, how, hmb, hw, hwws, he, upd_self] at hu
                  have hu' : s.taskState u = some .waitingTimed := by
                    simpa [step, hrt, hts, how, hmb, hw, hwws, upd_ne _ _ huw] using hu
                  obtain ⟨ac, hac⟩ := h.timed_is_waiter u hu'
                  by_cases hab : ac = b
                  · -- u was in timedMailboxWaiters b = w :: ws; since u ≠ w, u ∈ ws
                    have hac_b : u ∈ s.timedMailboxWaiters b := hab ▸ hac
                    have hu_ws : u ∈ ws := (List.mem_cons.mp (hwws ▸ hac_b)).resolve_left huw
                    exact ⟨b, by simpa [step, hrt, hts, how, hmb, hw, hwws, hab] using hu_ws⟩
                  · exact ⟨ac, by simpa [step, hrt, hts, how, hmb, hw, hwws, if_neg hab] using hac⟩
                · -- timed_waiters_valid
                  intro a' u hm
                  by_cases hab : a' = b
                  · -- a' = b: u was woken from timedMailboxWaiters b = w :: ws  
                    have hm' : u ∈ ws := by simpa [step, hrt, hts, how, hmb, hw, hwws, hab] using hm
                    have huw : u ≠ w := fun he =>
                      absurd (he ▸ hm') (List.nodup_cons.mp (hwws ▸ h.timed_waiters_nodup b)).1
                    simpa [step, hrt, hts, how, hmb, hw, hwws, upd_ne s.taskState (some .ready) huw] using
                      h.timed_waiters_valid b u (hwws ▸ List.mem_cons_of_mem w hm')
                  · -- a' ≠ b: membership in s.timedMailboxWaiters a' unchanged
                    have htmeq : (step s (.send t b m)).1.timedMailboxWaiters a' = s.timedMailboxWaiters a' := by
                      simp [step, hrt, hts, how, hmb, hw, hwws, hab]
                    have hm' : u ∈ s.timedMailboxWaiters a' := htmeq ▸ hm
                    -- u ≠ w: if u = w, then w ∈ timedMailboxWaiters a' (a' ≠ b) but w ∈ timedMailboxWaiters b
                    have hw_in_b : w ∈ s.timedMailboxWaiters b := hwws ▸ List.mem_cons_self w ws
                    have huw : u ≠ w := fun he =>
                      h.timed_waiters_exclusive a' b u hab hm' (he ▸ hw_in_b)
                    have hval : s.taskState u = some .waitingTimed := h.timed_waiters_valid a' u hm'
                    have htseq : (step s (.send t b m)).1.taskState u = s.taskState u := by
                      simp [step, hrt, hts, how, hmb, hw, hwws, upd_ne _ _ huw]
                    exact htseq.trans hval
                · -- timed_waiters_nodup
                  intro a'
                  by_cases hab : a' = b
                  · simpa [step, hrt, hts, how, hmb, hw, hwws, hab] using
                      (List.nodup_cons.mp (hwws ▸ h.timed_waiters_nodup b)).2
                  · simpa [step, hrt, hts, how, hmb, hw, hwws, if_neg hab] using
                      h.timed_waiters_nodup a'
                · -- timed_waiters_exclusive
                  intro a' b' u hab' hma hmb'
                  -- Both a' and b' cannot be b simultaneously since hab' : a' ≠ b'
                  by_cases ha : a' = b <;> by_cases hb : b' = b
                  · -- a' = b, b' = b: contradicts hab'
                    exact absurd (ha.trans hb.symm) hab'
                  · -- a' = b: u ∈ ws; b' ≠ b: u ∈ s.timedMailboxWaiters b'
                    have hu_ws : u ∈ ws := by simpa [step, hrt, hts, how, hmb, hw, hwws, ha] using hma
                    have hms_b' : u ∈ s.timedMailboxWaiters b' := by simpa [step, hrt, hts, how, hmb, hw, hwws, if_neg hb] using hmb'
                    exact h.timed_waiters_exclusive b b' u (fun h' => hb h'.symm) (hwws ▸ List.mem_cons_of_mem w hu_ws) hms_b'
                  · -- a' ≠ b: u ∈ s.timedMailboxWaiters a'; b' = b: u ∈ ws
                    have hms_a' : u ∈ s.timedMailboxWaiters a' := by simpa [step, hrt, hts, how, hmb, hw, hwws, if_neg ha] using hma
                    have hu_ws : u ∈ ws := by simpa [step, hrt, hts, how, hmb, hw, hwws, hb] using hmb'
                    exact h.timed_waiters_exclusive a' b u ha hms_a' (hwws ▸ List.mem_cons_of_mem w hu_ws)
                  · -- a' ≠ b, b' ≠ b: both in s.timedMailboxWaiters
                    have hms_a' := by simpa [step, hrt, hts, how, hmb, hw, hwws, if_neg ha] using hma
                    have hms_b' := by simpa [step, hrt, hts, how, hmb, hw, hwws, if_neg hb] using hmb'
                    exact h.timed_waiters_exclusive a' b' u hab' hms_a' hms_b'
            | cons w ws =>
              have hwt  : s.taskState w = some .waiting := h.waiters_waiting b w (hw ▸ List.mem_cons_self w ws)
              have hwq  : w ∉ s.readyQ := waiting_not_in_readyQ h hwt
              have hwne : w ≠ t := waiter_ne_running h hwt hrt
              -- The step wakes w to .ready and bumps nextMsgId
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · -- readyQ_nodup
                simp [step, hrt, hts, how, hmb, hw]
                exact nodup_append_singleton h.readyQ_nodup hwq
              · -- readyQ_queued
                intro u hm; simp [step, hrt, hts, how, hmb, hw] at hm ⊢
                rcases hm with hm | rfl
                · by_cases hue : u = w
                  · simp [upd_self, hue, Option.any, TaskState.isRunnable]
                  · simp [upd_ne _ _ hue]; exact h.readyQ_queued u hm
                · simp [upd_self, Option.any, TaskState.isRunnable]
              · -- running_runs
                intro u hru; simp [step, hrt, hts, how, hmb, hw] at hru ⊢
                by_cases hue : u = w
                · exact False.elim (hwne (hue.symm.trans hru.symm))
                · simp [upd_ne _ _ hue]; exact h.running_runs u (hru ▸ hrt)
              · simp [step, hrt, hts, how, hmb, hw]
                exact nodup_of_sublist (List.Sublist.map TimerEntry.task (List.filter_sublist _)) h.timers_nodup
              · -- timers_sleep
                intro e he; simp [step, hrt, hts, how, hmb, hw] at he ⊢
                have hts_e := h.timers_sleep e he.1
                by_cases hne : e.task = w
                · exact absurd (hne ▸ hts_e) (by simp [hwt])
                · simp [upd_ne _ _ hne]; exact hts_e
              · -- fresh_none
                intro u hu; simp [step, hrt, hts, how, hmb, hw] at hu ⊢
                by_cases hue : u = w
                · exact absurd hwt (by simp [← hue, h.fresh_none u hu])
                · simp [upd_ne _ _ hue]; exact h.fresh_none u hu
              · simp [step, hrt, hts, how, hmb, hw]; exact h.timers_sorted.sublist (List.filter_sublist _)
              · -- spawned_has_owner
                intro u st hts'; simp [step, hrt, hts, how, hmb, hw] at hts' ⊢
                by_cases hue : u = w
                · simp [upd_self, hue] at hts' ⊢; exact h.spawned_has_owner w .waiting hwt
                · simp [upd_ne _ _ hue] at hts' ⊢; exact h.spawned_has_owner u st hts'
              · -- owned_has_mailbox
                intro u cc hown; simp only [send_taskOwner] at hown
                obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
                exact send_mailbox_isSome hmbc m
              · -- runnable_queued
                intro u st hts' hrun; simp [step, hrt, hts, how, hmb, hw] at hts' ⊢
                by_cases hue : u = w
                · simp [hue, upd_self] at hts'; exact Or.inr hue
                · simp [upd_ne _ _ hue] at hts'; exact Or.inl (h.runnable_queued u st hts' hrun)
              · -- waiters_waiting
                intro a' u hm; simp [step, hrt, hts, how, hmb, hw] at hm ⊢
                by_cases hab : a' = b
                · simp only [if_pos hab] at hm
                  have hmem : u ∈ s.mailboxWaiters b := hw ▸ List.mem_cons_of_mem w hm
                  have hue : u ≠ w := fun he => (List.nodup_cons.mp (hw ▸ h.waiters_nodup b)).1 (he ▸ hm)
                  simp [upd_ne _ _ hue, hab]; exact h.waiters_waiting b u hmem
                · simp only [if_neg hab] at hm
                  have hts_u := h.waiters_waiting a' u hm
                  have hue : u ≠ w := fun he => by
                    have ho1 : s.taskOwner w = some a' := he ▸ h.waiters_owned a' u hm
                    have ho2 : s.taskOwner w = some b  := h.waiters_owned b w (hw ▸ List.mem_cons_self w ws)
                    exact hab (Option.some.inj (ho1.symm.trans ho2))
                  simp [upd_ne _ _ hue, hab]; exact hts_u
              · -- waiters_owned
                intro a' u hm; simp [step, hrt, hts, how, hmb, hw] at hm ⊢
                by_cases hab : a' = b
                · simp only [if_pos hab] at hm
                  exact hab ▸ h.waiters_owned b u (hw ▸ List.mem_cons_of_mem w hm)
                · simp only [if_neg hab] at hm ⊢; exact h.waiters_owned a' u hm
              · -- waiting_queued
                intro u hts'; simp [step, hrt, hts, how, hmb, hw] at hts' ⊢
                by_cases hue : u = w
                · simp [hue, upd_self] at hts'
                · simp [upd_ne _ _ hue] at hts'
                  obtain ⟨a', ha', hmem⟩ := h.waiting_queued u hts'
                  refine ⟨a', ha', ?_⟩
                  by_cases hab : a' = b
                  · simp only [if_pos hab]; exact waiter_in_tail h hw (by rwa [hab] at hmem) hue
                  · simp only [if_neg hab]; exact hmem
              · -- waiters_nodup
                intro a'; simp [step, hrt, hts, how, hmb, hw]
                by_cases hab : a' = b
                · simp only [if_pos hab]
                  exact (List.nodup_cons.mp (hw ▸ h.waiters_nodup b)).2
                · simp only [if_neg hab]; exact h.waiters_nodup a'
              · -- parent_lt
                intro u p hp
                exact h.parent_lt u p (by simpa [step, hrt, hts, how, hmb, hw] using hp)
              · -- parent_spawned (RFC 042)
                intro u p hp
                obtain ⟨st, hst⟩ := h.parent_spawned u p (by simpa [step, hrt, hts, how, hmb, hw] using hp)
                exact step_preserves_spawned hst _
              · -- occ_fresh (RFC 033): send cons, nextMsgId + 1
                intro ac mc env hmbc henv
                have hmi : ((step s (.send t b m)).1).nextMsgId = s.nextMsgId + 1 := by
                  simp [step, hrt, hts, how, hmb, hw]
                rw [hmi]
                by_cases hac : ac = b
                · rw [hac, send_appends hrt hts how hmb m] at hmbc
                  have hv := Option.some.inj hmbc; subst hv
                  simp only [List.mem_append, List.mem_singleton] at henv
                  rcases henv with henv | rfl
                  · exact Nat.lt_succ_of_lt (h.occ_fresh _ mb env hmb henv)
                  · exact Nat.lt_succ_self _
                · rw [send_preserves_other hac m] at hmbc
                  exact Nat.lt_succ_of_lt (h.occ_fresh ac mc env hmbc henv)
              · -- occ_nodup (RFC 033): send cons
                intro ac mc hmbc
                by_cases hac : ac = b
                · rw [hac, send_appends hrt hts how hmb m] at hmbc
                  have hv := Option.some.inj hmbc; subst hv
                  simp only [List.map_append, List.map_singleton]
                  exact nodup_append_singleton (h.occ_nodup _ mb hmb) (nextMsgId_fresh h hmb)
                · rw [send_preserves_other hac m] at hmbc
                  exact h.occ_nodup ac mc hmbc
              · -- occ_disjoint (RFC 033): send cons
                intro ac bc mba mbb hab hmba hmbb ea hea eb heb
                by_cases hac : ac = b <;> by_cases hbc : bc = b
                · exact absurd (hac.trans hbc.symm) hab
                · rw [hac, send_appends hrt hts how hmb m] at hmba
                  have hv := Option.some.inj hmba; subst hv
                  rw [send_preserves_other hbc m] at hmbb
                  simp only [List.mem_append, List.mem_singleton] at hea
                  rcases hea with hea | rfl
                  · exact h.occ_disjoint ac bc mb mbb hab (hac ▸ hmb) hmbb ea hea eb heb
                  · intro heq; exact Nat.lt_irrefl _ (heq ▸ h.occ_fresh bc mbb eb hmbb heb)
                · rw [hbc, send_appends hrt hts how hmb m] at hmbb
                  have hv := Option.some.inj hmbb; subst hv
                  rw [send_preserves_other hac m] at hmba
                  simp only [List.mem_append, List.mem_singleton] at heb
                  rcases heb with heb | rfl
                  · exact h.occ_disjoint ac bc mba mb hab hmba (hbc ▸ hmb) ea hea eb heb
                  · intro heq; exact Nat.lt_irrefl _ (heq.symm ▸ h.occ_fresh ac mba ea hmba hea)
                · rw [send_preserves_other hac m] at hmba
                  rw [send_preserves_other hbc m] at hmbb
                  exact h.occ_disjoint ac bc mba mbb hab hmba hmbb ea hea eb heb
              · -- owner_spawned (RFC 038): taskOwner unchanged by send
                intro u a' how'
                obtain ⟨st, hst⟩ := h.owner_spawned u a'
                  (by simpa [step, hrt, hts, how, hmb, hw] using how')
                exact step_preserves_spawned hst _
              · -- parent_child_spawned (RFC 038): taskParent unchanged by send
                intro u p hp
                obtain ⟨st, hst⟩ := h.parent_child_spawned u p
                  (by simpa [step, hrt, hts, how, hmb, hw] using hp)
                exact step_preserves_spawned hst _
              · -- timed_has_deadline
                intro u hu; simp [step, hrt, hts, how, hmb, hw] at hu
                have huw : u ≠ w := by intro he; simp [he, upd_self] at hu
                have hu' : s.taskState u = some .waitingTimed := by simpa [upd_ne _ _ huw] using hu
                obtain ⟨dl, hdl⟩ := h.timed_has_deadline u hu'
                exact ⟨dl, by simpa [step, hrt, hts, how, hmb, hw, huw] using hdl⟩
              · -- deadline_is_timed
                intro u dv hd; simp [step, hrt, hts, how, hmb, hw] at hd
                have huw : u ≠ w := by intro he; simp [he] at hd
                have hd' : s.waitDeadline u = some dv := by simpa [huw] using hd
                simpa [step, hrt, hts, how, hmb, hw, upd_ne _ _ huw] using h.deadline_is_timed u dv hd'
              · -- timed_has_timer
                intro u hu; simp [step, hrt, hts, how, hmb, hw] at hu ⊢
                have huw : u ≠ w := by intro he; simp [he, upd_self] at hu
                simp [upd_ne _ _ huw] at hu
                obtain ⟨e, he, hek⟩ := h.timed_has_timer u hu
                have hewne : e.task ≠ w := fun heq => huw (hek ▸ heq)
                exact ⟨e, by simp [he, hewne], hek⟩
              · -- timed_is_waiter
                intro u hu; simp [step, hrt, hts, how, hmb, hw] at hu ⊢
                have huw : u ≠ w := by intro he; simp [he, upd_self] at hu
                simp [upd_ne _ _ huw] at hu; exact h.timed_is_waiter u hu
              · -- timed_waiters_valid
                intro a' u hm; simp [step, hrt, hts, how, hmb, hw] at hm ⊢
                have huw : u ≠ w := by
                  intro he; rw [he] at hm
                  exact absurd (h.timed_waiters_valid a' w hm) (by simp [hwt])
                simp [upd_ne _ _ huw]; exact h.timed_waiters_valid a' u hm
              · -- timed_waiters_nodup
                intro a'; simpa [step, hrt, hts, how, hmb, hw] using h.timed_waiters_nodup a'
              · -- timed_waiters_exclusive
                intro a' b' u hab' hma hmb'
                exact h.timed_waiters_exclusive a' b' u hab'
                  (by simpa [step, hrt, hts, how, hmb, hw] using hma)
                  (by simpa [step, hrt, hts, how, hmb, hw] using hmb')
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed =>
        simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h

-- ─── receive: WellFormed preservation ─────────────────────────────────────

theorem preserves_wf_receive {s : RuntimeState} (h : WellFormed s)
    {t : TaskId} :
    WellFormed ((step s (.receive t)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some st => cases st with
      | running => cases how : s.taskOwner t with
        | none => simpa [step, hrt, hts, how] using h
        | some a => cases hmb : s.mailboxes a with
          | none => simpa [step, hrt, hts, how, hmb] using h
          | some mb => cases hd : mb.dequeue with
            | some p =>
              obtain ⟨env, rest⟩ := p
              -- receive dequeues head envelope; nextMsgId unchanged
              have hstep_d : (step s (.receive t)).1 =
                  { s with mailboxes := upd s.mailboxes a (some rest) } := by
                simp [step, hrt, hts, how, hmb, hd]
              -- Extract head/tail relationship
              have hcons : mb.messages = env :: rest.messages := by
                have := Mailbox.dequeue_spec mb; rw [hd] at this; exact this
              rw [hstep_d]
              refine ⟨h.readyQ_nodup, fun u hm => h.readyQ_queued u hm, h.running_runs,
                h.timers_nodup, h.timers_sleep, h.fresh_none, h.timers_sorted,
                h.spawned_has_owner, ?_, fun u st hts' hrun => h.runnable_queued u st hts' hrun,
                h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                h.timed_has_deadline, h.deadline_is_timed, h.timed_has_timer, h.timed_is_waiter,
                h.timed_waiters_valid, h.timed_waiters_nodup, h.timed_waiters_exclusive⟩
              · intro u cc hown
                obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
                by_cases hcc : cc = a
                · exact ⟨rest, by simp [upd, hcc]⟩
                · exact ⟨mbc, by simp [upd, if_neg hcc, hmbc]⟩
              · intro u p hp; exact h.parent_lt u p
                  (by simpa [step, hrt, hts, how, hmb, hd] using hp)
              · intro u p hp
                obtain ⟨st, hst⟩ := h.parent_spawned u p
                  (by simpa [step, hrt, hts, how, hmb, hd] using hp)
                exact ⟨st, by simpa [step, hrt, hts, how, hmb, hd] using hst⟩
              · -- occ_fresh: nextMsgId unchanged, rest ⊆ mb (RFC 033)
                intro ac mc env2 hmbc henv2
                by_cases hac : ac = a
                · rw [hac] at hmbc; simp only [upd_self] at hmbc
                  have hv := Option.some.inj hmbc; subst hv
                  exact h.occ_fresh ac mb env2 (hac ▸ hmb) (hcons ▸ List.mem_cons_of_mem _ henv2)
                · simp only [upd, if_neg hac] at hmbc; exact h.occ_fresh ac mc env2 hmbc henv2
              · -- occ_nodup: rest ⊆ mb (RFC 033)
                intro ac mc hmbc
                by_cases hac : ac = a
                · rw [hac] at hmbc; simp only [upd_self] at hmbc
                  have hv := Option.some.inj hmbc; subst hv
                  have hnd := h.occ_nodup ac mb (hac ▸ hmb)
                  rw [hcons, List.map_cons, List.nodup_cons] at hnd
                  exact hnd.2
                · simp only [upd, if_neg hac] at hmbc; exact h.occ_nodup ac mc hmbc
              · -- occ_disjoint: rest ⊆ mb (RFC 033)
                intro ac bc mba mbb hab hmba hmbb ea hea eb heb
                by_cases hac : ac = a <;> by_cases hbc : bc = a
                · exact absurd (hac.trans hbc.symm) hab
                · rw [hac] at hmba; simp only [upd_self] at hmba
                  have hv := Option.some.inj hmba; subst hv
                  simp only [upd, if_neg hbc] at hmbb
                  exact h.occ_disjoint ac bc mb mbb hab (hac ▸ hmb) hmbb
                    ea (hcons ▸ List.mem_cons_of_mem _ hea) eb heb
                · rw [hbc] at hmbb; simp only [upd_self] at hmbb
                  have hv := Option.some.inj hmbb; subst hv
                  simp only [upd, if_neg hac] at hmba
                  exact h.occ_disjoint ac bc mba mb hab hmba (hbc ▸ hmb)
                    ea hea eb (hcons ▸ List.mem_cons_of_mem _ heb)
                · simp only [upd, if_neg hac] at hmba; simp only [upd, if_neg hbc] at hmbb
                  exact h.occ_disjoint ac bc mba mbb hab hmba hmbb ea hea eb heb
              · -- owner_spawned (RFC 038): taskOwner unchanged; taskState = s.taskState
                intro u a' how'
                exact h.owner_spawned u a' how'
              · -- parent_child_spawned (RFC 038): taskParent unchanged; taskState = s.taskState
                intro u p hp
                exact h.parent_child_spawned u p hp
            | none =>
              have ht_not_waiter : t ∉ s.mailboxWaiters a := fun hmem =>
                absurd (h.waiters_waiting a t hmem) (by simp [hts])
              have hstep_p : (step s (.receive t)).1 =
                  { s with taskState := upd s.taskState t (some .waiting), running := none,
                            mailboxWaiters := fun ac => if ac = a then s.mailboxWaiters a ++ [t]
                                                        else s.mailboxWaiters ac } := by
                simp [step, hrt, hts, how, hmb, hd]
              rw [hstep_p]
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact h.readyQ_nodup
              · intro u hm
                by_cases hut : u = t
                · simp [hut] at hm ⊢; have := h.readyQ_queued t hm
                  simp [hts, Option.any, TaskState.isRunnable] at this
                · simp [upd_ne _ _ hut]; exact h.readyQ_queued u hm
              · intro u hru; exact absurd hru (by simp)
              · exact h.timers_nodup
              · intro e he; have hts_e := h.timers_sleep e he
                by_cases hne : e.task = t
                · exact absurd (hne ▸ hts_e) (by simp [hts])
                · simp only [upd_ne _ _ hne]; exact hts_e
              · intro u hu
                by_cases hut : u = t
                · simp [hut] at hu ⊢; exact absurd hts (by simp [h.fresh_none t hu])
                · simp [upd_ne _ _ hut]; exact h.fresh_none u hu
              · exact h.timers_sorted
              · intro u st hts''
                by_cases hut : u = t
                · simp only [upd_self] at hts''; exact ⟨a, by rw [hut]; exact how⟩
                · simp only [upd_ne _ _ hut] at hts''; exact h.spawned_has_owner u st hts''
              · intro u cc hown
                obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
                exact ⟨mbc, hmbc⟩
              · intro u st hts'' hrun
                by_cases hut : u = t
                · simp only [hut, upd_self] at hts''
                  have hst := Option.some.inj hts''.symm; subst hst
                  simp [TaskState.isRunnable] at hrun
                · simp [upd_ne _ _ hut] at hts''; exact h.runnable_queued u st hts'' hrun
              · intro ac u hm
                by_cases hac : ac = a
                · simp only [if_pos hac] at hm ⊢
                  rcases List.mem_append.mp hm with hm | hm
                  · have hts_u := h.waiters_waiting a u hm
                    have hut : u ≠ t := fun he => absurd (he ▸ hts_u) (by simp [hts])
                    simp [upd_ne _ _ hut]; exact hts_u
                  · simp only [List.mem_singleton] at hm; simp [hm, upd_self]
                · simp only [if_neg hac] at hm ⊢
                  have hts_u := h.waiters_waiting ac u hm
                  have hut : u ≠ t := fun he => absurd (he ▸ hts_u) (by simp [hts])
                  simp [upd_ne _ _ hut]; exact hts_u
              · intro ac u hm
                by_cases hac : ac = a
                · simp only [if_pos hac] at hm ⊢
                  rcases List.mem_append.mp hm with hm | hm
                  · exact hac ▸ h.waiters_owned a u hm
                  · simp only [List.mem_singleton] at hm; exact hac ▸ (hm ▸ how)
                · simp only [if_neg hac] at hm ⊢; exact h.waiters_owned ac u hm
              · intro u hts''
                by_cases hut : u = t
                · simp [upd_self, hut] at hts''
                  exact ⟨a, by rw [hut]; exact how, by simp [if_pos rfl, hut]⟩
                · simp [upd_ne _ _ hut] at hts''
                  obtain ⟨a', ha', hmem⟩ := h.waiting_queued u hts''
                  refine ⟨a', ha', ?_⟩
                  by_cases hac : a' = a
                  · simp only [if_pos hac]; exact List.mem_append_left _ (by rwa [hac] at hmem)
                  · simp only [if_neg hac]; exact hmem
              · intro ac
                by_cases hac : ac = a
                · simp only [if_pos hac]
                  exact nodup_append (h.waiters_nodup a) (by simp)
                    (fun u hmem hts_mem => by simp at hts_mem; exact ht_not_waiter (hts_mem ▸ hmem))
                · simp only [if_neg hac]; exact h.waiters_nodup ac
              · -- parent_lt
                exact fun u p hp => h.parent_lt u p (by simpa [step, hrt, hts, how, hmb, hd] using hp)
              · -- parent_spawned: receive parks t → .waiting; still some _
                intro u p hp
                obtain ⟨st, hst⟩ := h.parent_spawned u p
                  (by simpa [step, hrt, hts, how, hmb, hd] using hp)
                by_cases hpt : p = t
                · exact ⟨.waiting, by simp [step, hrt, hts, how, hmb, hd, upd_self, hpt]⟩
                · exact ⟨st, by simp [step, hrt, hts, how, hmb, hd, upd, if_neg hpt]; exact hst⟩
              · -- occ_fresh: mailboxes unchanged, nextMsgId unchanged
                intro a' mb' env hmb' henv; exact h.occ_fresh a' mb' env hmb' henv
              · -- occ_nodup: mailboxes unchanged
                intro a' mb' hmb'; exact h.occ_nodup a' mb' hmb'
              · -- occ_disjoint: mailboxes unchanged
                intro a' b' mba mbb hab hmba hmbb ea hea eb heb
                exact h.occ_disjoint a' b' mba mbb hab hmba hmbb ea hea eb heb
              · -- owner_spawned (RFC 038): taskOwner unchanged; taskState changes at t
                intro u a' how'
                obtain ⟨st, hst⟩ := h.owner_spawned u a' how'
                by_cases hut : u = t
                · subst hut; exact ⟨.waiting, by simp [upd_self]⟩
                · exact ⟨st, by simp [upd_ne _ _ hut]; exact hst⟩
              · -- parent_child_spawned (RFC 038): taskParent unchanged; taskState changes at t
                intro u p hp
                obtain ⟨st, hst⟩ := h.parent_child_spawned u p hp
                by_cases hut : u = t
                · subst hut; exact ⟨.waiting, by simp [upd_self]⟩
                · exact ⟨st, by simp [upd_ne _ _ hut]; exact hst⟩
              · -- timed_has_deadline: t goes to .waiting (not .waitingTimed); others unchanged
                intro u hu
                by_cases hut : u = t
                · simp [hut, upd_self] at hu
                · simp [upd_ne _ _ hut] at hu
                  exact h.timed_has_deadline u hu
              · -- deadline_is_timed: t goes .waiting (no deadline), others unchanged
                intro u dv hd
                -- After rw [hstep_p], hd : { ... }.waitDeadline u = some dv = s.waitDeadline u
                -- (waitDeadline is unchanged). goal: upd s.taskState t .waiting u = .waitingTimed
                have hut : u ≠ t := fun he => by
                  have h1 := h.deadline_is_timed u dv hd
                  rw [he] at h1; rw [h1] at hts; simp at hts
                simp only [upd_ne _ _ hut]; exact h.deadline_is_timed u dv hd
              · -- timed_has_timer: timers unchanged
                intro u hu
                by_cases hut : u = t
                · simp [hut, upd_self] at hu
                · simp [upd_ne _ _ hut] at hu; exact h.timed_has_timer u hu
              · -- timed_is_waiter: timedMailboxWaiters unchanged
                intro u hu
                by_cases hut : u = t
                · simp [hut, upd_self] at hu
                · simp [upd_ne _ _ hut] at hu; exact h.timed_is_waiter u hu
              · -- timed_waiters_valid: timedMailboxWaiters unchanged
                intro a' u hm
                have hut : u ≠ t := fun he => absurd (h.timed_waiters_valid a' u hm) (by simp [he, hts])
                simp [upd_ne _ _ hut]; exact h.timed_waiters_valid a' u hm
              · -- timed_waiters_nodup: timedMailboxWaiters unchanged
                intro a'; exact h.timed_waiters_nodup a'
              · -- timed_waiters_exclusive: timedMailboxWaiters unchanged
                intro a' b' u hab' hma hmb'
                exact h.timed_waiters_exclusive a' b' u hab' hma hmb'
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed =>
        simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h

-- ─── inject: WellFormed preservation ──────────────────────────────────────

theorem preserves_wf_inject {s : RuntimeState} (h : WellFormed s)
    {a : ActorId} {m : Message} :
    WellFormed ((step s (.inject a m)).1) := by
  cases hmb : s.mailboxes a with
  | none => simpa [step, hmb] using h
  | some mb => cases hw : s.mailboxWaiters a with
    | nil =>
      -- Handle timed waiter case first
      by_cases htw : s.timedMailboxWaiters a = []
      · -- nil-nil case: no waiters
        have hstep : (step s (.inject a m)).1 =
            { s with
              mailboxes := upd s.mailboxes a (some (mb.enqueue ⟨s.nextMsgId, none, m⟩))
              nextMsgId := s.nextMsgId + 1 } := by
          simp [step, hmb, hw, htw]
        rw [hstep]
        refine ⟨h.readyQ_nodup, fun u hm => h.readyQ_queued u hm, h.running_runs,
          h.timers_nodup, h.timers_sleep, h.fresh_none, h.timers_sorted,
          h.spawned_has_owner, ?_, fun u st hts' hrun => h.runnable_queued u st hts' hrun,
          h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          h.timed_has_deadline, h.deadline_is_timed, h.timed_has_timer, h.timed_is_waiter,
          h.timed_waiters_valid, h.timed_waiters_nodup, h.timed_waiters_exclusive⟩
        · intro u cc hown
          obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
          by_cases hcc : cc = a
          · subst hcc; exact ⟨mb.enqueue ⟨s.nextMsgId, none, m⟩, by simp [upd_self]⟩
          · exact ⟨mbc, by simp [upd, if_neg hcc, hmbc]⟩
        · intro u p hp; exact h.parent_lt u p (by simpa [step, hmb, hw, htw] using hp)
        · intro u p hp
          obtain ⟨st, hst⟩ := h.parent_spawned u p hp
          exact ⟨st, hst⟩
        · intro ac mc env hmbc henv
          change env.occurrence < s.nextMsgId + 1
          by_cases hac : ac = a
          · rw [hac] at hmbc; simp only [upd_self] at hmbc
            have hv := Option.some.inj hmbc; subst hv
            simp only [Mailbox.enqueue, List.mem_append, List.mem_singleton] at henv
            rcases henv with henv | rfl
            · exact Nat.lt_succ_of_lt (h.occ_fresh a mb env hmb henv)
            · exact Nat.lt_succ_self _
          · simp only [upd, if_neg hac] at hmbc
            exact Nat.lt_succ_of_lt (h.occ_fresh ac mc env hmbc henv)
        · intro ac mc hmbc
          by_cases hac : ac = a
          · rw [hac] at hmbc; simp only [upd_self] at hmbc
            have hv := Option.some.inj hmbc; subst hv
            simp only [Mailbox.enqueue, List.map_append, List.map_singleton]
            exact nodup_append_singleton (h.occ_nodup a mb hmb) (nextMsgId_fresh h hmb)
          · simp only [upd, if_neg hac] at hmbc; exact h.occ_nodup ac mc hmbc
        · intro ac bc mba mbb hab hmba hmbb ea hea eb heb
          by_cases hac : ac = a <;> by_cases hbc : bc = a
          · exact absurd (hac.trans hbc.symm) hab
          · rw [hac] at hmba; simp only [upd_self] at hmba
            have hv := Option.some.inj hmba; subst hv
            simp only [upd, if_neg hbc] at hmbb
            simp only [Mailbox.enqueue, List.mem_append, List.mem_singleton] at hea
            rcases hea with hea | rfl
            · exact h.occ_disjoint ac bc mb mbb hab (hac ▸ hmb) hmbb ea hea eb heb
            · intro heq; exact Nat.lt_irrefl _ (heq ▸ h.occ_fresh bc mbb eb hmbb heb)
          · rw [hbc] at hmbb; simp only [upd_self] at hmbb
            have hv := Option.some.inj hmbb; subst hv
            simp only [upd, if_neg hac] at hmba
            simp only [Mailbox.enqueue, List.mem_append, List.mem_singleton] at heb
            rcases heb with heb | rfl
            · exact h.occ_disjoint ac bc mba mb hab hmba (hbc ▸ hmb) ea hea eb heb
            · intro heq; exact Nat.lt_irrefl _ (heq.symm ▸ h.occ_fresh ac mba ea hmba hea)
          · simp [upd, if_neg hac] at hmba; simp [upd, if_neg hbc] at hmbb
            exact h.occ_disjoint ac bc mba mbb hab hmba hmbb ea hea eb heb
        · intro u a' how'; obtain ⟨st, hst⟩ := h.owner_spawned u a' how'
          exact ⟨st, hst⟩
        · intro u p hp; obtain ⟨st, hst⟩ := h.parent_child_spawned u p hp
          exact ⟨st, hst⟩
      · -- nil-timed cons case: timed waiter w gets woken (mirror of send timed cons)
        obtain ⟨w, ws, htw⟩ : ∃ w ws, s.timedMailboxWaiters a = w :: ws := by
          cases h' : s.timedMailboxWaiters a with
          | nil => exact absurd h' htw
          | cons w ws => exact ⟨w, ws, rfl⟩
        have hwtt := h.timed_waiters_valid a w (htw ▸ List.mem_cons_self w ws)
        have hwq : w ∉ s.readyQ := fun hm =>
          absurd (h.readyQ_queued w hm) (by simp [hwtt, Option.any, TaskState.isRunnable])
        have hstep : (step s (.inject a m)).1 =
            { s with
              mailboxes := upd s.mailboxes a (some (mb.enqueue ⟨s.nextMsgId, none, m⟩))
              nextMsgId := s.nextMsgId + 1
              taskState := upd s.taskState w (some .ready)
              readyQ := s.readyQ ++ [w]
              timedMailboxWaiters := fun ac => if ac = a then ws else s.timedMailboxWaiters ac
              timers := s.timers.filter (fun e => e.task ≠ w)
              waitDeadline := fun u => if u = w then none else s.waitDeadline u } := by
          simp [step, hmb, hw, htw]
        rw [hstep]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- readyQ_nodup
          exact nodup_append_singleton h.readyQ_nodup hwq
        · -- readyQ_queued
          intro u hm; rcases List.mem_append.mp hm with hm | hm
          · by_cases hue : u = w
            · simp [hue, upd_self, Option.any, TaskState.isRunnable]
            · simp [upd_ne _ _ hue]; exact h.readyQ_queued u hm
          · simp [List.mem_singleton.mp hm, upd_self, Option.any, TaskState.isRunnable]
        · -- running_runs
          intro u hru; by_cases hue : u = w
          · have := h.running_runs u hru; rw [hue] at this
            exact absurd hwtt (this ▸ by simp)
          · simp [upd_ne _ _ hue]; exact h.running_runs u hru
        · -- timers_nodup
          exact nodup_of_sublist (List.Sublist.map TimerEntry.task (List.filter_sublist _)) h.timers_nodup
        · -- timers_sleep
          intro e he; simp only [List.mem_filter, decide_not] at he
          obtain ⟨hmem, hne⟩ := he
          have hne' : e.task ≠ w := by simpa using hne
          simp [upd_ne _ _ hne']; exact h.timers_sleep e hmem
        · -- fresh_none
          intro u hu; have huw : u ≠ w := fun he => by
            have := h.fresh_none u hu; rw [he] at this; rw [this] at hwtt; simp at hwtt
          simp [upd_ne _ _ huw]; exact h.fresh_none u hu
        · -- timers_sorted
          exact h.timers_sorted.sublist (List.filter_sublist _)
        · -- spawned_has_owner
          intro u st hts'; by_cases hue : u = w
          · simp [hue, upd_self] at hts'; exact h.spawned_has_owner u .waitingTimed (hue ▸ hwtt)
          · simp [upd_ne _ _ hue] at hts'; exact h.spawned_has_owner u st hts'
        · -- owned_has_mailbox
          intro u cc hown; obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
          by_cases hcc : cc = a
          · exact ⟨mb.enqueue ⟨s.nextMsgId, none, m⟩, by rw [hcc]; simp [upd_self]⟩
          · exact ⟨mbc, by simp [upd, if_neg hcc, hmbc]⟩
        · -- runnable_queued
          intro u st hts' hrun; by_cases hue : u = w
          · exact hue ▸ List.mem_append_right _ (List.mem_singleton.mpr rfl)
          · simp only [upd_ne _ _ hue] at hts'
            exact List.mem_append_left _ (h.runnable_queued u st hts' hrun)
        · -- waiters_waiting
          intro a' u hm; have huw : u ≠ w := fun he => by
            rw [he] at hm; exact absurd (h.waiters_waiting a' w hm) (by rw [hwtt]; simp)
          simp [upd_ne _ _ huw]; exact h.waiters_waiting a' u hm
        · -- waiters_owned
          intro a' u hm; exact h.waiters_owned a' u hm
        · -- waiting_queued
          intro u hts'; have huw : u ≠ w := fun he => by simp [he, upd_self] at hts'
          simp [upd_ne _ _ huw] at hts'; exact h.waiting_queued u hts'
        · -- waiters_nodup
          intro a'; exact h.waiters_nodup a'
        · -- parent_lt
          intro u p hp; exact h.parent_lt u p hp
        · -- parent_spawned
          intro u p hp; obtain ⟨st, hst⟩ := h.parent_spawned u p hp
          by_cases hpt : p = w
          · exact ⟨.ready, by simp [hpt, upd_self]⟩
          · exact ⟨st, by simp [upd_ne _ _ hpt]; exact hst⟩
        · -- occ_fresh
          intro ac mc env hmbc henv
          change env.occurrence < s.nextMsgId + 1
          by_cases hac : ac = a
          · rw [hac] at hmbc; simp only [upd_self] at hmbc
            have hv := Option.some.inj hmbc; subst hv
            simp only [Mailbox.enqueue, List.mem_append, List.mem_singleton] at henv
            rcases henv with henv | rfl
            · exact Nat.lt_succ_of_lt (h.occ_fresh a mb env hmb henv)
            · exact Nat.lt_succ_self _
          · simp only [upd, if_neg hac] at hmbc
            exact Nat.lt_succ_of_lt (h.occ_fresh ac mc env hmbc henv)
        · -- occ_nodup
          intro ac mc hmbc
          by_cases hac : ac = a
          · rw [hac] at hmbc; simp only [upd_self] at hmbc
            have hv := Option.some.inj hmbc; subst hv
            simp only [Mailbox.enqueue, List.map_append, List.map_singleton]
            exact nodup_append_singleton (h.occ_nodup a mb hmb) (nextMsgId_fresh h hmb)
          · simp only [upd, if_neg hac] at hmbc; exact h.occ_nodup ac mc hmbc
        · -- occ_disjoint
          intro ac bc mba mbb hab hmba hmbb ea hea eb heb
          by_cases hac : ac = a <;> by_cases hbc : bc = a
          · exact absurd (hac.trans hbc.symm) hab
          · rw [hac] at hmba; simp only [upd_self] at hmba
            have hv := Option.some.inj hmba; subst hv
            simp only [upd, if_neg hbc] at hmbb
            simp only [Mailbox.enqueue, List.mem_append, List.mem_singleton] at hea
            rcases hea with hea | rfl
            · exact h.occ_disjoint ac bc mb mbb hab (hac ▸ hmb) hmbb ea hea eb heb
            · intro heq; exact Nat.lt_irrefl _ (heq ▸ h.occ_fresh bc mbb eb hmbb heb)
          · rw [hbc] at hmbb; simp only [upd_self] at hmbb
            have hv := Option.some.inj hmbb; subst hv
            simp only [upd, if_neg hac] at hmba
            simp only [Mailbox.enqueue, List.mem_append, List.mem_singleton] at heb
            rcases heb with heb | rfl
            · exact h.occ_disjoint ac bc mba mb hab hmba (hbc ▸ hmb) ea hea eb heb
            · intro heq; exact Nat.lt_irrefl _ (heq.symm ▸ h.occ_fresh ac mba ea hmba hea)
          · simp only [upd, if_neg hac] at hmba; simp only [upd, if_neg hbc] at hmbb
            exact h.occ_disjoint ac bc mba mbb hab hmba hmbb ea hea eb heb
        · -- owner_spawned
          intro u a' how'; obtain ⟨st, hst⟩ := h.owner_spawned u a' how'
          by_cases hue : u = w
          · exact ⟨.ready, by simp [hue, upd_self]⟩
          · exact ⟨st, by simp [upd_ne _ _ hue]; exact hst⟩
        · -- parent_child_spawned
          intro u p hp; obtain ⟨st, hst⟩ := h.parent_child_spawned u p hp
          by_cases hue : u = w
          · exact ⟨.ready, by simp [hue, upd_self]⟩
          · exact ⟨st, by simp [upd_ne _ _ hue]; exact hst⟩
        · -- timed_has_deadline
          intro u hu; by_cases hue : u = w
          · simp [hue, upd_self] at hu
          · simp [upd_ne _ _ hue] at hu; obtain ⟨d, hd⟩ := h.timed_has_deadline u hu
            exact ⟨d, by simp [if_neg hue, hd]⟩
        · -- deadline_is_timed
          intro u dv hd; have huw : u ≠ w := fun he => by simp [he] at hd
          simp [if_neg huw] at hd; simp [upd_ne _ _ huw]; exact h.deadline_is_timed u dv hd
        · -- timed_has_timer
          intro u hu; by_cases hue : u = w
          · simp [hue, upd_self] at hu
          · simp [upd_ne _ _ hue] at hu; obtain ⟨e, he, hek⟩ := h.timed_has_timer u hu
            have hewne : e.task ≠ w := fun heq => hue (hek ▸ heq)
            exact ⟨e, by simp [List.mem_filter, he, hewne], hek⟩
        · -- timed_is_waiter
          intro u hu; by_cases hue : u = w
          · simp [hue, upd_self] at hu
          · simp [upd_ne _ _ hue] at hu; obtain ⟨ac, hac⟩ := h.timed_is_waiter u hu
            by_cases hac_eq : ac = a
            · refine ⟨a, ?_⟩
              have hu_ws : u ∈ ws := (List.mem_cons.mp (htw ▸ hac_eq ▸ hac)).resolve_left hue
              simp [hu_ws]
            · exact ⟨ac, by simp [if_neg hac_eq]; exact hac⟩
        · -- timed_waiters_valid
          intro a' u hm; by_cases hab : a' = a
          · have hmw : u ∈ ws := by simpa [hab] using hm
            have huw : u ≠ w := fun he =>
              absurd (he ▸ hmw) (List.nodup_cons.mp (htw ▸ h.timed_waiters_nodup a)).1
            simp [upd_ne _ _ huw]; exact h.timed_waiters_valid a u (htw ▸ List.mem_cons_of_mem w hmw)
          · have hmw : u ∈ s.timedMailboxWaiters a' := by simpa [if_neg hab] using hm
            have hw_in_a : w ∈ s.timedMailboxWaiters a := htw ▸ List.mem_cons_self w ws
            have huw : u ≠ w := fun he => h.timed_waiters_exclusive a' a u hab hmw (he ▸ hw_in_a)
            simp [upd_ne _ _ huw]; exact h.timed_waiters_valid a' u hmw
        · -- timed_waiters_nodup
          intro a'; by_cases hab : a' = a
          · simpa [hab] using (List.nodup_cons.mp (htw ▸ h.timed_waiters_nodup a)).2
          · simpa [if_neg hab] using h.timed_waiters_nodup a'
        · -- timed_waiters_exclusive
          intro a' b' u hab' hma hmb'
          by_cases ha : a' = a <;> by_cases hb : b' = a
          · exact absurd (ha.trans hb.symm) hab'
          · have hu_ws : u ∈ ws := by simpa [ha] using hma
            have hms_b' : u ∈ s.timedMailboxWaiters b' := by simpa [if_neg hb] using hmb'
            exact h.timed_waiters_exclusive a b' u (fun h' => hb h'.symm)
              (htw ▸ List.mem_cons_of_mem w hu_ws) hms_b'
          · have hms_a' : u ∈ s.timedMailboxWaiters a' := by simpa [if_neg ha] using hma
            have hu_ws : u ∈ ws := by simpa [hb] using hmb'
            exact h.timed_waiters_exclusive a' a u ha hms_a' (htw ▸ List.mem_cons_of_mem w hu_ws)
          · have hms_a' : u ∈ s.timedMailboxWaiters a' := by simpa [if_neg ha] using hma
            have hms_b' : u ∈ s.timedMailboxWaiters b' := by simpa [if_neg hb] using hmb'
            exact h.timed_waiters_exclusive a' b' u hab' hms_a' hms_b'
    | cons w ws =>
      have hwt  : s.taskState w = some .waiting := h.waiters_waiting a w (hw ▸ List.mem_cons_self w ws)
      have hwq  : w ∉ s.readyQ := waiting_not_in_readyQ h hwt
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [step, hmb, hw]; exact nodup_append_singleton h.readyQ_nodup hwq
      · intro u hm; simp [step, hmb, hw] at hm ⊢
        rcases hm with hm | rfl
        · by_cases hue : u = w
          · simp [upd_self, hue, Option.any, TaskState.isRunnable]
          · simp [upd_ne _ _ hue]; exact h.readyQ_queued u hm
        · simp [upd_self, Option.any, TaskState.isRunnable]
      · intro u hru; simp [step, hmb, hw] at hru ⊢
        by_cases hue : u = w
        · exact absurd hwt (by simp [← hue, h.running_runs u hru])
        · simp [upd_ne _ _ hue]; exact h.running_runs u hru
      · simp [step, hmb, hw]
        exact nodup_of_sublist (List.Sublist.map TimerEntry.task (List.filter_sublist _)) h.timers_nodup
      · intro e he; simp [step, hmb, hw] at he ⊢
        have hts_e := h.timers_sleep e he.1
        have hne' : e.task ≠ w := by simpa using he.2
        simp [upd_ne _ _ hne']; exact hts_e
      · intro u hu; simp [step, hmb, hw] at hu ⊢
        by_cases hue : u = w
        · exact absurd hwt (by simp [← hue, h.fresh_none u hu])
        · simp [upd_ne _ _ hue]; exact h.fresh_none u hu
      · simp [step, hmb, hw]; exact h.timers_sorted.sublist (List.filter_sublist _)
      · intro u st hts'; simp [step, hmb, hw] at hts' ⊢
        by_cases hue : u = w
        · simp [upd_self, hue] at hts' ⊢; exact h.spawned_has_owner w .waiting hwt
        · simp [upd_ne _ _ hue] at hts' ⊢; exact h.spawned_has_owner u st hts'
      · intro u cc hown; simp only [inject_taskOwner] at hown
        obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
        exact inject_mailbox_isSome hmbc m
      · intro u st hts' hrun; simp [step, hmb, hw] at hts' ⊢
        by_cases hue : u = w
        · simp [hue, upd_self] at hts'; exact Or.inr hue
        · simp [upd_ne _ _ hue] at hts'; exact Or.inl (h.runnable_queued u st hts' hrun)
      · intro a' u hm; simp [step, hmb, hw] at hm ⊢
        by_cases hab : a' = a
        · simp only [if_pos hab] at hm
          have hmem : u ∈ s.mailboxWaiters a := hw ▸ List.mem_cons_of_mem w hm
          have hue : u ≠ w := fun he => (List.nodup_cons.mp (hw ▸ h.waiters_nodup a)).1 (he ▸ hm)
          simp [upd_ne _ _ hue, hab]; exact h.waiters_waiting a u hmem
        · simp only [if_neg hab] at hm
          have hts_u := h.waiters_waiting a' u hm
          have hue : u ≠ w := fun he => by
            have ho1 : s.taskOwner w = some a' := he ▸ h.waiters_owned a' u hm
            have ho2 : s.taskOwner w = some a  := h.waiters_owned a w (hw ▸ List.mem_cons_self w ws)
            exact hab (Option.some.inj (ho1.symm.trans ho2))
          simp [upd_ne _ _ hue, hab]; exact hts_u
      · intro a' u hm; simp [step, hmb, hw] at hm ⊢
        by_cases hab : a' = a
        · simp only [if_pos hab] at hm
          exact hab ▸ h.waiters_owned a u (hw ▸ List.mem_cons_of_mem w hm)
        · simp only [if_neg hab] at hm ⊢; exact h.waiters_owned a' u hm
      · intro u hts'; simp [step, hmb, hw] at hts' ⊢
        by_cases hue : u = w
        · simp [hue, upd_self] at hts'
        · simp [upd_ne _ _ hue] at hts'
          obtain ⟨a', ha', hmem⟩ := h.waiting_queued u hts'
          refine ⟨a', ha', ?_⟩
          by_cases hab : a' = a
          · simp only [if_pos hab]; exact waiter_in_tail h hw (by rwa [hab] at hmem) hue
          · simp only [if_neg hab]; exact hmem
      · intro a'; simp [step, hmb, hw]
        by_cases hab : a' = a
        · simp only [if_pos hab]; exact (List.nodup_cons.mp (hw ▸ h.waiters_nodup a)).2
        · simp only [if_neg hab]; exact h.waiters_nodup a'
      · -- parent_lt
        exact fun u p hp => h.parent_lt u p (by simpa [step, hmb, hw] using hp)
      · -- parent_spawned (RFC 042)
        intro u p hp
        obtain ⟨st, hst⟩ := h.parent_spawned u p (by simpa [step, hmb, hw] using hp)
        exact step_preserves_spawned hst _
      · -- occ_fresh (RFC 033): inject cons
        intro ac mc env hmbc henv
        have hmi : ((step s (.inject a m)).1).nextMsgId = s.nextMsgId + 1 := by
          simp [step, hmb, hw]
        rw [hmi]
        by_cases hac : ac = a
        · rw [hac] at hmbc; rw [inject_appends hmb m] at hmbc
          have hv := Option.some.inj hmbc; subst hv
          simp only [List.mem_append, List.mem_singleton] at henv
          rcases henv with henv | rfl
          · exact Nat.lt_succ_of_lt (h.occ_fresh a mb env hmb henv)
          · exact Nat.lt_succ_self _
        · rw [inject_preserves_other hac m] at hmbc
          exact Nat.lt_succ_of_lt (h.occ_fresh ac mc env hmbc henv)
      · -- occ_nodup (RFC 033): inject cons
        intro ac mc hmbc
        by_cases hac : ac = a
        · rw [hac] at hmbc; rw [inject_appends hmb m] at hmbc
          have hv := Option.some.inj hmbc; subst hv
          simp only [List.map_append, List.map_singleton]
          exact nodup_append_singleton (h.occ_nodup a mb hmb) (nextMsgId_fresh h hmb)
        · rw [inject_preserves_other hac m] at hmbc
          exact h.occ_nodup ac mc hmbc
      · -- occ_disjoint (RFC 033): inject cons
        intro ac bc mba mbb hab hmba hmbb ea hea eb heb
        by_cases hac : ac = a <;> by_cases hbc : bc = a
        · exact absurd (hac.trans hbc.symm) hab
        · rw [hac] at hmba; rw [inject_appends hmb m] at hmba
          have hv := Option.some.inj hmba; subst hv
          rw [inject_preserves_other hbc m] at hmbb
          simp only [List.mem_append, List.mem_singleton] at hea
          rcases hea with hea | rfl
          · exact h.occ_disjoint ac bc mb mbb hab (hac ▸ hmb) hmbb ea hea eb heb
          · intro heq; exact Nat.lt_irrefl _ (heq ▸ h.occ_fresh bc mbb eb hmbb heb)
        · rw [hbc] at hmbb; rw [inject_appends hmb m] at hmbb
          have hv := Option.some.inj hmbb; subst hv
          rw [inject_preserves_other hac m] at hmba
          simp only [List.mem_append, List.mem_singleton] at heb
          rcases heb with heb | rfl
          · exact h.occ_disjoint ac bc mba mb hab hmba (hbc ▸ hmb) ea hea eb heb
          · intro heq; exact Nat.lt_irrefl _ (heq.symm ▸ h.occ_fresh ac mba ea hmba hea)
        · rw [inject_preserves_other hac m] at hmba
          rw [inject_preserves_other hbc m] at hmbb
          exact h.occ_disjoint ac bc mba mbb hab hmba hmbb ea hea eb heb
      · -- owner_spawned (RFC 038): taskOwner unchanged; taskState changes at w
        intro u a' how'
        obtain ⟨st, hst⟩ := h.owner_spawned u a' (by simpa [step, hmb, hw] using how')
        exact step_preserves_spawned hst (.inject a m)
      · -- parent_child_spawned (RFC 038): taskParent unchanged; taskState changes at w
        intro u p hp
        obtain ⟨st, hst⟩ := h.parent_child_spawned u p (by simpa [step, hmb, hw] using hp)
        exact step_preserves_spawned hst (.inject a m)
      · -- timed_has_deadline (RFC 040): w was .waiting (no deadline), others unchanged
        intro u hu; simp [step, hmb, hw] at hu
        have huw : u ≠ w := by intro he; simp [he, upd_self] at hu
        have hu' : s.taskState u = some .waitingTimed := by simpa [upd_ne _ _ huw] using hu
        obtain ⟨dl, hdl⟩ := h.timed_has_deadline u hu'
        exact ⟨dl, by simpa [step, hmb, hw, huw] using hdl⟩
      · -- deadline_is_timed (RFC 040)
        intro u dv hd; simp [step, hmb, hw] at hd
        have huw : u ≠ w := by intro he; simp [he] at hd
        have hd' : s.waitDeadline u = some dv := by simpa [huw] using hd
        simpa [step, hmb, hw, upd_ne _ _ huw] using h.deadline_is_timed u dv hd'
      · -- timed_has_timer (RFC 040): w's timer filtered
        intro u hu; simp [step, hmb, hw] at hu
        have huw : u ≠ w := by intro he; simp [he, upd_self] at hu
        have hu' : s.taskState u = some .waitingTimed := by simpa [upd_ne _ _ huw] using hu
        obtain ⟨e, he, hek⟩ := h.timed_has_timer u hu'
        have hewne : e.task ≠ w := fun heq => huw (hek ▸ heq)
        exact ⟨e, by simp [step, hmb, hw, he, hewne], hek⟩
      · -- timed_is_waiter (RFC 040): timedMailboxWaiters unchanged
        intro u hu; simp [step, hmb, hw] at hu
        have huw : u ≠ w := by intro he; simp [he, upd_self] at hu
        have hu' : s.taskState u = some .waitingTimed := by simpa [upd_ne _ _ huw] using hu
        obtain ⟨ac, hac⟩ := h.timed_is_waiter u hu'
        exact ⟨ac, by simpa [step, hmb, hw] using hac⟩
      · -- timed_waiters_valid (RFC 040): timedMailboxWaiters unchanged
        intro a' u hm
        have hm' : u ∈ s.timedMailboxWaiters a' := by simpa [step, hmb, hw] using hm
        have huw : u ≠ w := fun he => absurd (h.timed_waiters_valid a' w (he ▸ hm')) (by rw [hwt]; simp)
        simpa [step, hmb, hw, upd_ne _ _ huw] using h.timed_waiters_valid a' u hm'
      · -- timed_waiters_nodup (RFC 040): timedMailboxWaiters unchanged
        intro a'; simpa [step, hmb, hw] using h.timed_waiters_nodup a'
      · -- timed_waiters_exclusive (RFC 040): timedMailboxWaiters unchanged
        intro a' b' u hab' hma hmb'
        exact h.timed_waiters_exclusive a' b' u hab'
          (by simpa [step, hmb, hw] using hma) (by simpa [step, hmb, hw] using hmb')

-- ─── receiveUntil: WellFormed preservation (RFC 040) ──────────────────────

theorem preserves_wf_receiveUntil {s : RuntimeState} (h : WellFormed s)
    {t : TaskId} {deadline : Nat} :
    WellFormed ((step s (.receiveUntil t deadline)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some st => cases st with
      | running => cases how : s.taskOwner t with
        | none => simpa [step, hrt, hts, how] using h
        | some a => cases hmb : s.mailboxes a with
          | none => simpa [step, hrt, hts, how, hmb] using h
          | some mb => cases hd : mb.dequeue with
            | some p =>
              -- Message available: only mailboxes changes (dequeue)
              obtain ⟨env, rest⟩ := p
              have hstep : (step s (.receiveUntil t deadline)).1 =
                  { s with mailboxes := upd s.mailboxes a (some rest) } := by
                simp [step, hrt, hts, how, hmb, hd]
              have hcons : mb.messages = env :: rest.messages := by
                have := Mailbox.dequeue_spec mb; rw [hd] at this; exact this
              rw [hstep]
              refine ⟨h.readyQ_nodup, fun u hm => h.readyQ_queued u hm, h.running_runs,
                h.timers_nodup, h.timers_sleep, h.fresh_none, h.timers_sorted,
                h.spawned_has_owner, ?_, fun u st hts' hrun => h.runnable_queued u st hts' hrun,
                h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                h.timed_has_deadline, h.deadline_is_timed, h.timed_has_timer, h.timed_is_waiter,
                h.timed_waiters_valid, h.timed_waiters_nodup, h.timed_waiters_exclusive⟩
              · intro u cc hown
                obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
                by_cases hcc : cc = a
                · subst hcc; exact ⟨rest, by simp [upd_self]⟩
                · exact ⟨mbc, by simp [upd, if_neg hcc, hmbc]⟩
              · intro u p hp; exact h.parent_lt u p hp
              · intro u p hp; obtain ⟨st, hst⟩ := h.parent_spawned u p hp; exact ⟨st, hst⟩
              · -- occ_fresh: mailbox a shrinks (dequeue)
                intro ac mc env' hmbc henv
                by_cases hac : ac = a
                · rw [hac] at hmbc; simp only [upd_self] at hmbc
                  have hv := Option.some.inj hmbc; subst hv
                  have : env' ∈ mb.messages := hcons ▸ List.mem_cons_of_mem env henv
                  exact h.occ_fresh a mb env' hmb this
                · simp only [upd, if_neg hac] at hmbc; exact h.occ_fresh ac mc env' hmbc henv
              · -- occ_nodup
                intro ac mc hmbc
                by_cases hac : ac = a
                · rw [hac] at hmbc; simp only [upd_self] at hmbc
                  have hv := Option.some.inj hmbc; subst hv
                  have hsub := h.occ_nodup a mb hmb
                  rw [hcons, List.map_cons] at hsub; exact (List.nodup_cons.mp hsub).2
                · simp only [upd, if_neg hac] at hmbc; exact h.occ_nodup ac mc hmbc
              · -- occ_disjoint
                intro ac bc mba mbb hab hmba hmbb ea hea eb heb
                by_cases hac : ac = a <;> by_cases hbc : bc = a
                · exact absurd (hac.trans hbc.symm) hab
                · subst hac; simp only [upd_self] at hmba
                  have hv := Option.some.inj hmba; subst hv
                  simp only [upd, if_neg hbc] at hmbb
                  have heaa : ea ∈ mb.messages := hcons ▸ List.mem_cons_of_mem env hea
                  exact h.occ_disjoint ac bc mb mbb hab hmb hmbb ea heaa eb heb
                · subst hbc; simp only [upd_self] at hmbb
                  have hv := Option.some.inj hmbb; subst hv
                  simp only [upd, if_neg hac] at hmba
                  have hebb : eb ∈ mb.messages := hcons ▸ List.mem_cons_of_mem env heb
                  exact h.occ_disjoint ac bc mba mb hab hmba hmb ea hea eb hebb
                · simp only [upd, if_neg hac] at hmba; simp only [upd, if_neg hbc] at hmbb
                  exact h.occ_disjoint ac bc mba mbb hab hmba hmbb ea hea eb heb
              · intro u a' how'; obtain ⟨st, hst⟩ := h.owner_spawned u a' how'; exact ⟨st, hst⟩
              · intro u p hp; obtain ⟨st, hst⟩ := h.parent_child_spawned u p hp; exact ⟨st, hst⟩
            | none =>
              by_cases hdl : deadline ≤ s.now
              · -- Past-deadline fast path: no state change
                simpa [step, hrt, hts, how, hmb, hd, hdl] using h
              · -- Park with deadline: t → waitingTimed, added to timedMailboxWaiters a, timer + waitDeadline
                have hmb_empty : mb.messages = [] := by
                  have := Mailbox.dequeue_spec mb; rw [hd] at this; exact this
                have ht_not_twaiter : t ∉ s.timedMailboxWaiters a := fun hmem =>
                  absurd (h.timed_waiters_valid a t hmem) (by simp [hts])
                have hnotin_timers : t ∉ s.timers.map TimerEntry.task := by
                  intro hm; rw [List.mem_map] at hm
                  obtain ⟨e, he, hee⟩ := hm
                  have h1 := h.timers_sleep e he; rw [hee, hts] at h1
                  rcases h1 with h1 | h1 <;> simp at h1
                have hstep : (step s (.receiveUntil t deadline)).1 =
                    { s with
                        taskState := upd s.taskState t (some .waitingTimed)
                        running := none
                        timedMailboxWaiters := fun ac =>
                          if ac = a then s.timedMailboxWaiters a ++ [t]
                          else s.timedMailboxWaiters ac
                        timers := Timer.insertSorted ⟨deadline, t⟩ s.timers
                        waitDeadline := upd s.waitDeadline t (some deadline) } := by
                  simp [step, hrt, hts, how, hmb, hd, hdl]
                rw [hstep]
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · -- readyQ_nodup
                  exact h.readyQ_nodup
                · -- readyQ_queued
                  intro u hm
                  have h1 := h.readyQ_queued u hm
                  have hu : u ≠ t := fun he => by
                    rw [he, hts] at h1; simp [Option.any, TaskState.isRunnable] at h1
                  simp only [upd, if_neg hu]; exact h1
                · -- running_runs
                  intro u hru; simp at hru
                · -- timers_nodup
                  exact insertSorted_task_nodup hnotin_timers h.timers_nodup
                · -- timers_sleep
                  intro e he
                  rcases Timer.mem_insertSorted.mp he with rfl | he
                  · simp [upd_self]
                  · have h1 := h.timers_sleep e he
                    have hu : e.task ≠ t := fun heq => by
                      rw [heq, hts] at h1; rcases h1 with h1 | h1 <;> simp at h1
                    simp only [upd, if_neg hu]; exact h1
                · -- fresh_none
                  intro u hu
                  have h1 : u ≠ t := fun he => by
                    rw [← he] at hts; rw [h.fresh_none u hu] at hts; cases hts
                  simp only [upd, if_neg h1]; exact h.fresh_none u hu
                · -- timers_sorted
                  exact Timer.insertSorted_sorted h.timers_sorted
                · -- spawned_has_owner
                  intro u st hts'
                  by_cases hu : u = t
                  · subst hu; exact h.spawned_has_owner u .running hts
                  · simp only [upd, if_neg hu] at hts'; exact h.spawned_has_owner u st hts'
                · -- owned_has_mailbox
                  intro u b hown; exact h.owned_has_mailbox u b hown
                · -- runnable_queued
                  intro u st hts' hrun
                  by_cases hu : u = t
                  · subst hu; simp only [upd_self] at hts'; cases hts'
                    simp [TaskState.isRunnable] at hrun
                  · simp only [upd, if_neg hu] at hts'; exact h.runnable_queued u st hts' hrun
                · -- waiters_waiting: mailboxWaiters unchanged
                  intro a' u hm
                  have h1 := h.waiters_waiting a' u hm
                  have hu : u ≠ t := fun he => by rw [← he] at hts; rw [h1] at hts; cases hts
                  simp only [upd, if_neg hu]; exact h1
                · -- waiters_owned
                  intro a' u hm; exact h.waiters_owned a' u hm
                · -- waiting_queued: t goes to waitingTimed not waiting
                  intro u hts'
                  by_cases hu : u = t
                  · simp only [hu, upd_self] at hts'; cases hts'
                  · simp only [upd, if_neg hu] at hts'; exact h.waiting_queued u hts'
                · -- waiters_nodup
                  intro a'; exact h.waiters_nodup a'
                · -- parent_lt
                  intro u p hp; exact h.parent_lt u p hp
                · -- parent_spawned
                  intro u p hp
                  obtain ⟨st, hst⟩ := h.parent_spawned u p hp
                  by_cases hpt : p = t
                  · exact ⟨.waitingTimed, by simp [hpt, upd_self]⟩
                  · exact ⟨st, by simp only [upd, if_neg hpt]; exact hst⟩
                · -- occ_fresh: mailboxes unchanged
                  intro a' mb' env hmb' henv; exact h.occ_fresh a' mb' env hmb' henv
                · -- occ_nodup
                  intro a' mb' hmb'; exact h.occ_nodup a' mb' hmb'
                · -- occ_disjoint
                  intro a' b' mba mbb hab hmba hmbb ea hea eb heb
                  exact h.occ_disjoint a' b' mba mbb hab hmba hmbb ea hea eb heb
                · -- owner_spawned
                  intro u a' how'
                  obtain ⟨st, hst⟩ := h.owner_spawned u a' how'
                  by_cases hu : u = t
                  · subst hu; exact ⟨.waitingTimed, by simp [upd_self]⟩
                  · exact ⟨st, by simp only [upd, if_neg hu]; exact hst⟩
                · -- parent_child_spawned
                  intro u p hp
                  obtain ⟨st, hst⟩ := h.parent_child_spawned u p hp
                  by_cases hu : u = t
                  · subst hu; exact ⟨.waitingTimed, by simp [upd_self]⟩
                  · exact ⟨st, by simp only [upd, if_neg hu]; exact hst⟩
                · -- timed_has_deadline: t gets deadline; others preserved
                  intro u hu
                  by_cases hut : u = t
                  · exact ⟨deadline, by simp [hut, upd_self]⟩
                  · simp only [upd, if_neg hut] at hu
                    obtain ⟨dv, hdv⟩ := h.timed_has_deadline u hu
                    exact ⟨dv, by simp only [upd, if_neg hut]; exact hdv⟩
                · -- deadline_is_timed: t → waitingTimed with deadline
                  intro u dv hd'
                  by_cases hut : u = t
                  · simp [hut, upd_self]
                  · simp only [upd, if_neg hut] at hd'
                    have := h.deadline_is_timed u dv hd'
                    simp only [upd, if_neg hut]; exact this
                · -- timed_has_timer: t gets a timer; others keep theirs
                  intro u hu
                  by_cases hut : u = t
                  · exact ⟨⟨deadline, t⟩, by rw [Timer.mem_insertSorted]; exact Or.inl rfl, by simp [hut]⟩
                  · simp only [upd, if_neg hut] at hu
                    obtain ⟨e, he, hek⟩ := h.timed_has_timer u hu
                    exact ⟨e, by rw [Timer.mem_insertSorted]; exact Or.inr he, hek⟩
                · -- timed_is_waiter: t added to timedMailboxWaiters a
                  intro u hu
                  by_cases hut : u = t
                  · exact ⟨a, by simp [hut]⟩
                  · simp only [upd, if_neg hut] at hu
                    obtain ⟨a', ha'⟩ := h.timed_is_waiter u hu
                    by_cases haa : a' = a
                    · exact ⟨a, by simp [if_pos haa]; left; rw [← haa]; exact ha'⟩
                    · exact ⟨a', by simp [if_neg haa]; exact ha'⟩
                · -- timed_waiters_valid
                  intro a' u hm
                  by_cases haa : a' = a
                  · simp only [if_pos haa, List.mem_append, List.mem_singleton] at hm
                    rcases hm with hm | rfl
                    · have hu : u ≠ t := fun he => ht_not_twaiter (he ▸ hm)
                      simp only [upd, if_neg hu]; exact h.timed_waiters_valid a u hm
                    · simp [upd_self]
                  · simp only [if_neg haa] at hm
                    -- u ∈ timedMailboxWaiters a' (a' ≠ a); u = t impossible since t is running
                    have hu : u ≠ t := fun he => by
                      have := h.timed_waiters_valid a' t (he ▸ hm)
                      rw [hts] at this; cases this
                    simp only [upd, if_neg hu]; exact h.timed_waiters_valid a' u hm
                · -- timed_waiters_nodup: t appended to a's list (was nodup, t ∉ list)
                  intro a'
                  by_cases haa : a' = a
                  · simp only [if_pos haa]
                    exact nodup_append_singleton (h.timed_waiters_nodup a) (haa ▸ ht_not_twaiter)
                  · simp only [if_neg haa]; exact h.timed_waiters_nodup a'
                · -- timed_waiters_exclusive: t added only to a's list
                  intro a' b' u hab' hma hmb'
                  by_cases ha' : a' = a <;> by_cases hb' : b' = a
                  · exact absurd (ha'.trans hb'.symm) hab'
                  · -- a' = a (u ∈ as ++ [t]), b' ≠ a (u ∈ s.tmw b')
                    simp only [if_pos ha', List.mem_append, List.mem_singleton] at hma
                    simp only [if_neg hb'] at hmb'
                    rcases hma with hma | rfl
                    · exact h.timed_waiters_exclusive a b' u (ha' ▸ hab') hma hmb'
                    · have := h.timed_waiters_valid b' u hmb'; rw [hts] at this; cases this
                  · -- a' ≠ a, b' = a (u ∈ as ++ [t])
                    simp only [if_neg ha'] at hma
                    simp only [if_pos hb', List.mem_append, List.mem_singleton] at hmb'
                    rcases hmb' with hmb' | rfl
                    · exact h.timed_waiters_exclusive a' a u (hb' ▸ hab') hma hmb'
                    · have := h.timed_waiters_valid a' u hma; rw [hts] at this; cases this
                  · simp only [if_neg ha'] at hma; simp only [if_neg hb'] at hmb'
                    exact h.timed_waiters_exclusive a' b' u hab' hma hmb'
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed =>
        simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h

-- ─── selective receive: WellFormed preservation (RFC 041) ─────────────────

theorem preserves_wf_receiveByOccurrence {s : RuntimeState} (h : WellFormed s)
    {t : TaskId} {occ : MessageId} :
    WellFormed ((step s (.receiveByOccurrence t occ)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some st => cases st with
      | running => cases how : s.taskOwner t with
        | none => simpa [step, hrt, hts, how] using h
        | some a => cases hmb : s.mailboxes a with
          | none => simpa [step, hrt, hts, how, hmb] using h
          | some mb => cases hd : mb.dequeueFirst (·.occurrence = occ) with
            | some p =>
              obtain ⟨env, rest⟩ := p
              -- receive dequeues head envelope; nextMsgId unchanged
              have hstep_d : (step s (.receiveByOccurrence t occ)).1 =
                  { s with mailboxes := upd s.mailboxes a (some rest) } := by
                simp [step, hrt, hts, how, hmb, hd]
              -- Extract head/tail relationship
              -- selective dequeue: rest is a sublist of mb, so every rest envelope was in mb
              have hsubmem : ∀ {x : Envelope}, x ∈ rest.messages → x ∈ mb.messages :=
                fun {x} hx => (Mailbox.dequeueFirst_sublist _ mb hd).mem hx
              have hsubnodup : (rest.messages.map Envelope.occurrence).Nodup → True := fun _ => trivial
              rw [hstep_d]
              refine ⟨h.readyQ_nodup, fun u hm => h.readyQ_queued u hm, h.running_runs,
                h.timers_nodup, h.timers_sleep, h.fresh_none, h.timers_sorted,
                h.spawned_has_owner, ?_, fun u st hts' hrun => h.runnable_queued u st hts' hrun,
                h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                h.timed_has_deadline, h.deadline_is_timed, h.timed_has_timer, h.timed_is_waiter,
                h.timed_waiters_valid, h.timed_waiters_nodup, h.timed_waiters_exclusive⟩
              · intro u cc hown
                obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
                by_cases hcc : cc = a
                · exact ⟨rest, by simp [upd, hcc]⟩
                · exact ⟨mbc, by simp [upd, if_neg hcc, hmbc]⟩
              · intro u p hp; exact h.parent_lt u p
                  (by simpa [step, hrt, hts, how, hmb, hd] using hp)
              · intro u p hp
                obtain ⟨st, hst⟩ := h.parent_spawned u p
                  (by simpa [step, hrt, hts, how, hmb, hd] using hp)
                exact ⟨st, by simpa [step, hrt, hts, how, hmb, hd] using hst⟩
              · -- occ_fresh: nextMsgId unchanged, rest ⊆ mb (RFC 033)
                intro ac mc env2 hmbc henv2
                by_cases hac : ac = a
                · rw [hac] at hmbc; simp only [upd_self] at hmbc
                  have hv := Option.some.inj hmbc; subst hv
                  exact h.occ_fresh ac mb env2 (hac ▸ hmb) (hsubmem henv2)
                · simp only [upd, if_neg hac] at hmbc; exact h.occ_fresh ac mc env2 hmbc henv2
              · -- occ_nodup: rest ⊆ mb (RFC 033)
                intro ac mc hmbc
                by_cases hac : ac = a
                · rw [hac] at hmbc; simp only [upd_self] at hmbc
                  have hv := Option.some.inj hmbc; subst hv
                  have hnd := h.occ_nodup ac mb (hac ▸ hmb)
                  exact (List.Sublist.map Envelope.occurrence
                    (Mailbox.dequeueFirst_sublist _ mb hd)).nodup hnd
                · simp only [upd, if_neg hac] at hmbc; exact h.occ_nodup ac mc hmbc
              · -- occ_disjoint: rest ⊆ mb (RFC 033)
                intro ac bc mba mbb hab hmba hmbb ea hea eb heb
                by_cases hac : ac = a <;> by_cases hbc : bc = a
                · exact absurd (hac.trans hbc.symm) hab
                · rw [hac] at hmba; simp only [upd_self] at hmba
                  have hv := Option.some.inj hmba; subst hv
                  simp only [upd, if_neg hbc] at hmbb
                  exact h.occ_disjoint ac bc mb mbb hab (hac ▸ hmb) hmbb
                    ea (hsubmem hea) eb heb
                · rw [hbc] at hmbb; simp only [upd_self] at hmbb
                  have hv := Option.some.inj hmbb; subst hv
                  simp only [upd, if_neg hac] at hmba
                  exact h.occ_disjoint ac bc mba mb hab hmba (hbc ▸ hmb)
                    ea hea eb (hsubmem heb)
                · simp only [upd, if_neg hac] at hmba; simp only [upd, if_neg hbc] at hmbb
                  exact h.occ_disjoint ac bc mba mbb hab hmba hmbb ea hea eb heb
              · -- owner_spawned (RFC 038): taskOwner unchanged; taskState = s.taskState
                intro u a' how'
                exact h.owner_spawned u a' how'
              · -- parent_child_spawned (RFC 038): taskParent unchanged; taskState = s.taskState
                intro u p hp
                exact h.parent_child_spawned u p hp
            | none =>
              have ht_not_waiter : t ∉ s.mailboxWaiters a := fun hmem =>
                absurd (h.waiters_waiting a t hmem) (by simp [hts])
              have hstep_p : (step s (.receiveByOccurrence t occ)).1 =
                  { s with taskState := upd s.taskState t (some .waiting), running := none,
                            mailboxWaiters := fun ac => if ac = a then s.mailboxWaiters a ++ [t]
                                                        else s.mailboxWaiters ac } := by
                simp [step, hrt, hts, how, hmb, hd]
              rw [hstep_p]
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact h.readyQ_nodup
              · intro u hm
                by_cases hut : u = t
                · simp [hut] at hm ⊢; have := h.readyQ_queued t hm
                  simp [hts, Option.any, TaskState.isRunnable] at this
                · simp [upd_ne _ _ hut]; exact h.readyQ_queued u hm
              · intro u hru; exact absurd hru (by simp)
              · exact h.timers_nodup
              · intro e he; have hts_e := h.timers_sleep e he
                by_cases hne : e.task = t
                · exact absurd (hne ▸ hts_e) (by simp [hts])
                · simp only [upd_ne _ _ hne]; exact hts_e
              · intro u hu
                by_cases hut : u = t
                · simp [hut] at hu ⊢; exact absurd hts (by simp [h.fresh_none t hu])
                · simp [upd_ne _ _ hut]; exact h.fresh_none u hu
              · exact h.timers_sorted
              · intro u st hts''
                by_cases hut : u = t
                · simp only [upd_self] at hts''; exact ⟨a, by rw [hut]; exact how⟩
                · simp only [upd_ne _ _ hut] at hts''; exact h.spawned_has_owner u st hts''
              · intro u cc hown
                obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
                exact ⟨mbc, hmbc⟩
              · intro u st hts'' hrun
                by_cases hut : u = t
                · simp only [hut, upd_self] at hts''
                  have hst := Option.some.inj hts''.symm; subst hst
                  simp [TaskState.isRunnable] at hrun
                · simp [upd_ne _ _ hut] at hts''; exact h.runnable_queued u st hts'' hrun
              · intro ac u hm
                by_cases hac : ac = a
                · simp only [if_pos hac] at hm ⊢
                  rcases List.mem_append.mp hm with hm | hm
                  · have hts_u := h.waiters_waiting a u hm
                    have hut : u ≠ t := fun he => absurd (he ▸ hts_u) (by simp [hts])
                    simp [upd_ne _ _ hut]; exact hts_u
                  · simp only [List.mem_singleton] at hm; simp [hm, upd_self]
                · simp only [if_neg hac] at hm ⊢
                  have hts_u := h.waiters_waiting ac u hm
                  have hut : u ≠ t := fun he => absurd (he ▸ hts_u) (by simp [hts])
                  simp [upd_ne _ _ hut]; exact hts_u
              · intro ac u hm
                by_cases hac : ac = a
                · simp only [if_pos hac] at hm ⊢
                  rcases List.mem_append.mp hm with hm | hm
                  · exact hac ▸ h.waiters_owned a u hm
                  · simp only [List.mem_singleton] at hm; exact hac ▸ (hm ▸ how)
                · simp only [if_neg hac] at hm ⊢; exact h.waiters_owned ac u hm
              · intro u hts''
                by_cases hut : u = t
                · simp [upd_self, hut] at hts''
                  exact ⟨a, by rw [hut]; exact how, by simp [if_pos rfl, hut]⟩
                · simp [upd_ne _ _ hut] at hts''
                  obtain ⟨a', ha', hmem⟩ := h.waiting_queued u hts''
                  refine ⟨a', ha', ?_⟩
                  by_cases hac : a' = a
                  · simp only [if_pos hac]; exact List.mem_append_left _ (by rwa [hac] at hmem)
                  · simp only [if_neg hac]; exact hmem
              · intro ac
                by_cases hac : ac = a
                · simp only [if_pos hac]
                  exact nodup_append (h.waiters_nodup a) (by simp)
                    (fun u hmem hts_mem => by simp at hts_mem; exact ht_not_waiter (hts_mem ▸ hmem))
                · simp only [if_neg hac]; exact h.waiters_nodup ac
              · -- parent_lt
                exact fun u p hp => h.parent_lt u p (by simpa [step, hrt, hts, how, hmb, hd] using hp)
              · -- parent_spawned: receive parks t → .waiting; still some _
                intro u p hp
                obtain ⟨st, hst⟩ := h.parent_spawned u p
                  (by simpa [step, hrt, hts, how, hmb, hd] using hp)
                by_cases hpt : p = t
                · exact ⟨.waiting, by simp [step, hrt, hts, how, hmb, hd, upd_self, hpt]⟩
                · exact ⟨st, by simp [step, hrt, hts, how, hmb, hd, upd, if_neg hpt]; exact hst⟩
              · -- occ_fresh: mailboxes unchanged, nextMsgId unchanged
                intro a' mb' env hmb' henv; exact h.occ_fresh a' mb' env hmb' henv
              · -- occ_nodup: mailboxes unchanged
                intro a' mb' hmb'; exact h.occ_nodup a' mb' hmb'
              · -- occ_disjoint: mailboxes unchanged
                intro a' b' mba mbb hab hmba hmbb ea hea eb heb
                exact h.occ_disjoint a' b' mba mbb hab hmba hmbb ea hea eb heb
              · -- owner_spawned (RFC 038): taskOwner unchanged; taskState changes at t
                intro u a' how'
                obtain ⟨st, hst⟩ := h.owner_spawned u a' how'
                by_cases hut : u = t
                · subst hut; exact ⟨.waiting, by simp [upd_self]⟩
                · exact ⟨st, by simp [upd_ne _ _ hut]; exact hst⟩
              · -- parent_child_spawned (RFC 038): taskParent unchanged; taskState changes at t
                intro u p hp
                obtain ⟨st, hst⟩ := h.parent_child_spawned u p hp
                by_cases hut : u = t
                · subst hut; exact ⟨.waiting, by simp [upd_self]⟩
                · exact ⟨st, by simp [upd_ne _ _ hut]; exact hst⟩
              · -- timed_has_deadline: t goes to .waiting (not .waitingTimed); others unchanged
                intro u hu
                by_cases hut : u = t
                · simp [hut, upd_self] at hu
                · simp [upd_ne _ _ hut] at hu
                  exact h.timed_has_deadline u hu
              · -- deadline_is_timed: t goes .waiting (no deadline), others unchanged
                intro u dv hd
                -- After rw [hstep_p], hd : { ... }.waitDeadline u = some dv = s.waitDeadline u
                -- (waitDeadline is unchanged). goal: upd s.taskState t .waiting u = .waitingTimed
                have hut : u ≠ t := fun he => by
                  have h1 := h.deadline_is_timed u dv hd
                  rw [he] at h1; rw [h1] at hts; simp at hts
                simp only [upd_ne _ _ hut]; exact h.deadline_is_timed u dv hd
              · -- timed_has_timer: timers unchanged
                intro u hu
                by_cases hut : u = t
                · simp [hut, upd_self] at hu
                · simp [upd_ne _ _ hut] at hu; exact h.timed_has_timer u hu
              · -- timed_is_waiter: timedMailboxWaiters unchanged
                intro u hu
                by_cases hut : u = t
                · simp [hut, upd_self] at hu
                · simp [upd_ne _ _ hut] at hu; exact h.timed_is_waiter u hu
              · -- timed_waiters_valid: timedMailboxWaiters unchanged
                intro a' u hm
                have hut : u ≠ t := fun he => absurd (h.timed_waiters_valid a' u hm) (by simp [he, hts])
                simp [upd_ne _ _ hut]; exact h.timed_waiters_valid a' u hm
              · -- timed_waiters_nodup: timedMailboxWaiters unchanged
                intro a'; exact h.timed_waiters_nodup a'
              · -- timed_waiters_exclusive: timedMailboxWaiters unchanged
                intro a' b' u hab' hma hmb'
                exact h.timed_waiters_exclusive a' b' u hab' hma hmb'
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed =>
        simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h


theorem preserves_wf_receiveFrom {s : RuntimeState} (h : WellFormed s)
    {t : TaskId} {src : ActorId} :
    WellFormed ((step s (.receiveFrom t src)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some st => cases st with
      | running => cases how : s.taskOwner t with
        | none => simpa [step, hrt, hts, how] using h
        | some a => cases hmb : s.mailboxes a with
          | none => simpa [step, hrt, hts, how, hmb] using h
          | some mb => cases hd : mb.dequeueFirst (·.source = some src) with
            | some p =>
              obtain ⟨env, rest⟩ := p
              -- receive dequeues head envelope; nextMsgId unchanged
              have hstep_d : (step s (.receiveFrom t src)).1 =
                  { s with mailboxes := upd s.mailboxes a (some rest) } := by
                simp [step, hrt, hts, how, hmb, hd]
              -- Extract head/tail relationship
              -- selective dequeue: rest is a sublist of mb, so every rest envelope was in mb
              have hsubmem : ∀ {x : Envelope}, x ∈ rest.messages → x ∈ mb.messages :=
                fun {x} hx => (Mailbox.dequeueFirst_sublist _ mb hd).mem hx
              have hsubnodup : (rest.messages.map Envelope.occurrence).Nodup → True := fun _ => trivial
              rw [hstep_d]
              refine ⟨h.readyQ_nodup, fun u hm => h.readyQ_queued u hm, h.running_runs,
                h.timers_nodup, h.timers_sleep, h.fresh_none, h.timers_sorted,
                h.spawned_has_owner, ?_, fun u st hts' hrun => h.runnable_queued u st hts' hrun,
                h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                h.timed_has_deadline, h.deadline_is_timed, h.timed_has_timer, h.timed_is_waiter,
                h.timed_waiters_valid, h.timed_waiters_nodup, h.timed_waiters_exclusive⟩
              · intro u cc hown
                obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
                by_cases hcc : cc = a
                · exact ⟨rest, by simp [upd, hcc]⟩
                · exact ⟨mbc, by simp [upd, if_neg hcc, hmbc]⟩
              · intro u p hp; exact h.parent_lt u p
                  (by simpa [step, hrt, hts, how, hmb, hd] using hp)
              · intro u p hp
                obtain ⟨st, hst⟩ := h.parent_spawned u p
                  (by simpa [step, hrt, hts, how, hmb, hd] using hp)
                exact ⟨st, by simpa [step, hrt, hts, how, hmb, hd] using hst⟩
              · -- occ_fresh: nextMsgId unchanged, rest ⊆ mb (RFC 033)
                intro ac mc env2 hmbc henv2
                by_cases hac : ac = a
                · rw [hac] at hmbc; simp only [upd_self] at hmbc
                  have hv := Option.some.inj hmbc; subst hv
                  exact h.occ_fresh ac mb env2 (hac ▸ hmb) (hsubmem henv2)
                · simp only [upd, if_neg hac] at hmbc; exact h.occ_fresh ac mc env2 hmbc henv2
              · -- occ_nodup: rest ⊆ mb (RFC 033)
                intro ac mc hmbc
                by_cases hac : ac = a
                · rw [hac] at hmbc; simp only [upd_self] at hmbc
                  have hv := Option.some.inj hmbc; subst hv
                  have hnd := h.occ_nodup ac mb (hac ▸ hmb)
                  exact (List.Sublist.map Envelope.occurrence
                    (Mailbox.dequeueFirst_sublist _ mb hd)).nodup hnd
                · simp only [upd, if_neg hac] at hmbc; exact h.occ_nodup ac mc hmbc
              · -- occ_disjoint: rest ⊆ mb (RFC 033)
                intro ac bc mba mbb hab hmba hmbb ea hea eb heb
                by_cases hac : ac = a <;> by_cases hbc : bc = a
                · exact absurd (hac.trans hbc.symm) hab
                · rw [hac] at hmba; simp only [upd_self] at hmba
                  have hv := Option.some.inj hmba; subst hv
                  simp only [upd, if_neg hbc] at hmbb
                  exact h.occ_disjoint ac bc mb mbb hab (hac ▸ hmb) hmbb
                    ea (hsubmem hea) eb heb
                · rw [hbc] at hmbb; simp only [upd_self] at hmbb
                  have hv := Option.some.inj hmbb; subst hv
                  simp only [upd, if_neg hac] at hmba
                  exact h.occ_disjoint ac bc mba mb hab hmba (hbc ▸ hmb)
                    ea hea eb (hsubmem heb)
                · simp only [upd, if_neg hac] at hmba; simp only [upd, if_neg hbc] at hmbb
                  exact h.occ_disjoint ac bc mba mbb hab hmba hmbb ea hea eb heb
              · -- owner_spawned (RFC 038): taskOwner unchanged; taskState = s.taskState
                intro u a' how'
                exact h.owner_spawned u a' how'
              · -- parent_child_spawned (RFC 038): taskParent unchanged; taskState = s.taskState
                intro u p hp
                exact h.parent_child_spawned u p hp
            | none =>
              have ht_not_waiter : t ∉ s.mailboxWaiters a := fun hmem =>
                absurd (h.waiters_waiting a t hmem) (by simp [hts])
              have hstep_p : (step s (.receiveFrom t src)).1 =
                  { s with taskState := upd s.taskState t (some .waiting), running := none,
                            mailboxWaiters := fun ac => if ac = a then s.mailboxWaiters a ++ [t]
                                                        else s.mailboxWaiters ac } := by
                simp [step, hrt, hts, how, hmb, hd]
              rw [hstep_p]
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact h.readyQ_nodup
              · intro u hm
                by_cases hut : u = t
                · simp [hut] at hm ⊢; have := h.readyQ_queued t hm
                  simp [hts, Option.any, TaskState.isRunnable] at this
                · simp [upd_ne _ _ hut]; exact h.readyQ_queued u hm
              · intro u hru; exact absurd hru (by simp)
              · exact h.timers_nodup
              · intro e he; have hts_e := h.timers_sleep e he
                by_cases hne : e.task = t
                · exact absurd (hne ▸ hts_e) (by simp [hts])
                · simp only [upd_ne _ _ hne]; exact hts_e
              · intro u hu
                by_cases hut : u = t
                · simp [hut] at hu ⊢; exact absurd hts (by simp [h.fresh_none t hu])
                · simp [upd_ne _ _ hut]; exact h.fresh_none u hu
              · exact h.timers_sorted
              · intro u st hts''
                by_cases hut : u = t
                · simp only [upd_self] at hts''; exact ⟨a, by rw [hut]; exact how⟩
                · simp only [upd_ne _ _ hut] at hts''; exact h.spawned_has_owner u st hts''
              · intro u cc hown
                obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
                exact ⟨mbc, hmbc⟩
              · intro u st hts'' hrun
                by_cases hut : u = t
                · simp only [hut, upd_self] at hts''
                  have hst := Option.some.inj hts''.symm; subst hst
                  simp [TaskState.isRunnable] at hrun
                · simp [upd_ne _ _ hut] at hts''; exact h.runnable_queued u st hts'' hrun
              · intro ac u hm
                by_cases hac : ac = a
                · simp only [if_pos hac] at hm ⊢
                  rcases List.mem_append.mp hm with hm | hm
                  · have hts_u := h.waiters_waiting a u hm
                    have hut : u ≠ t := fun he => absurd (he ▸ hts_u) (by simp [hts])
                    simp [upd_ne _ _ hut]; exact hts_u
                  · simp only [List.mem_singleton] at hm; simp [hm, upd_self]
                · simp only [if_neg hac] at hm ⊢
                  have hts_u := h.waiters_waiting ac u hm
                  have hut : u ≠ t := fun he => absurd (he ▸ hts_u) (by simp [hts])
                  simp [upd_ne _ _ hut]; exact hts_u
              · intro ac u hm
                by_cases hac : ac = a
                · simp only [if_pos hac] at hm ⊢
                  rcases List.mem_append.mp hm with hm | hm
                  · exact hac ▸ h.waiters_owned a u hm
                  · simp only [List.mem_singleton] at hm; exact hac ▸ (hm ▸ how)
                · simp only [if_neg hac] at hm ⊢; exact h.waiters_owned ac u hm
              · intro u hts''
                by_cases hut : u = t
                · simp [upd_self, hut] at hts''
                  exact ⟨a, by rw [hut]; exact how, by simp [if_pos rfl, hut]⟩
                · simp [upd_ne _ _ hut] at hts''
                  obtain ⟨a', ha', hmem⟩ := h.waiting_queued u hts''
                  refine ⟨a', ha', ?_⟩
                  by_cases hac : a' = a
                  · simp only [if_pos hac]; exact List.mem_append_left _ (by rwa [hac] at hmem)
                  · simp only [if_neg hac]; exact hmem
              · intro ac
                by_cases hac : ac = a
                · simp only [if_pos hac]
                  exact nodup_append (h.waiters_nodup a) (by simp)
                    (fun u hmem hts_mem => by simp at hts_mem; exact ht_not_waiter (hts_mem ▸ hmem))
                · simp only [if_neg hac]; exact h.waiters_nodup ac
              · -- parent_lt
                exact fun u p hp => h.parent_lt u p (by simpa [step, hrt, hts, how, hmb, hd] using hp)
              · -- parent_spawned: receive parks t → .waiting; still some _
                intro u p hp
                obtain ⟨st, hst⟩ := h.parent_spawned u p
                  (by simpa [step, hrt, hts, how, hmb, hd] using hp)
                by_cases hpt : p = t
                · exact ⟨.waiting, by simp [step, hrt, hts, how, hmb, hd, upd_self, hpt]⟩
                · exact ⟨st, by simp [step, hrt, hts, how, hmb, hd, upd, if_neg hpt]; exact hst⟩
              · -- occ_fresh: mailboxes unchanged, nextMsgId unchanged
                intro a' mb' env hmb' henv; exact h.occ_fresh a' mb' env hmb' henv
              · -- occ_nodup: mailboxes unchanged
                intro a' mb' hmb'; exact h.occ_nodup a' mb' hmb'
              · -- occ_disjoint: mailboxes unchanged
                intro a' b' mba mbb hab hmba hmbb ea hea eb heb
                exact h.occ_disjoint a' b' mba mbb hab hmba hmbb ea hea eb heb
              · -- owner_spawned (RFC 038): taskOwner unchanged; taskState changes at t
                intro u a' how'
                obtain ⟨st, hst⟩ := h.owner_spawned u a' how'
                by_cases hut : u = t
                · subst hut; exact ⟨.waiting, by simp [upd_self]⟩
                · exact ⟨st, by simp [upd_ne _ _ hut]; exact hst⟩
              · -- parent_child_spawned (RFC 038): taskParent unchanged; taskState changes at t
                intro u p hp
                obtain ⟨st, hst⟩ := h.parent_child_spawned u p hp
                by_cases hut : u = t
                · subst hut; exact ⟨.waiting, by simp [upd_self]⟩
                · exact ⟨st, by simp [upd_ne _ _ hut]; exact hst⟩
              · -- timed_has_deadline: t goes to .waiting (not .waitingTimed); others unchanged
                intro u hu
                by_cases hut : u = t
                · simp [hut, upd_self] at hu
                · simp [upd_ne _ _ hut] at hu
                  exact h.timed_has_deadline u hu
              · -- deadline_is_timed: t goes .waiting (no deadline), others unchanged
                intro u dv hd
                -- After rw [hstep_p], hd : { ... }.waitDeadline u = some dv = s.waitDeadline u
                -- (waitDeadline is unchanged). goal: upd s.taskState t .waiting u = .waitingTimed
                have hut : u ≠ t := fun he => by
                  have h1 := h.deadline_is_timed u dv hd
                  rw [he] at h1; rw [h1] at hts; simp at hts
                simp only [upd_ne _ _ hut]; exact h.deadline_is_timed u dv hd
              · -- timed_has_timer: timers unchanged
                intro u hu
                by_cases hut : u = t
                · simp [hut, upd_self] at hu
                · simp [upd_ne _ _ hut] at hu; exact h.timed_has_timer u hu
              · -- timed_is_waiter: timedMailboxWaiters unchanged
                intro u hu
                by_cases hut : u = t
                · simp [hut, upd_self] at hu
                · simp [upd_ne _ _ hut] at hu; exact h.timed_is_waiter u hu
              · -- timed_waiters_valid: timedMailboxWaiters unchanged
                intro a' u hm
                have hut : u ≠ t := fun he => absurd (h.timed_waiters_valid a' u hm) (by simp [he, hts])
                simp [upd_ne _ _ hut]; exact h.timed_waiters_valid a' u hm
              · -- timed_waiters_nodup: timedMailboxWaiters unchanged
                intro a'; exact h.timed_waiters_nodup a'
              · -- timed_waiters_exclusive: timedMailboxWaiters unchanged
                intro a' b' u hab' hma hmb'
                exact h.timed_waiters_exclusive a' b' u hab' hma hmb'
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed =>
        simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h



end Henret
