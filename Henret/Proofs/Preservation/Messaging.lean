import Henret.Proofs.Invariants
import Henret.Proofs.Messaging

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
              have hstep : (step s (.send t b m)).1 =
                  { s with
                    mailboxes := upd s.mailboxes b (some (mb.enqueue ⟨s.nextMsgId, s.taskOwner t, m⟩))
                    nextMsgId := s.nextMsgId + 1 } := by
                simp [step, hrt, hts, how, hmb, hw]
              rw [hstep]
              refine ⟨h.readyQ_nodup, fun u hm => h.readyQ_queued u hm, h.running_runs,
                h.timers_nodup, h.timers_sleep, h.fresh_none, h.timers_sorted,
                h.spawned_has_owner, ?_, fun u st hts' hrun => h.runnable_queued u st hts' hrun,
                h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, ?_, ?_, ?_, ?_, ?_⟩
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
            | cons w ws =>
              have hwt  : s.taskState w = some .waiting := h.waiters_waiting b w (hw ▸ List.mem_cons_self w ws)
              have hwq  : w ∉ s.readyQ := waiting_not_in_readyQ h hwt
              have hwne : w ≠ t := waiter_ne_running h hwt hrt
              -- The step wakes w to .ready and bumps nextMsgId
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
                · exact absurd (hue.symm.trans hru.symm) hwne
                · simp [upd_ne _ _ hue]; exact h.running_runs u (hru ▸ hrt)
              · simp [step, hrt, hts, how, hmb, hw]; exact h.timers_nodup
              · -- timers_sleep
                intro e he; simp [step, hrt, hts, how, hmb, hw] at he ⊢
                have hts_e := h.timers_sleep e he
                by_cases hne : e.task = w
                · exact absurd (hne ▸ hts_e) (by simp [hwt])
                · simp [upd_ne _ _ hne]; exact hts_e
              · -- fresh_none
                intro u hu; simp [step, hrt, hts, how, hmb, hw] at hu ⊢
                by_cases hue : u = w
                · exact absurd hwt (by simp [← hue, h.fresh_none u hu])
                · simp [upd_ne _ _ hue]; exact h.fresh_none u hu
              · simp [step, hrt, hts, how, hmb, hw]; exact h.timers_sorted
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
              · -- parent_spawned: send cons wakes w → .ready; parent still exists
                intro u p hp
                have hpar : s.taskParent u = some p :=
                  by simpa [step, hrt, hts, how, hmb, hw] using hp
                obtain ⟨st, hst⟩ := h.parent_spawned u p hpar
                by_cases hpw : p = w
                · exact ⟨.ready, by simp [step, hrt, hts, how, hmb, hw, upd_self, hpw]⟩
                · exact ⟨st, by simp [step, hrt, hts, how, hmb, hw, upd, if_neg hpw]; exact hst⟩
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
      | new | ready | yielded | sleeping | completed | cancelled | waiting =>
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
                h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, ?_, ?_, ?_, ?_, ?_⟩
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
            | none =>
              have ht_not_waiter : t ∉ s.mailboxWaiters a := fun hmem =>
                absurd (h.waiters_waiting a t hmem) (by simp [hts])
              have hstep_p : (step s (.receive t)).1 =
                  { s with taskState := upd s.taskState t (some .waiting), running := none,
                            mailboxWaiters := fun ac => if ac = a then s.mailboxWaiters a ++ [t]
                                                        else s.mailboxWaiters ac } := by
                simp [step, hrt, hts, how, hmb, hd]
              rw [hstep_p]
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
                have hpar : s.taskParent u = some p :=
                  by simpa [step, hrt, hts, how, hmb, hd] using hp
                obtain ⟨st, hst⟩ := h.parent_spawned u p hpar
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
      | new | ready | yielded | sleeping | completed | cancelled | waiting =>
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
      have hstep : (step s (.inject a m)).1 =
          { s with
            mailboxes := upd s.mailboxes a (some (mb.enqueue ⟨s.nextMsgId, none, m⟩))
            nextMsgId := s.nextMsgId + 1 } := by
        simp [step, hmb, hw]
      rw [hstep]
      refine ⟨h.readyQ_nodup, fun u hm => h.readyQ_queued u hm, h.running_runs,
        h.timers_nodup, h.timers_sleep, h.fresh_none, h.timers_sorted,
        h.spawned_has_owner, ?_, fun u st hts' hrun => h.runnable_queued u st hts' hrun,
        h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, ?_, ?_, ?_, ?_, ?_⟩
      · intro u cc hown
        obtain ⟨mbc, hmbc⟩ := h.owned_has_mailbox u cc hown
        by_cases hcc : cc = a
        · subst hcc; exact ⟨mb.enqueue ⟨s.nextMsgId, none, m⟩, by simp [upd_self]⟩
        · exact ⟨mbc, by simp [upd, if_neg hcc, hmbc]⟩
      · intro u p hp; exact h.parent_lt u p (by simpa [step, hmb, hw] using hp)
      · intro u p hp
        obtain ⟨st, hst⟩ := h.parent_spawned u p (by simpa [step, hmb, hw] using hp)
        exact ⟨st, by simpa [step, hmb, hw] using hst⟩
      · -- occ_fresh (RFC 033): inject nil
        intro ac mc env hmbc henv
        by_cases hac : ac = a
        · rw [hac] at hmbc; simp only [upd_self] at hmbc
          have hv := Option.some.inj hmbc; subst hv
          simp only [Mailbox.enqueue, List.mem_append, List.mem_singleton] at henv
          rcases henv with henv | rfl
          · exact Nat.lt_succ_of_lt (h.occ_fresh a mb env hmb henv)
          · exact Nat.lt_succ_self _
        · simp only [upd, if_neg hac] at hmbc
          exact Nat.lt_succ_of_lt (h.occ_fresh ac mc env hmbc henv)
      · -- occ_nodup (RFC 033): inject nil
        intro ac mc hmbc
        by_cases hac : ac = a
        · rw [hac] at hmbc; simp only [upd_self] at hmbc
          have hv := Option.some.inj hmbc; subst hv
          simp only [Mailbox.enqueue, List.map_append, List.map_singleton]
          exact nodup_append_singleton (h.occ_nodup a mb hmb) (nextMsgId_fresh h hmb)
        · simp only [upd, if_neg hac] at hmbc; exact h.occ_nodup ac mc hmbc
      · -- occ_disjoint (RFC 033): inject nil
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
    | cons w ws =>
      have hwt  : s.taskState w = some .waiting := h.waiters_waiting a w (hw ▸ List.mem_cons_self w ws)
      have hwq  : w ∉ s.readyQ := waiting_not_in_readyQ h hwt
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · simp [step, hmb, hw]; exact h.timers_nodup
      · intro e he; simp [step, hmb, hw] at he ⊢
        have hts_e := h.timers_sleep e he
        by_cases hne : e.task = w
        · exact absurd (hne ▸ hts_e) (by simp [hwt])
        · simp [upd_ne _ _ hne]; exact hts_e
      · intro u hu; simp [step, hmb, hw] at hu ⊢
        by_cases hue : u = w
        · exact absurd hwt (by simp [← hue, h.fresh_none u hu])
        · simp [upd_ne _ _ hue]; exact h.fresh_none u hu
      · simp [step, hmb, hw]; exact h.timers_sorted
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
      · -- parent_spawned: inject may wake w → .ready; still some _
        intro u p hp
        have hpar := (by simpa [step, hmb, hw] using hp : s.taskParent u = some p)
        obtain ⟨st, hst⟩ := h.parent_spawned u p hpar
        by_cases hpw : p = w
        · exact ⟨.ready, by simp [step, hmb, hw, upd_self, hpw]⟩
        · exact ⟨st, by simp [step, hmb, hw, upd, if_neg hpw]; exact hst⟩
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

end Henret
