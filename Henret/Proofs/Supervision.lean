-- Supervision.lean imports only Invariants + Ownership to avoid cycles.
-- (Parenthood.lean → InvariantsPreservation.lean would create a cycle if
--  InvariantsPreservation.lean imported Supervision.lean transitively.)
import Henret.Proofs.Invariants
import Henret.Proofs.Ownership

namespace Henret

/-!
# Henret.Proofs.Supervision  (RFC 039)

Correctness and `WellFormed`-preservation theorems for cascade cancel.

## applyCancelTree projection lemmas

Every field of `applyCancelTree s tc` is @[simp]-tagged for uniform
proof style throughout this file.
-/

/-! ## Projection lemmas (all fields of applyCancelTree) -/

@[simp] theorem ct_taskState (s : RuntimeState) (tc : List TaskId) (u : TaskId) :
    (applyCancelTree s tc).taskState u =
    if u ∈ tc then (match s.taskState u with
      | none    => none
      | some st => if st.isTerminal then some st else some .cancelled)
    else s.taskState u := rfl

@[simp] theorem ct_readyQ (s : RuntimeState) (tc : List TaskId) :
    (applyCancelTree s tc).readyQ = s.readyQ.filter (· ∉ tc) := rfl

@[simp] theorem ct_running (s : RuntimeState) (tc : List TaskId) :
    (applyCancelTree s tc).running =
    if tc.any (fun t => s.running = some t) then none else s.running := rfl

@[simp] theorem ct_timers (s : RuntimeState) (tc : List TaskId) :
    (applyCancelTree s tc).timers = s.timers.filter (fun e => e.task ∉ tc) := rfl

@[simp] theorem ct_mailboxWaiters (s : RuntimeState) (tc : List TaskId) (a : ActorId) :
    (applyCancelTree s tc).mailboxWaiters a = (s.mailboxWaiters a).filter (· ∉ tc) := rfl

@[simp] theorem ct_timedMailboxWaiters (s : RuntimeState) (tc : List TaskId) (a : ActorId) :
    (applyCancelTree s tc).timedMailboxWaiters a = (s.timedMailboxWaiters a).filter (· ∉ tc) := rfl

@[simp] theorem ct_waitDeadline (s : RuntimeState) (tc : List TaskId) (t : TaskId) :
    (applyCancelTree s tc).waitDeadline t = if t ∈ tc then none else s.waitDeadline t := rfl

@[simp] theorem ct_now         (s : RuntimeState) (tc : List TaskId) : (applyCancelTree s tc).now        = s.now        := rfl
@[simp] theorem ct_nextId      (s : RuntimeState) (tc : List TaskId) : (applyCancelTree s tc).nextId     = s.nextId     := rfl
@[simp] theorem ct_nextMsgId   (s : RuntimeState) (tc : List TaskId) : (applyCancelTree s tc).nextMsgId  = s.nextMsgId  := rfl
@[simp] theorem ct_taskOwner   (s : RuntimeState) (tc : List TaskId) : (applyCancelTree s tc).taskOwner  = s.taskOwner  := rfl
@[simp] theorem ct_taskParent  (s : RuntimeState) (tc : List TaskId) : (applyCancelTree s tc).taskParent = s.taskParent := rfl
@[simp] theorem ct_mailboxes   (s : RuntimeState) (tc : List TaskId) : (applyCancelTree s tc).mailboxes  = s.mailboxes  := rfl

/-! ## Descendant collection lemmas -/

theorem descendantsOf_mem_iff {s : RuntimeState} {root t : TaskId} :
    t ∈ descendantsOf s root ↔
    (t < s.nextId ∧ s.taskState t ≠ none ∧ isInSubtreeOf s root t = true) := by
  simp only [descendantsOf, List.mem_filter, List.mem_range, Bool.and_eq_true,
             Bool.decide_eq_true]
  constructor
  · rintro ⟨hl, hts, htree⟩
    refine ⟨hl, ?_, htree⟩
    cases hst : s.taskState t with
    | none => simp [hst] at hts
    | some _ => intro h; exact absurd h (by simp)
  · rintro ⟨hl, hne, htree⟩
    refine ⟨hl, ?_, htree⟩
    cases hst : s.taskState t with
    | none => exact absurd hst hne
    | some _ => simp

theorem descendantsOf_nodup (s : RuntimeState) (root : TaskId) :
    (descendantsOf s root).Nodup :=
  List.Nodup.sublist (List.filter_sublist _) (List.nodup_range _)

theorem descendantsOf_bound {s : RuntimeState} {root t : TaskId}
    (h : t ∈ descendantsOf s root) : t < s.nextId := by
  simp only [descendantsOf, List.mem_filter, List.mem_range] at h; exact h.1

theorem descendantsOf_spawned {s : RuntimeState} {root t : TaskId}
    (h : t ∈ descendantsOf s root) : s.taskState t ≠ none := by
  simp only [descendantsOf, List.mem_filter, List.mem_range, Bool.and_eq_true] at h
  intro heq; simp [heq] at h

theorem descendantsOf_includes_root {s : RuntimeState} {root : TaskId}
    (hsp : s.taskState root ≠ none) (hlt : root < s.nextId) :
    root ∈ descendantsOf s root := by
  simp only [descendantsOf, List.mem_filter, List.mem_range, Bool.and_eq_true]
  refine ⟨hlt, ?_, ?_⟩
  · cases hst : s.taskState root with
    | none => exact absurd hst hsp
    | some _ => simp
  · simp [isInSubtreeOf]

/-! ## cancelTree step equation -/

theorem cancelTree_step_eq (s : RuntimeState) (root : TaskId) :
    (step s (.cancelTree root)).1 = applyCancelTree s (descendantsOf s root) :=
  rfl

/-! ## Core correctness theorems -/

/-- Non-terminal tasks in the cancellation set are cancelled. -/
theorem cancelTree_cancels_task {s : RuntimeState} {root t : TaskId}
    (hd : t ∈ descendantsOf s root) {st : TaskState}
    (hts : s.taskState t = some st) (hnt : ¬st.isTerminal) :
    ((step s (.cancelTree root)).1).taskState t = some .cancelled := by
  simp [cancelTree_step_eq, hd, hts, hnt]

/-- Tasks not in the cancellation set retain their state. -/
theorem cancelTree_preserves_task_state {s : RuntimeState} {root t : TaskId}
    (ht : t ∉ descendantsOf s root) :
    ((step s (.cancelTree root)).1).taskState t = s.taskState t := by
  simp [cancelTree_step_eq, ht]

/-- The root itself is cancelled (if spawned and non-terminal). -/
theorem cancelTree_cancels_root {s : RuntimeState} {root : TaskId}
    (hlt : root < s.nextId) {st : TaskState}
    (hts : s.taskState root = some st) (hnt : ¬st.isTerminal) :
    ((step s (.cancelTree root)).1).taskState root = some .cancelled :=
  cancelTree_cancels_task
    (descendantsOf_includes_root (by simp [hts]) hlt) hts hnt

/-- Cancelled tasks are not in `readyQ`. -/
theorem cancelTree_removes_from_readyQ {s : RuntimeState} {root t : TaskId}
    (hd : t ∈ descendantsOf s root) :
    t ∉ ((step s (.cancelTree root)).1).readyQ := by
  simp [cancelTree_step_eq, List.mem_filter, hd]

/-- Cancelled tasks are not in `timers`. -/
theorem cancelTree_removes_from_timers {s : RuntimeState} {root : TaskId}
    {e : TimerEntry} (hd : e.task ∈ descendantsOf s root) :
    e ∉ ((step s (.cancelTree root)).1).timers := by
  simp [cancelTree_step_eq, List.mem_filter, hd]

/-- Cancelled tasks are not in any `mailboxWaiters` list. -/
theorem cancelTree_removes_from_waiters {s : RuntimeState} {root t : TaskId}
    {a : ActorId} (hd : t ∈ descendantsOf s root) :
    t ∉ ((step s (.cancelTree root)).1).mailboxWaiters a := by
  simp [cancelTree_step_eq, List.mem_filter, hd]




/-! ## WellFormed preservation -/

/-- `cancelTree` preserves all 27 `WellFormed` fields. -/
theorem preserves_wf_cancelTree {s : RuntimeState} (h : WellFormed s) (root : TaskId) :
    WellFormed ((step s (.cancelTree root)).1) := by
  simp only [cancelTree_step_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. readyQ_nodup
    exact List.Nodup.sublist (List.filter_sublist _) h.readyQ_nodup
  · -- 2. readyQ_queued: t ∈ filtered readyQ → t ∉ tc → taskState unchanged → runnable
    intro t htm
    have ⟨hm, hun⟩ : t ∈ s.readyQ ∧ t ∉ descendantsOf s root := by
      simpa [ct_readyQ, List.mem_filter] using htm
    simp only [ct_taskState, if_neg hun]; exact h.readyQ_queued t hm
  · -- 3. running_runs
    intro t hrun
    simp only [ct_running] at hrun
    split at hrun
    · -- any = true → running = none → none = some t, impossible
      exact absurd hrun (by simp)
    · -- any = false → running = s.running
      rename_i hany
      -- from hany: tc.any (...) = false, so t ∉ tc
      have hun : t ∉ descendantsOf s root := by
        intro hc
        have : (descendantsOf s root).any (fun u => s.running = some u) = true :=
          List.any_eq_true.mpr ⟨t, hc, by simp [hrun]⟩
        exact absurd this (by simpa using hany)
      simp only [ct_taskState, if_neg hun]; exact h.running_runs t hrun
  · -- 4. timers_nodup: (filter.map .task) ≤ (original.map .task) → nodup
    exact List.Nodup.sublist
      (List.Sublist.map TimerEntry.task (List.filter_sublist _)) h.timers_nodup
  · -- 5. timers_sleep
    intro e hem
    have ⟨hm, hun⟩ : e ∈ s.timers ∧ e.task ∉ descendantsOf s root := by
      simpa [ct_timers, List.mem_filter] using hem
    simp only [ct_taskState, if_neg hun]; exact h.timers_sleep e hm
  · -- 6. fresh_none
    intro t hge
    simp only [ct_nextId] at hge
    have hun : t ∉ descendantsOf s root :=
      fun hc => absurd hge (Nat.not_le.mpr (descendantsOf_bound hc))
    simp only [ct_taskState, if_neg hun]; exact h.fresh_none t hge
  · -- 7. timers_sorted
    exact List.Pairwise.sublist (List.filter_sublist _) h.timers_sorted
  · -- 8. spawned_has_owner
    intro t st hts
    simp only [ct_taskOwner, ct_taskState] at hts ⊢
    by_cases hun : t ∈ descendantsOf s root
    · -- t ∈ tc: get s.taskState t ≠ none from descendantsOf_spawned
      cases hst0 : s.taskState t with
      | none => exact absurd hst0 (descendantsOf_spawned hun)
      | some st0 => exact h.spawned_has_owner t st0 hst0
    · simp only [hun, ite_false] at hts; exact h.spawned_has_owner t st hts
  · -- 9. owned_has_mailbox: mailboxes unchanged
    intro t a hown; simp only [ct_mailboxes] at *; exact h.owned_has_mailbox t a hown
  · -- 10. runnable_queued: if t runnable in new state → t ∉ tc (cancelled not runnable)
    intro t st hts hrun
    have hun : t ∉ descendantsOf s root := by
      intro hc
      simp only [ct_taskState, hc, ite_true] at hts
      cases hst : s.taskState t with
      | none => simp [hst] at hts
      | some st' =>
        simp only [hst] at hts
        cases hterm : st'.isTerminal with
        | false =>
          simp [hterm] at hts
          -- hts : TaskState.cancelled = st
          cases hts; simp [TaskState.isRunnable] at hrun
        | true =>
          simp [hterm] at hts
          -- hts : st' = st (after Option.some.injEq)
          rw [← hts] at hrun
          cases st' <;> simp_all [TaskState.isTerminal, TaskState.isRunnable]
    simp only [ct_taskState, if_neg hun] at hts
    simpa [ct_readyQ, List.mem_filter] using ⟨h.runnable_queued t st hts hrun, hun⟩
  · -- 11. waiters_waiting
    intro a t htm
    have ⟨hm, hun⟩ : t ∈ s.mailboxWaiters a ∧ t ∉ descendantsOf s root := by
      simpa [ct_mailboxWaiters, List.mem_filter] using htm
    simp only [ct_taskState, if_neg hun]; exact h.waiters_waiting a t hm
  · -- 12. waiters_owned: taskOwner unchanged, waiter membership holds in original
    intro a t htm
    simp only [ct_taskOwner]
    have ⟨hm, _⟩ : t ∈ s.mailboxWaiters a ∧ t ∉ descendantsOf s root := by
      simpa [ct_mailboxWaiters, List.mem_filter] using htm
    exact h.waiters_owned a t hm
  · -- 13. waiting_queued: .waiting not terminal → t ∉ tc
    intro t hts
    have hun : t ∉ descendantsOf s root := by
      intro hc
      simp only [ct_taskState, hc, ite_true] at hts
      cases hst : s.taskState t with
      | none => simp [hst] at hts
      | some st =>
        simp only [hst] at hts
        cases hterm : st.isTerminal with
        | false =>
          simp [hterm] at hts
          -- hts : .cancelled = .waiting, impossible
        | true =>
          simp [hterm] at hts
          -- hts : st = .waiting; hterm : st.isTerminal = true; contradiction
          simp [hts, TaskState.isTerminal] at hterm
    simp only [ct_taskState, if_neg hun] at hts
    simp only [ct_mailboxWaiters, ct_taskOwner]
    obtain ⟨a, ha, hmem⟩ := h.waiting_queued t hts
    exact ⟨a, ha, by simpa [ct_mailboxWaiters, List.mem_filter] using ⟨hmem, hun⟩⟩
  · -- 14. waiters_nodup
    intro a; exact List.Nodup.sublist (List.filter_sublist _) (h.waiters_nodup a)
  · -- 15. parent_lt: taskParent unchanged
    intro t p hp; simp only [ct_taskParent] at hp; exact h.parent_lt t p hp
  · -- 16. parent_spawned: p (the parent) is spawned in new state
    intro t p hp
    simp only [ct_taskParent] at hp
    obtain ⟨st, hst⟩ := h.parent_spawned t p hp
    -- p might or might not be in tc
    by_cases hu : p ∈ descendantsOf s root
    · simp only [ct_taskState, hu, ite_true, hst]
      cases hterm : st.isTerminal with
      | true  => exact ⟨st, by simp [hterm]⟩
      | false => exact ⟨.cancelled, by simp [hterm]⟩
    · exact ⟨st, by simp only [ct_taskState, if_neg hu, hst]⟩
  · -- 17. occ_fresh: mailboxes unchanged
    intro a mb env hmb henv; simp only [ct_mailboxes] at *
    exact h.occ_fresh a mb env hmb henv
  · -- 18. occ_nodup
    intro a mb hmb; simp only [ct_mailboxes] at *; exact h.occ_nodup a mb hmb
  · -- 19. occ_disjoint
    intro a b mba mbb hab hmba hmbb ea hea eb heb
    simp only [ct_mailboxes] at *
    exact h.occ_disjoint a b mba mbb hab hmba hmbb ea hea eb heb
  · -- 20. owner_spawned: t owned → t spawned in new state
    intro t a how; simp only [ct_taskOwner] at how
    obtain ⟨st, hst⟩ := h.owner_spawned t a how
    by_cases hu : t ∈ descendantsOf s root
    · simp only [ct_taskState, hu, ite_true, hst]
      cases hterm : st.isTerminal with
      | true  => exact ⟨st, by simp [hterm]⟩
      | false => exact ⟨.cancelled, by simp [hterm]⟩
    · exact ⟨st, by simp only [ct_taskState, if_neg hu, hst]⟩
  · -- 21. parent_child_spawned: t has parent → t spawned in new state
    intro t p hp; simp only [ct_taskParent] at hp
    obtain ⟨st, hst⟩ := h.parent_child_spawned t p hp
    by_cases hu : t ∈ descendantsOf s root
    · simp only [ct_taskState, hu, ite_true, hst]
      cases hterm : st.isTerminal with
      | true  => exact ⟨st, by simp [hterm]⟩
      | false => exact ⟨.cancelled, by simp [hterm]⟩
    · exact ⟨st, by simp only [ct_taskState, if_neg hu, hst]⟩

  · -- 22. timed_has_deadline
    intro u hu
    -- if u ∈ tc then taskState u ≠ .waitingTimed (it's .cancelled or unchanged terminal)
    have hun : u ∉ descendantsOf s root := by
      intro hm
      simp only [ct_taskState, hm] at hu
      -- hu : (if u ∈ tc then match s.taskState u with ... else s.taskState u) = some .waitingTimed
      -- with hm : u ∈ tc this becomes the match branch
      cases hst : s.taskState u with
      | none => simp [hst, hm] at hu
      | some st =>
        simp only [hst, hm, ite_true] at hu
        by_cases hterm : st.isTerminal
        · simp only [hterm, if_true] at hu
          have hsteq := Option.some.inj hu
          rw [hsteq] at hterm; exact absurd hterm (by decide)
        · have hf : st.isTerminal = false := Bool.eq_false_iff.mpr hterm
          simp [hf] at hu
    simp only [ct_taskState, if_neg hun] at hu
    simp only [ct_waitDeadline, if_neg hun]
    exact h.timed_has_deadline u hu
  · -- 23. deadline_is_timed
    intro u d hd
    simp only [ct_waitDeadline] at hd
    by_cases hm : u ∈ descendantsOf s root
    · simp [hm] at hd
    · simp only [if_neg hm] at hd
      simp only [ct_taskState, if_neg hm]
      exact h.deadline_is_timed u d hd
  · -- 24. timed_has_timer
    intro u hu
    have hun : u ∉ descendantsOf s root := by
      intro hm
      simp only [ct_taskState, hm] at hu
      -- hu : (if u ∈ tc then match s.taskState u with ... else s.taskState u) = some .waitingTimed
      -- with hm : u ∈ tc this becomes the match branch
      cases hst : s.taskState u with
      | none => simp [hst, hm] at hu
      | some st =>
        simp only [hst, hm, ite_true] at hu
        by_cases hterm : st.isTerminal
        · simp only [hterm, if_true] at hu
          have hsteq := Option.some.inj hu
          rw [hsteq] at hterm; exact absurd hterm (by decide)
        · have hf : st.isTerminal = false := Bool.eq_false_iff.mpr hterm
          simp [hf] at hu
    simp only [ct_taskState, if_neg hun] at hu
    obtain ⟨e, he, hek⟩ := h.timed_has_timer u hu
    refine ⟨e, ?_, hek⟩
    simp only [ct_timers, List.mem_filter]
    exact ⟨he, by simp [hek, hun]⟩
  · -- 25. timed_is_waiter
    intro u hu
    have hun : u ∉ descendantsOf s root := by
      intro hm
      simp only [ct_taskState, hm] at hu
      -- hu : (if u ∈ tc then match s.taskState u with ... else s.taskState u) = some .waitingTimed
      -- with hm : u ∈ tc this becomes the match branch
      cases hst : s.taskState u with
      | none => simp [hst, hm] at hu
      | some st =>
        simp only [hst, hm, ite_true] at hu
        by_cases hterm : st.isTerminal
        · simp only [hterm, if_true] at hu
          have hsteq := Option.some.inj hu
          rw [hsteq] at hterm; exact absurd hterm (by decide)
        · have hf : st.isTerminal = false := Bool.eq_false_iff.mpr hterm
          simp [hf] at hu
    simp only [ct_taskState, if_neg hun] at hu
    obtain ⟨a, ha⟩ := h.timed_is_waiter u hu
    refine ⟨a, ?_⟩
    simp only [ct_timedMailboxWaiters, List.mem_filter]
    exact ⟨ha, by simp [hun]⟩
  · -- 26. timed_waiters_valid
    intro a u hu
    simp only [ct_timedMailboxWaiters, List.mem_filter] at hu
    obtain ⟨hmem, hun⟩ := hu
    -- hun : decide (u ∉ descendantsOf s root) = true
    have hun' : u ∉ descendantsOf s root := by simpa using hun
    simp only [ct_taskState, if_neg hun']
    exact h.timed_waiters_valid a u hmem
  · -- 27. timed_waiters_nodup
    intro a
    simp only [ct_timedMailboxWaiters]
    exact List.Nodup.sublist (List.filter_sublist _) (h.timed_waiters_nodup a)
  · -- 28. timed_waiters_exclusive: cancelTree filters each list by (· ∉ tc)
    intro a b u hab hma hmb
    simp only [ct_timedMailboxWaiters] at hma hmb
    exact h.timed_waiters_exclusive a b u hab
      (List.mem_filter.mp hma).1 (List.mem_filter.mp hmb).1

end Henret
