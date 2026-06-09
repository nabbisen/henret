import Henret.Proofs.Lifecycle

namespace Henret

/-! ## List helper lemmas (Lean-core only) -/

theorem nodup_of_sublist {α : Type} {l₁ l₂ : List α}
    (hs : l₁.Sublist l₂) (h : l₂.Nodup) : l₁.Nodup :=
  List.Pairwise.sublist hs h

theorem nodup_append_singleton {α : Type} {l : List α} {t : α}
    (h : l.Nodup) (hn : t ∉ l) : (l ++ [t]).Nodup := by
  have : (l ++ [t]).Pairwise (· ≠ ·) := by
    rw [List.pairwise_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact fun he => hn (he ▸ ha)
  exact this

theorem nodup_append {α : Type} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hd : ∀ a ∈ l₁, a ∉ l₂) :
    (l₁ ++ l₂).Nodup := by
  have : (l₁ ++ l₂).Pairwise (· ≠ ·) := by
    rw [List.pairwise_append]
    exact ⟨h₁, h₂, fun a ha b hb he => hd a ha (by rw [he]; exact hb)⟩
  exact this

/-- Map-nodup gives task-injectivity on timer entries. -/
theorem nodup_task_inj {l : List TimerEntry}
    (h : (l.map TimerEntry.task).Nodup) :
    ∀ {a b : TimerEntry}, a ∈ l → b ∈ l → a.task = b.task → a = b := by
  induction l with
  | nil => intro a b ha _ _; cases ha
  | cons x r ih =>
    rw [List.map_cons, List.nodup_cons] at h
    intro a b ha hb heq
    cases ha with
    | head =>
      cases hb with
      | head => rfl
      | tail _ hbr =>
        exact absurd (List.mem_map_of_mem TimerEntry.task hbr) (heq ▸ h.1)
    | tail _ har =>
      cases hb with
      | head =>
        exact absurd (List.mem_map_of_mem TimerEntry.task har) (heq ▸ h.1)
      | tail _ hbr => exact ih h.2 har hbr heq

/-- Task membership across sorted insertion. -/
theorem mem_map_insertSorted {e : TimerEntry} {l : List TimerEntry} {u : TaskId} :
    u ∈ (Timer.insertSorted e l).map TimerEntry.task ↔
      u = e.task ∨ u ∈ l.map TimerEntry.task := by
  constructor
  · intro hm
    rw [List.mem_map] at hm
    obtain ⟨b, hb, rfl⟩ := hm
    rcases Timer.mem_insertSorted.mp hb with rfl | hbr
    · exact Or.inl rfl
    · exact Or.inr (List.mem_map_of_mem _ hbr)
  · rintro (rfl | hm)
    · exact List.mem_map_of_mem _ (Timer.mem_insertSorted.mpr (Or.inl rfl))
    · rw [List.mem_map] at hm
      obtain ⟨b, hb, rfl⟩ := hm
      exact List.mem_map_of_mem _ (Timer.mem_insertSorted.mpr (Or.inr hb))

/-- Sorted insertion of a fresh task keeps the task list duplicate-free. -/
theorem insertSorted_task_nodup {e : TimerEntry} {l : List TimerEntry}
    (hnotin : e.task ∉ l.map TimerEntry.task)
    (h : (l.map TimerEntry.task).Nodup) :
    ((Timer.insertSorted e l).map TimerEntry.task).Nodup := by
  induction l with
  | nil => simp [Timer.insertSorted]
  | cons x r ih =>
    rw [List.map_cons, List.nodup_cons] at h
    have h1 : e.task ≠ x.task := fun hh =>
      hnotin (by rw [List.map_cons]; exact hh ▸ List.mem_cons_self _ _)
    have h2 : e.task ∉ r.map TimerEntry.task := fun hh =>
      hnotin (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hh)
    by_cases hle : e.deadline ≤ x.deadline
    · simp only [Timer.insertSorted, if_pos hle, List.map_cons, List.nodup_cons]
      refine ⟨?_, h.1, h.2⟩
      rw [List.mem_cons]
      rintro (hh | hh)
      · exact h1 hh
      · exact h2 hh
    · simp only [Timer.insertSorted, if_neg hle, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih h2 h.2⟩
      intro hm
      rcases mem_map_insertSorted.mp hm with hh | hh
      · exact h1 hh.symm
      · exact h.1 hh

/-! ## The well-formedness invariant (RFC 013) -/

/-- Runtime well-formedness: the ownership-location discipline that
holds in every reachable state.

The disjointness of ownership locations is *derived*, not stated:
each location pins the task to a distinct lifecycle state (queued ⇒
runnable, running slot ⇒ `running`, timer ⇒ `sleeping`), and a task
has exactly one state — so a task can occupy at most one location.
See `ready_not_running`, `ready_no_timer`, `running_no_timer`. -/
structure WellFormed (s : RuntimeState) : Prop where
  /-- The scheduler never duplicates a ready task. -/
  readyQ_nodup  : s.readyQ.Nodup
  /-- Every queued task is in a runnable state (`new`/`ready`/`yielded`). -/
  readyQ_queued : ∀ t ∈ s.readyQ, (s.taskState t).any TaskState.isRunnable = true
  /-- The running slot holds a task in `running` state. -/
  running_runs  : ∀ t, s.running = some t → s.taskState t = some .running
  /-- A task has at most one pending timer. -/
  timers_nodup  : (s.timers.map TimerEntry.task).Nodup
  /-- Every timer entry's task is `sleeping`. -/
  timers_sleep  : ∀ e ∈ s.timers, s.taskState e.task = some .sleeping
  /-- Ids at or above the fresh counter are unspawned. -/
  fresh_none    : ∀ t, s.nextId ≤ t → s.taskState t = none
  /-- The timer queue is sorted by deadline (RFC 019). -/
  timers_sorted : Timer.Sorted s.timers
  /-- Every spawned task has an owning actor (RFC 019). -/
  spawned_has_owner :
    ∀ t st, s.taskState t = some st → ∃ a, s.taskOwner t = some a
  /-- Every owning actor exists, i.e. has a mailbox (RFC 019). -/
  owned_has_mailbox :
    ∀ t a, s.taskOwner t = some a → ∃ mb, s.mailboxes a = some mb
  /-- **Schedulable completeness** (RFC 028): every runnable task is in
      the ready queue — the runtime never loses a runnable task. -/
  runnable_queued :
    ∀ t st, s.taskState t = some st → st.isRunnable = true → t ∈ s.readyQ
  /-- Every task in a waiter list is in the `waiting` state (RFC 031). -/
  waiters_waiting :
    ∀ a t, t ∈ s.mailboxWaiters a → s.taskState t = some .waiting
  /-- Every waiter waits on its **own** actor's mailbox (RFC 031). -/
  waiters_owned :
    ∀ a t, t ∈ s.mailboxWaiters a → s.taskOwner t = some a
  /-- Every waiting task is in its own actor's waiter list (RFC 031). -/
  waiting_queued :
    ∀ t, s.taskState t = some .waiting →
      ∃ a, s.taskOwner t = some a ∧ t ∈ s.mailboxWaiters a
  /-- Waiter lists are duplicate-free — needed for deterministic wake-one (RFC 031). -/
  waiters_nodup :
    ∀ a, (s.mailboxWaiters a).Nodup
  /-- Parenthood is acyclic: every parent has a strictly smaller id than
      its child. Follows from fresh-id monotonicity at `spawnChild` time;
      makes cycle-freedom a corollary of `<`-well-foundedness (RFC 032). -/
  parent_lt :
    ∀ t p, s.taskParent t = some p → p < t
  /-- A recorded parent is a real (spawned) task (RFC 032). -/
  parent_spawned :
    ∀ t p, s.taskParent t = some p → ∃ st, s.taskState p = some st
  /-- Every envelope in any mailbox was allocated before the current
      `nextMsgId` counter — the analogue of `fresh_none` for messages (RFC 033). -/
  occ_fresh :
    ∀ a mb env, s.mailboxes a = some mb → env ∈ mb.messages →
      env.occurrence < s.nextMsgId
  /-- Within each mailbox, all occurrence ids are distinct (RFC 033). -/
  occ_nodup :
    ∀ a mb, s.mailboxes a = some mb →
      (mb.messages.map Envelope.occurrence).Nodup
  /-- Across different mailboxes, all occurrence ids are distinct (RFC 033). -/
  occ_disjoint :
    ∀ a b mba mbb, a ≠ b →
      s.mailboxes a = some mba → s.mailboxes b = some mbb →
      ∀ ea ∈ mba.messages, ∀ eb ∈ mbb.messages,
        ea.occurrence ≠ eb.occurrence
  /-- Every owned task is spawned: a task with a `taskOwner` has a `taskState` (RFC 038). -/
  owner_spawned :
    ∀ t a, s.taskOwner t = some a → ∃ st, s.taskState t = some st
  /-- Every task with a parent is itself spawned: a task with a `taskParent`
      has a `taskState` (RFC 038). -/
  parent_child_spawned :
    ∀ t p, s.taskParent t = some p → ∃ st, s.taskState t = some st

/-- The initial state is well-formed (21 fields). -/
theorem wf_init : WellFormed RuntimeState.init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [RuntimeState.init]

/-! ## Ownership uniqueness corollaries (RFC 004 acceptance) -/

/-- A queued task is never in the running slot. -/
theorem WellFormed.ready_not_running {s : RuntimeState} (h : WellFormed s)
    {t : TaskId} (hm : t ∈ s.readyQ) : s.running ≠ some t := by
  intro hr
  have h1 := h.readyQ_queued t hm
  rw [h.running_runs t hr] at h1
  simp [Option.any, TaskState.isRunnable] at h1

/-- A queued task has no pending timer. -/
theorem WellFormed.ready_no_timer {s : RuntimeState} (h : WellFormed s)
    {t : TaskId} (hm : t ∈ s.readyQ) {e : TimerEntry} (he : e ∈ s.timers) :
    e.task ≠ t := by
  intro heq
  have h1 := h.readyQ_queued t hm
  have h2 := h.timers_sleep e he
  rw [heq] at h2
  rw [h2] at h1
  simp [Option.any, TaskState.isRunnable] at h1

/-- The running task has no pending timer. -/
theorem WellFormed.running_no_timer {s : RuntimeState} (h : WellFormed s)
    {t : TaskId} (hr : s.running = some t) {e : TimerEntry} (he : e ∈ s.timers) :
    e.task ≠ t := by
  intro heq
  have h1 := h.running_runs t hr
  have h2 := h.timers_sleep e he
  rw [heq, h1] at h2
  cases h2

end Henret
