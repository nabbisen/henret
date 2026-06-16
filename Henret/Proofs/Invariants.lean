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

/-! ## Resource-owner abstraction (RFC 091) -/

/-- An actor **exists** once it has a mailbox. `actorStatus` is total and
defaults to active, so status alone cannot witness existence — without this,
`acquireActor 999999` could allocate for an actor that was never created
(RFC 091 review §5). -/
def ActorExists (s : RuntimeState) (a : ActorId) : Prop :=
  ∃ mb, s.mailboxes a = some mb

/-- The owner of a resource refers to an **existing** principal (RFC 091): a
spawned task, or an existing actor. Generalizes RFC 057's `resource_owner_spawned`. -/
def OwnerValid (s : RuntimeState) : ResourceOwner → Prop
  | .task t  => ∃ st, s.taskState t = some st
  | .actor a => ActorExists s a

/-- The owner can currently hold a live (`allocated`) handle: a non-terminal
task, or an existing non-closed actor (RFC 091). Generalizes
`allocated_owner_nonterminal`. -/
def OwnerLive (s : RuntimeState) : ResourceOwner → Prop
  | .task t  => ∃ st, s.taskState t = some st ∧ ¬ st.isTerminal
  | .actor a => ActorExists s a ∧ s.actorStatus a ≠ .closed

/-- The owner can no longer act, so only a `closing` obligation remains: a
terminal task, or an existing closed actor (RFC 091). Generalizes
`closing_owner_terminal`. -/
def OwnerClosed (s : RuntimeState) : ResourceOwner → Prop
  | .task t  => ∃ st, s.taskState t = some st ∧ st.isTerminal
  | .actor a => ActorExists s a ∧ s.actorStatus a = .closed

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
  /-- Every timer entry's task is `sleeping` or `waitingTimed` (RFC 040: generalized). -/
  timers_sleep  : ∀ e ∈ s.timers, s.taskState e.task = some .sleeping
                                 ∨ s.taskState e.task = some .waitingTimed
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
  /-- Every `waitingTimed` task has a registered deadline (RFC 040). -/
  timed_has_deadline :
    ∀ t, s.taskState t = some .waitingTimed → ∃ d, s.waitDeadline t = some d
  /-- Converse: a task with a deadline is in the `waitingTimed` state (RFC 040). -/
  deadline_is_timed :
    ∀ t d, s.waitDeadline t = some d → s.taskState t = some .waitingTimed
  /-- Every `waitingTimed` task has a corresponding timer entry (RFC 040). -/
  timed_has_timer :
    ∀ t, s.taskState t = some .waitingTimed → ∃ e ∈ s.timers, e.task = t
  /-- Every `waitingTimed` task is in some actor's `timedMailboxWaiters` list (RFC 040). -/
  timed_is_waiter :
    ∀ t, s.taskState t = some .waitingTimed → ∃ a, t ∈ s.timedMailboxWaiters a
  /-- Every task in a `timedMailboxWaiters` list is in the `waitingTimed` state (RFC 040). -/
  timed_waiters_valid :
    ∀ a t, t ∈ s.timedMailboxWaiters a → s.taskState t = some .waitingTimed
  /-- Timed-waiter lists are duplicate-free (RFC 040). -/
  timed_waiters_nodup :
    ∀ a, (s.timedMailboxWaiters a).Nodup
  /-- A task appears in at most one timed-waiter list (RFC 040). -/
  timed_waiters_exclusive :
    ∀ a b t, a ≠ b → t ∈ s.timedMailboxWaiters a → t ∉ s.timedMailboxWaiters b
  /-- No reachable mailbox exceeds its configured capacity (RFC 056). For an
      unbounded policy (`capacity = none`) the premise is vacuous, so this is
      a no-op for any state that configures no bounds. -/
  mailbox_within_capacity :
    ∀ a n mb, (s.mailboxPolicy a).capacity = some n → s.mailboxes a = some mb →
      mb.messages.length ≤ n
  /-- Resource ids at or above the fresh counter are unallocated (RFC 057). -/
  resource_fresh :
    ∀ r, r ≥ s.nextResourceId → s.resources r = none
  /-- Every resource's owner refers to an existing principal (RFC 057/091). -/
  resource_owner_valid :
    ∀ r rr, s.resources r = some rr → OwnerValid s rr.owner
  /-- An `allocated` resource is owned by a principal that can still hold a live
      handle — a non-terminal task or an open actor (RFC 057/091). -/
  allocated_owner_live :
    ∀ r rr, s.resources r = some rr → rr.state = .allocated → OwnerLive s rr.owner
  /-- A `closing` resource's owner can no longer act — a terminal task or a
      closed actor (RFC 057/091). -/
  closing_owner_closed :
    ∀ r rr, s.resources r = some rr → rr.state = .closing → OwnerClosed s rr.owner

/-! ## Resource WellFormed compatibility corollaries (RFC 057 API over RFC 091 fields)

The owner-generic fields above subsume the original task-keyed RFC 057 fields.
These corollaries recover the exact old statements for `.task` owners (so RFC 057
proofs keep their API) and add the symmetric `.actor` projections (RFC 091). -/

/-- RFC 057 compat: a task-owned `allocated` resource has a live owning task. -/
theorem WellFormed.allocated_owner_nonterminal {s : RuntimeState} (h : WellFormed s) :
    ∀ r t, s.resources r = some ⟨.task t, .allocated⟩ →
      ∃ st, s.taskState t = some st ∧ ¬ st.isTerminal := by
  intro r t hr
  have := h.allocated_owner_live r ⟨.task t, .allocated⟩ hr rfl
  simpa [OwnerLive] using this

/-- RFC 057 compat: a task-owned `closing` resource has a terminal owning task. -/
theorem WellFormed.closing_owner_terminal {s : RuntimeState} (h : WellFormed s) :
    ∀ r t, s.resources r = some ⟨.task t, .closing⟩ →
      ∃ st, s.taskState t = some st ∧ st.isTerminal := by
  intro r t hr
  have := h.closing_owner_closed r ⟨.task t, .closing⟩ hr rfl
  simpa [OwnerClosed] using this

/-- RFC 091: an actor-owned `allocated` resource has an existing, non-closed actor. -/
theorem WellFormed.actor_allocated_owner_open {s : RuntimeState} (h : WellFormed s) :
    ∀ r a, s.resources r = some ⟨.actor a, .allocated⟩ →
      ActorExists s a ∧ s.actorStatus a ≠ .closed := by
  intro r a hr
  have := h.allocated_owner_live r ⟨.actor a, .allocated⟩ hr rfl
  simpa [OwnerLive] using this

/-- RFC 091: an actor-owned `closing` resource has an existing, closed actor. -/
theorem WellFormed.actor_closing_owner_closed {s : RuntimeState} (h : WellFormed s) :
    ∀ r a, s.resources r = some ⟨.actor a, .closing⟩ →
      ActorExists s a ∧ s.actorStatus a = .closed := by
  intro r a hr
  have := h.closing_owner_closed r ⟨.actor a, .closing⟩ hr rfl
  simpa [OwnerClosed] using this

/-- From `mailboxFull = false` at a bounded policy, the mailbox has strict room.
    The bridge between the computable `send`/`inject` guard and the capacity
    invariant's `length < n` obligation (RFC 056). -/
theorem lt_capacity_of_not_full {s : RuntimeState} {b : ActorId} {mb : Mailbox} {n : Nat}
    (hcap : (s.mailboxPolicy b).capacity = some n)
    (hfull : s.mailboxFull b mb = false) : mb.messages.length < n := by
  simp only [RuntimeState.mailboxFull, hcap, decide_eq_false_iff_not, Nat.not_le] at hfull
  exact hfull

/-- The initial state is well-formed (33 fields). -/
theorem wf_init : WellFormed RuntimeState.init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [RuntimeState.init]

/-- Changing only `restartOf` preserves well-formedness: no `WellFormed`
    field mentions `restartOf`, so every field is unchanged (RFC 049). -/
theorem WellFormed.restartOf_irrel {s : RuntimeState} (f : TaskId → Option TaskId)
    (h : WellFormed s) : WellFormed { s with restartOf := f } :=
  ⟨h.readyQ_nodup, h.readyQ_queued, h.running_runs, h.timers_nodup, h.timers_sleep,
   h.fresh_none, h.timers_sorted, h.spawned_has_owner, h.owned_has_mailbox, h.runnable_queued,
   h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, h.parent_lt,
   h.parent_spawned, h.occ_fresh, h.occ_nodup, h.occ_disjoint, h.owner_spawned,
   h.parent_child_spawned, h.timed_has_deadline, h.deadline_is_timed, h.timed_has_timer,
   h.timed_is_waiter, h.timed_waiters_valid, h.timed_waiters_nodup, h.timed_waiters_exclusive,
   h.mailbox_within_capacity, h.resource_fresh, h.resource_owner_valid, h.allocated_owner_live, h.closing_owner_closed⟩

/-- Changing only `runtimeStatus` preserves `WellFormed`: no invariant field
    mentions `runtimeStatus`, so each obligation is discharged by the
    corresponding projection through the structure update. (RFC 091 narrowed
    this from the former `status_irrel`: the resource owner invariants now
    depend on `actorStatus`, so an arbitrary `actorStatus` change is no longer
    irrelevant — `closeActor` must mark actor-owned resources to preserve WF.) -/
theorem WellFormed.runtimeStatus_irrel {s : RuntimeState}
    (r : RuntimeStatus) (h : WellFormed s) :
    WellFormed { s with runtimeStatus := r } :=
  ⟨h.readyQ_nodup, h.readyQ_queued, h.running_runs, h.timers_nodup, h.timers_sleep,
   h.fresh_none, h.timers_sorted, h.spawned_has_owner, h.owned_has_mailbox, h.runnable_queued,
   h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, h.parent_lt,
   h.parent_spawned, h.occ_fresh, h.occ_nodup, h.occ_disjoint, h.owner_spawned,
   h.parent_child_spawned, h.timed_has_deadline, h.deadline_is_timed, h.timed_has_timer,
   h.timed_is_waiter, h.timed_waiters_valid, h.timed_waiters_nodup, h.timed_waiters_exclusive,
   h.mailbox_within_capacity, h.resource_fresh, h.resource_owner_valid, h.allocated_owner_live, h.closing_owner_closed⟩

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
  rcases h.timers_sleep e he with h2 | h2 <;>
    (rw [heq] at h2; rw [h2] at h1; simp [Option.any, TaskState.isRunnable] at h1)

/-- The running task has no pending timer. -/
theorem WellFormed.running_no_timer {s : RuntimeState} (h : WellFormed s)
    {t : TaskId} (hr : s.running = some t) {e : TimerEntry} (he : e ∈ s.timers) :
    e.task ≠ t := by
  intro heq
  have h1 := h.running_runs t hr
  rcases h.timers_sleep e he with h2 | h2 <;> rw [heq, h1] at h2 <;> cases h2

end Henret
