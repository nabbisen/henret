import Henret.Scheduler.Policy
import Henret.Proofs.InvariantsPreservation

/-!
# Henret.Proofs.Policy  (RFC 058)

Soundness and preservation for the scheduling-policy layer.

The key structural fact is `reorder_preserves_wf`: moving the chosen task to
the front of `readyQ` is a *permutation*, so the only three `WellFormed`
fields that mention `readyQ` (`readyQ_nodup`, `readyQ_queued`,
`runnable_queued`) transfer across the permutation, and the other thirty are
unchanged. `policyStep_preserves_wf` then follows immediately from the core
`step_preserves_wf` applied to `schedule`, so **every** policy — not just the
built-ins — inherits the full 33-field invariant.
-/

namespace Henret

/-- Reordering the ready queue to put the policy-chosen task at the head
preserves the full `WellFormed` invariant. The reorder is a permutation, so the
three `readyQ` fields transfer and the rest are untouched. -/
theorem reorder_preserves_wf (p : SchedulingPolicy) {s : RuntimeState}
    (h : WellFormed s) : WellFormed (p.reorder s) := by
  unfold SchedulingPolicy.reorder
  cases hc : p.choose s with
  | none => exact h
  | some t =>
    have ht : t ∈ s.readyQ := p.choose_sound s t hc
    have hperm : List.Perm s.readyQ (t :: s.readyQ.erase t) := List.perm_cons_erase ht
    exact
      { readyQ_nodup := hperm.nodup h.readyQ_nodup
        readyQ_queued := fun u hu => h.readyQ_queued u (hperm.mem_iff.mpr hu)
        running_runs := h.running_runs
        timers_nodup := h.timers_nodup
        timers_sleep := h.timers_sleep
        fresh_none := h.fresh_none
        timers_sorted := h.timers_sorted
        spawned_has_owner := h.spawned_has_owner
        owned_has_mailbox := h.owned_has_mailbox
        runnable_queued := fun u st hus hrun =>
          hperm.mem_iff.mp (h.runnable_queued u st hus hrun)
        waiters_waiting := h.waiters_waiting
        waiters_owned := h.waiters_owned
        waiting_queued := h.waiting_queued
        waiters_nodup := h.waiters_nodup
        parent_lt := h.parent_lt
        parent_spawned := h.parent_spawned
        occ_fresh := h.occ_fresh
        occ_nodup := h.occ_nodup
        occ_disjoint := h.occ_disjoint
        owner_spawned := h.owner_spawned
        parent_child_spawned := h.parent_child_spawned
        timed_has_deadline := h.timed_has_deadline
        deadline_is_timed := h.deadline_is_timed
        timed_has_timer := h.timed_has_timer
        timed_is_waiter := h.timed_is_waiter
        timed_waiters_valid := h.timed_waiters_valid
        timed_waiters_nodup := h.timed_waiters_nodup
        timed_waiters_exclusive := h.timed_waiters_exclusive
        mailbox_within_capacity := h.mailbox_within_capacity
        resource_fresh := h.resource_fresh
        resource_owner_valid := h.resource_owner_valid
        allocated_owner_live := h.allocated_owner_live
        closing_owner_closed := h.closing_owner_closed }

/-- **Every policy preserves `WellFormed`.** A policy-directed schedule step
keeps all 33 invariant fields, because it is a `readyQ` permutation followed by
the core `schedule`. -/
theorem policyStep_preserves_wf (p : SchedulingPolicy) {s : RuntimeState}
    (h : WellFormed s) : WellFormed (policyStep p s).1 := by
  unfold policyStep
  exact step_preserves_wf (reorder_preserves_wf p h) .schedule

/-- `schedule` never allocates a task id. -/
theorem schedule_preserves_nextId (s : RuntimeState) :
    (step s .schedule).1.nextId = s.nextId := by
  simp only [step]; (repeat' split) <;> rfl

/-- **A policy never creates a task.** Policy scheduling only chooses among
existing ready tasks; the allocation counter is untouched. -/
theorem policy_does_not_create_task (p : SchedulingPolicy) (s : RuntimeState) :
    (policyStep p s).1.nextId = s.nextId := by
  unfold policyStep
  rw [schedule_preserves_nextId]
  unfold SchedulingPolicy.reorder; cases p.choose s <;> rfl

/-- The FIFO reorder is the identity: moving the head to the head changes
nothing. -/
theorem reorder_fifo_eq (s : RuntimeState) : fifoPolicy.reorder s = s := by
  unfold SchedulingPolicy.reorder fifoPolicy
  cases hq : s.readyQ with
  | nil => simp [hq]
  | cons hd tl =>
    simp only [hq, List.head?_cons, List.erase_cons_head]
    rw [← hq]

/-- **The FIFO policy is exactly the core `schedule`.** Choosing the head and
moving it to the head is a no-op, so `policyStep fifoPolicy` agrees with the
unchanged core scheduler on every state. -/
theorem fifo_policy_equiv_schedule (s : RuntimeState) :
    policyStep fifoPolicy s = step s .schedule := by
  unfold policyStep
  rw [reorder_fifo_eq]

/-- FIFO selects the front of the queue. -/
theorem fifo_picks_head {s : RuntimeState} {a : TaskId} {rest : List TaskId}
    (h : s.readyQ = a :: rest) : fifoPolicy.choose s = some a := by
  simp [fifoPolicy, h]

/-- LIFO selects the back of the queue — a genuinely different choice from FIFO
on any queue of length ≥ 2, yet `policyStep_preserves_wf` covers both. -/
theorem lifo_picks_last {s : RuntimeState} {a : TaskId}
    (h : s.readyQ.getLast? = some a) : lifoPolicy.choose s = some a := h

end Henret
