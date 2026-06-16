import Henret.Proofs.Metadata
import Henret.Proofs.Preservation.Lifecycle
import Henret.Proofs.Ownership
import Henret.Proofs.Preservation.Messaging
import Henret.Proofs.Preservation.Time
import Henret.Proofs.Supervision
import Henret.Proofs.Preservation.Time
import Henret.Proofs.Preservation.Resource

namespace Henret

/-! ## Invariant preservation assembly (RFC 013, modularised RFC 034)

Per-operation proofs live in `Henret.Proofs.Preservation.{Lifecycle,
Messaging,Time}`. This file assembles them into the public-surface
theorems. -/

/-- `closeActor a` closes actor `a` and marks its actor-owned `allocated`
    resources `closing` (RFC 091). The marking is exactly what keeps `WellFormed`:
    closing the actor would otherwise falsify `allocated_owner_live` for any of
    `a`'s live resources, so the resource transition is mandatory, not cosmetic. -/
theorem preserves_wf_closeActor {s : RuntimeState} (h : WellFormed s) (a : ActorId) :
    WellFormed ((step s (.closeActor a)).1) := by
  cases hmb : s.mailboxes a with
  | none => simpa [step, hmb] using h
  | some mb =>
    have hstep : (step s (.closeActor a)).1 = { s with
        actorStatus := upd s.actorStatus a .closed
        resources   := markActorResourcesClosing a s.resources } := by simp [step, hmb]
    rw [hstep]
    refine ⟨h.readyQ_nodup, h.readyQ_queued, h.running_runs, h.timers_nodup, h.timers_sleep,
      h.fresh_none, h.timers_sorted, h.spawned_has_owner, h.owned_has_mailbox, h.runnable_queued,
      h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, h.parent_lt,
      h.parent_spawned, h.occ_fresh, h.occ_nodup, h.occ_disjoint, h.owner_spawned,
      h.parent_child_spawned, h.timed_has_deadline, h.deadline_is_timed, h.timed_has_timer,
      h.timed_is_waiter, h.timed_waiters_valid, h.timed_waiters_nodup, h.timed_waiters_exclusive,
      h.mailbox_within_capacity, ?_, ?_, ?_, ?_⟩
    · -- resource_fresh
      intro r hr
      exact markActorResourcesClosing_none a s.resources r (h.resource_fresh r hr)
    · -- resource_owner_valid : owner predicates read taskState/mailboxes only (defeq)
      intro r rr hrr
      simp only [markActorResourcesClosing] at hrr
      obtain ⟨st0, hs⟩ := markClosingIfOwner_owner hrr
      exact h.resource_owner_valid r ⟨rr.owner, st0⟩ hs
    · -- allocated_owner_live
      intro r rr hrr hal
      simp only [markActorResourcesClosing] at hrr
      obtain ⟨o, st⟩ := rr; cases hal
      obtain ⟨hs, hpf⟩ := markClosingIfOwner_allocated hrr
      have hl := h.allocated_owner_live r ⟨o, .allocated⟩ hs rfl
      cases ho : o with
      | task t => rw [ho] at hl; exact hl
      | actor b =>
        have hba : b ≠ a := by
          rw [ho] at hpf; intro he; subst he; simp at hpf
        rw [ho] at hl; simp only [OwnerLive, ActorExists] at hl ⊢
        obtain ⟨hex, hne⟩ := hl
        refine ⟨hex, ?_⟩
        simp only [upd, if_neg hba]; exact hne
    · -- closing_owner_closed
      intro r rr hrr hcl
      simp only [markActorResourcesClosing] at hrr
      obtain ⟨o, st⟩ := rr; cases hcl
      rcases markClosingIfOwner_closing hrr with hclr | ⟨hal, hpt⟩
      · -- already closing in s
        have hc := h.closing_owner_closed r ⟨o, .closing⟩ hclr rfl
        cases ho : o with
        | task t => rw [ho] at hc; exact hc
        | actor b =>
          rw [ho] at hc; simp only [OwnerClosed, ActorExists] at hc ⊢
          obtain ⟨hex, hce⟩ := hc
          refine ⟨hex, ?_⟩
          by_cases hba : b = a
          · subst hba; simp [upd_self]
          · simp only [upd, if_neg hba]; exact hce
      · -- newly marked: o == .actor a = true ⇒ o = .actor a
        have hoa : o = .actor a := by simpa using hpt
        subst hoa
        simp only [OwnerClosed, ActorExists]
        exact ⟨⟨mb, hmb⟩, by simp [upd_self]⟩

/-- `shutdown` only flips the runtime status. -/
theorem preserves_wf_shutdown {s : RuntimeState} (h : WellFormed s) :
    WellFormed ((step s .shutdown).1) :=
  WellFormed.runtimeStatus_irrel .shuttingDown h

/-- `stopWhenIdle` only flips the runtime status (or is a no-op). -/
theorem preserves_wf_stopWhenIdle {s : RuntimeState} (h : WellFormed s) :
    WellFormed ((step s .stopWhenIdle).1) := by
  simp only [step]
  split
  · exact WellFormed.runtimeStatus_irrel .stopped h
  · simpa using h

/-- `stopWhenDrained` only flips the runtime status (or is a no-op) (RFC 087). -/
theorem preserves_wf_stopWhenDrained {s : RuntimeState} (h : WellFormed s) :
    WellFormed ((step s .stopWhenDrained).1) := by
  simp only [step]
  split
  · exact WellFormed.runtimeStatus_irrel .stopped h
  · simpa using h

/-- Every operation preserves well-formedness. -/
theorem step_preserves_wf {s : RuntimeState} (h : WellFormed s)
    (op : RuntimeOp) : WellFormed ((step s op).1) := by
  cases op with
  | spawn a    => exact preserves_wf_spawn h a
  | schedule   => exact preserves_wf_schedule h
  | yield t    => exact preserves_wf_yield h
  | complete t => exact preserves_wf_complete h
  | cancel t   => exact preserves_wf_cancel h
  | send t b m => exact preserves_wf_send h
  | receive t  => exact preserves_wf_receive h
  | receiveUntil t d => exact preserves_wf_receiveUntil h
  | receiveByOccurrence t occ => exact preserves_wf_receiveByOccurrence h
  | receiveFrom t src => exact preserves_wf_receiveFrom h
  | inject a m => exact preserves_wf_inject h
  | sleep t d  => exact preserves_wf_sleep h
  | tick t     => exact preserves_wf_tick h
  | wake t     => exact preserves_wf_wake h
  | spawnChild t a => exact preserves_wf_spawnChild h a
  | cancelTree root => exact preserves_wf_cancelTree h root
  | fail t => exact preserves_wf_fail h
  | restartOne p c a => exact preserves_wf_restartOne h a
  | closeActor a => exact preserves_wf_closeActor h a
  | shutdown => exact preserves_wf_shutdown h
  | stopWhenIdle => exact preserves_wf_stopWhenIdle h
  | stopWhenDrained => exact preserves_wf_stopWhenDrained h
  | acquire t => exact preserves_wf_acquire h t
  | acquireActor a => exact preserves_wf_acquireActor h a
  | releaseActor a r => exact preserves_wf_releaseActor h a r
  | release t r => exact preserves_wf_release h t r
  | finalize r => exact preserves_wf_finalize h r
  | setPriority t p => exact preserves_wf_setPriority h t p
  | setDeadline t d => exact preserves_wf_setDeadline h t d

/-- Whole-program invariant preservation. -/
theorem run_preserves_wf {s : RuntimeState} (h : WellFormed s) :
    ∀ ops : List RuntimeOp, WellFormed (run s ops) := by
  intro ops
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih => exact ih (step_preserves_wf h op)

/-- **Every reachable state is well-formed** (RFC 013 headline). -/
theorem reachable_wf (ops : List RuntimeOp) :
    WellFormed (run RuntimeState.init ops) :=
  run_preserves_wf wf_init ops

/-- Every reachable spawned task has an owning actor (RFC 014/019). -/
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

/-- The timer queue is sorted in every reachable state (RFC 019). -/
theorem reachable_timers_sorted (ops : List RuntimeOp) :
    Timer.Sorted (run RuntimeState.init ops).timers :=
  (reachable_wf ops).timers_sorted

/-- **Schedulable completeness** (RFC 028): every reachable runnable
task is in the ready queue — the runtime never loses a runnable task. -/
theorem reachable_runnable_is_queued (ops : List RuntimeOp)
    {t : TaskId} {st : TaskState}
    (h : (run RuntimeState.init ops).taskState t = some st)
    (hrun : st.isRunnable = true) :
    t ∈ (run RuntimeState.init ops).readyQ :=
  (reachable_wf ops).runnable_queued t st h hrun

/-- **Exact queue characterization** (RFC 028): `t ∈ readyQ ↔ runnable`
in every reachable state. -/
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
      rw [hts] at h1; exact ⟨st, rfl, by simpa [Option.any] using h1⟩
  · rintro ⟨st, hts, hrun⟩
    exact (reachable_wf ops).runnable_queued t st hts hrun

/-! ## Waiter exactness (RFC 031) -/

/-- Every reachable waiting task is in its own actor's waiter list. -/
theorem reachable_waiting_is_queued (ops : List RuntimeOp) {t : TaskId}
    (h : (run RuntimeState.init ops).taskState t = some .waiting) :
    ∃ a, (run RuntimeState.init ops).taskOwner t = some a ∧
         t ∈ (run RuntimeState.init ops).mailboxWaiters a :=
  (reachable_wf ops).waiting_queued t h

/-- A task is in at most one waiter list: waiter-list membership
determines the actor (via ownership). -/
theorem reachable_waiter_actor_unique (ops : List RuntimeOp)
    {a b : ActorId} {t : TaskId}
    (ha : t ∈ (run RuntimeState.init ops).mailboxWaiters a)
    (hb : t ∈ (run RuntimeState.init ops).mailboxWaiters b) :
    a = b :=
  Option.some.inj
    (((reachable_wf ops).waiters_owned a t ha).symm.trans
     ((reachable_wf ops).waiters_owned b t hb))

/-- **Exact waiter characterization** (RFC 031 acceptance criterion,
mirror of `reachable_queue_exact`): in every reachable state,
`t ∈ mailboxWaiters a ↔ t is waiting ∧ a owns t`.  Together with
`reachable_waiter_actor_unique` this says every waiting task is in
exactly one waiter list — its own actor's — and that list contains
exactly the tasks waiting on that actor. -/
theorem reachable_waiters_exact (ops : List RuntimeOp)
    {a : ActorId} {t : TaskId} :
    t ∈ (run RuntimeState.init ops).mailboxWaiters a ↔
      (run RuntimeState.init ops).taskState t = some .waiting ∧
      (run RuntimeState.init ops).taskOwner t = some a := by
  constructor
  · intro hm
    exact ⟨(reachable_wf ops).waiters_waiting a t hm,
           (reachable_wf ops).waiters_owned a t hm⟩
  · rintro ⟨hts, how⟩
    obtain ⟨a', ha', hmem⟩ := (reachable_wf ops).waiting_queued t hts
    exact (Option.some.inj (ha'.symm.trans how)) ▸ hmem

/-- Whole-program monotonicity: terminal states survive any program. -/
theorem run_preserves_terminal {u : TaskId} {st : TaskState}
    (hterm : st.isTerminal = true) :
    ∀ {s : RuntimeState}, WellFormed s → s.taskState u = some st →
      ∀ ops : List RuntimeOp, (run s ops).taskState u = some st := by
  intro s h_wf h ops
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih =>
    exact ih (step_preserves_wf h_wf op) (step_preserves_terminal h_wf h hterm op)

theorem run_preserves_completed {s : RuntimeState} {u : TaskId}
    (h_wf : WellFormed s) (h : s.taskState u = some .completed) (ops : List RuntimeOp) :
    (run s ops).taskState u = some .completed :=
  run_preserves_terminal rfl h_wf h ops

theorem run_preserves_cancelled {s : RuntimeState} {u : TaskId}
    (h_wf : WellFormed s) (h : s.taskState u = some .cancelled) (ops : List RuntimeOp) :
    (run s ops).taskState u = some .cancelled :=
  run_preserves_terminal rfl h_wf h ops

/-! ## Wake exactness (RFC 006) -/

/-- **Bounded-mailbox safety** (RFC 056): no reachable mailbox ever exceeds
    its configured capacity. The reachable projection of `WellFormed` field
    `mailbox_within_capacity`; for an unbounded policy the premise is vacuous. -/
theorem reachable_mailbox_within_capacity (ops : List RuntimeOp)
    {a : ActorId} {n : Nat} {mb : Mailbox}
    (hcap : ((run RuntimeState.init ops).mailboxPolicy a).capacity = some n)
    (hmb : (run RuntimeState.init ops).mailboxes a = some mb) :
    mb.messages.length ≤ n :=
  (reachable_wf ops).mailbox_within_capacity a n mb hcap hmb

end Henret

/-!
# Henret.Proofs.InvariantsPreservation

Preservation of the `WellFormed` invariant (RFC 013, modularised RFC 034).

Per-operation proofs are split by operation family:
- `Henret.Proofs.Preservation.Lifecycle` — spawn, schedule, yield, complete, cancel
- `Henret.Proofs.Preservation.Messaging` — send, receive, inject
- `Henret.Proofs.Preservation.Time` — sleep, tick, wake

Public surface (unchanged from pre-RFC-034):
* `step_preserves_wf` — all eleven operations preserve well-formedness.
* `run_preserves_wf` / `reachable_wf` — every reachable state is well-formed.
* `reachable_queue_exact` — the ready queue contains exactly the runnable tasks.
* `reachable_waiters_exact` / `reachable_waiter_actor_unique` /
  `reachable_waiting_is_queued` — every waiting task is in exactly one
  waiter list (its own actor's), and that list contains exactly the
  tasks waiting on that actor (RFC 031).
-/
