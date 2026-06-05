import Henret.Proofs.Preservation.Lifecycle
import Henret.Proofs.Ownership
import Henret.Proofs.Preservation.Messaging
import Henret.Proofs.Preservation.Time

namespace Henret

/-! ## Invariant preservation assembly (RFC 013, modularised RFC 034)

Per-operation proofs live in `Henret.Proofs.Preservation.{Lifecycle,
Messaging,Time}`. This file assembles them into the public-surface
theorems. -/

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
  | inject a m => exact preserves_wf_inject h
  | sleep t d  => exact preserves_wf_sleep h
  | tick t     => exact preserves_wf_tick h
  | wake t     => exact preserves_wf_wake h

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
