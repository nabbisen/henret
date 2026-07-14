import Henret.Scheduler.Model
import Henret.Proofs.InvariantsPreservation

/-!
  # Henret.Proofs.Shutdown  (RFC 055)

  Structured-cancellation and shutdown **safety** theorems, kept
  **separate** from the 33-field `WellFormed` so the base safety contract
  is untouched (the admission-status fields are `WellFormed`-irrelevant;
  see `WellFormed.status_irrel`).

  These are *safety-only* results — no liveness or termination claim.
  They characterise the admission guards added in RFC 055:

  * `closeActor a` flips actor `a` to `.closed` (when it has a mailbox)
    and never deletes mailbox contents — closing rejects *future*
    `send`/`inject` but still allows `receive` to drain.
  * a `.closed` actor rejects both `send` and `inject` targeting it.
  * a non-`running` runtime rejects root `spawn` and environment `inject`.
  * `stopWhenIdle` reaches `.stopped` only from a quiescent state.

  Structured subtree cancellation (the RFC's "cancelSubtree") is already
  provided by `cancelTree` (RFC 039); the RFC's descendant-cancellation
  and non-descendant-preservation obligations are discharged by the
  existing `cancelTree_cancels_task` and `cancelTree_preserves_task_state`
  family in `Henret.Proofs.Supervision`.
-/

namespace Henret

/-! ## Actor closing -/

/-- Closing an actor that has a mailbox sets its status to `.closed`. -/
theorem closeActor_sets_closed {s : RuntimeState} {a : ActorId} {mb : Mailbox}
    (hmb : s.mailboxes a = some mb) :
    ((step s (.closeActor a)).1).actorStatus a = .closed := by
  simp [step, hmb, upd]

/-- Closing an actor with no mailbox is invalid (a no-op). -/
theorem closeActor_no_mailbox_invalid {s : RuntimeState} {a : ActorId}
    (hmb : s.mailboxes a = none) :
    step s (.closeActor a) = (s, .invalid) := by
  simp [step, hmb]

/-- Closing an actor never deletes or alters any mailbox — existing
    messages remain available for `receive` to drain. -/
theorem closeActor_preserves_mailboxes {s : RuntimeState} {a : ActorId} :
    ((step s (.closeActor a)).1).mailboxes = s.mailboxes := by
  simp only [step]; split <;> rfl

/-- Closing actor `a` does not change any *other* actor's status. -/
theorem closeActor_preserves_other_status {s : RuntimeState} {a c : ActorId}
    (h : c ≠ a) :
    ((step s (.closeActor a)).1).actorStatus c = s.actorStatus c := by
  simp only [step]; split
  · simp [upd, h]
  · rfl

/-! ## Closed-actor admission rejection -/

/-- A `.closed` actor rejects every `send` targeting it. -/
theorem closed_actor_rejects_send {s : RuntimeState} {t : TaskId} {b : ActorId}
    {m : Message} (hc : s.actorStatus b = .closed) :
    (step s (.send t b m)).2 = .invalid := by
  simp [step, hc]

/-- A closed `send` is a no-op on state. -/
theorem closed_actor_send_noop {s : RuntimeState} {t : TaskId} {b : ActorId}
    {m : Message} (hc : s.actorStatus b = .closed) :
    (step s (.send t b m)).1 = s := by
  simp [step, hc]

/-- A `.closed` actor rejects every environment `inject` targeting it. -/
theorem closed_actor_rejects_inject {s : RuntimeState} {a : ActorId} {m : Message}
    (hc : s.actorStatus a = .closed) :
    (step s (.inject a m)).2 = .invalid := by
  simp [step, hc]

/-! ## Runtime shutdown admission rejection -/

/-- `shutdown` sets the runtime status to `.shuttingDown`. -/
theorem shutdown_sets_status {s : RuntimeState} :
    ((step s .shutdown).1).runtimeStatus = .shuttingDown := by
  simp [step]

/-- While not `running`, the runtime rejects every root `spawn`. -/
theorem shutdown_rejects_spawn {s : RuntimeState} {a : ActorId}
    (h : s.runtimeStatus ≠ .running) :
    (step s (.spawn a)).2 = .invalid := by
  simp [step, h]

/-- While not `running`, the runtime rejects every environment `inject`. -/
theorem shutdown_rejects_inject {s : RuntimeState} {a : ActorId} {m : Message}
    (h : s.runtimeStatus ≠ .running) :
    (step s (.inject a m)).2 = .invalid := by
  simp [step, h]

/-! ## Quiescence and `stopWhenIdle` -/

/-- `stopWhenIdle` succeeds **only** from a quiescent state: if the step
    reports `.ok`, the runtime had no running task, an empty ready queue,
    and no pending timers. This is the core shutdown-safety property. -/
theorem stopWhenIdle_requires_quiescent {s : RuntimeState}
    (h : (step s .stopWhenIdle).2 = .ok) : RuntimeQuiescent s := by
  by_cases hq : s.running = none ∧ s.readyQ = [] ∧ s.timers = []
  · exact hq
  · simp [step, hq] at h

/-- From a quiescent state, `stopWhenIdle` reaches `.stopped`. -/
theorem stopWhenIdle_sets_stopped {s : RuntimeState} (hq : RuntimeQuiescent s) :
    ((step s .stopWhenIdle).1).runtimeStatus = .stopped := by
  obtain ⟨h1, h2, h3⟩ := hq
  simp [step, h1, h2, h3]

/-- A non-quiescent `stopWhenIdle` is invalid (a no-op). -/
theorem stopWhenIdle_not_quiescent_invalid {s : RuntimeState}
    (hq : ¬ RuntimeQuiescent s) :
    step s .stopWhenIdle = (s, .invalid) := by
  simp only [RuntimeQuiescent] at hq
  simp [step, hq]

end Henret
