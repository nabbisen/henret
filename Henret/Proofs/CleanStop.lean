import Henret.Proofs.Frozen

/-!
# Clean-stop predicates (RFC 092 — resolution of the `stopped → Drained` question)

The architect's ruling on the deferred RFC 057 Tier 2 item was **Option B**: do
**not** make `runtimeStatus = .stopped` globally imply `Drained`, and do **not**
strengthen `stopWhenIdle` to require a drained ledger (which would collapse
`stopWhenIdle ≡ stopWhenDrained`, a breaking merge conflicting with RFC 087's
additive design). Instead, keep the two stop operations semantically distinct and
expose a **named clean-stop predicate** as the contract-level handle that
downstream bridge/adapter/replay/observability/API RFCs must use.

* `Stopped`        — bare status fact; *no* claim about the resource ledger.
* `StoppedDrained` — stopped **and** the ledger is `Drained`.
* `CleanStopped`   — stopped **and** `Frozen` (quiescent, non-running, drained);
  the strongest, built on the RFC 090 spine.

**Why `Stopped` is only an *entry* fact, not a durable one.** `Frozen` is stated
over `runtimeStatus ≠ .running` rather than `= .stopped` on purpose: `shutdown`
relabels `.stopped → .shuttingDown` (both are `≠ .running`), and no operation ever
returns the status to `.running`. So a clean stop's *durable* content is `Frozen`
(quiescence + drained, permanent), while the exact `.stopped` label may later
become `.shuttingDown`. Permanence is therefore exposed at the `Frozen` level
(`cleanStopped_run_stays_frozen`), reusing the RFC 090 theorems.

The contrast theorem `stopWhenIdle_can_stop_undrained` certifies that the two stop
operations are *intentionally* different — `stopWhenIdle` may reach `.stopped`
with a live resource — so the distinction can never silently rot into a doc claim
that bare `.stopped` means clean.
-/

namespace Henret

/-- The runtime has accepted a stop transition. **No** claim about the resource
    ledger: a `stopWhenIdle` stop may leave resources `allocated`/`closing`. -/
def Stopped (s : RuntimeState) : Prop :=
  s.runtimeStatus = .stopped

/-- A *drained* stop: stopped and every resource is `released`. -/
def StoppedDrained (s : RuntimeState) : Prop :=
  Stopped s ∧ Drained s

/-- A *clean* stop: stopped and `Frozen` (quiescent, non-running, drained). This is
    the contract-level handle for "the runtime shut down cleanly". -/
def CleanStopped (s : RuntimeState) : Prop :=
  Stopped s ∧ Frozen s

/-! ## Projections -/

/-- A clean stop is drained. -/
theorem cleanStopped_drained {s : RuntimeState} (h : CleanStopped s) : Drained s := by
  obtain ⟨_, _, _, _, _, hdr⟩ := h; exact hdr

/-- A clean stop is scheduler-quiescent. -/
theorem cleanStopped_quiescent {s : RuntimeState} (h : CleanStopped s) :
    RuntimeQuiescent s := by
  obtain ⟨_, hrun, hready, htimers, _, _⟩ := h; exact ⟨hrun, hready, htimers⟩

/-- A clean stop is in particular a drained stop. -/
theorem cleanStopped_stoppedDrained {s : RuntimeState} (h : CleanStopped s) :
    StoppedDrained s :=
  ⟨h.1, cleanStopped_drained h⟩

/-! ## Entry: `stopWhenDrained` lands in a clean stop -/

/-- A successful `stopWhenDrained` enters `CleanStopped`. (`stopWhenIdle` does
    **not** get this theorem — that is the whole point; see
    `stopWhenIdle_can_stop_undrained`.) -/
theorem stopWhenDrained_enters_cleanStopped {s : RuntimeState} (h_wf : WellFormed s)
    (h : (step s .stopWhenDrained).2 = .ok) :
    CleanStopped (step s .stopWhenDrained).1 := by
  have hguard : s.running = none ∧ s.readyQ = [] ∧ s.timers = [] ∧ s.resourceDrained = true := by
    simp only [step] at h; split at h
    · rename_i hg; exact hg
    · exact absurd h (by simp)
  have hstate : (step s .stopWhenDrained).1 = { s with runtimeStatus := .stopped } := by
    simp only [step]; split
    · rfl
    · rename_i hg; exact absurd hguard hg
  refine ⟨?_, stopWhenDrained_enters_frozen h_wf h⟩
  unfold Stopped; rw [hstate]

/-- Reachable form: from any reachable state, a successful `stopWhenDrained`
    enters `CleanStopped`. -/
theorem reachable_stopWhenDrained_enters_cleanStopped (ops : List RuntimeOp)
    (h : (step (run RuntimeState.init ops) .stopWhenDrained).2 = .ok) :
    CleanStopped (step (run RuntimeState.init ops) .stopWhenDrained).1 :=
  stopWhenDrained_enters_cleanStopped (reachable_wf ops) h

/-! ## Permanence (at the `Frozen` level)

The durable content of a clean stop is `Frozen`. Exact `.stopped` may degrade to
`.shuttingDown` under a later `shutdown`, but never back to `.running`, and
quiescence + `Drained` persist across **any** subsequent operation sequence. -/

/-- One step from a clean stop preserves `Frozen` (quiescent + drained + non-running). -/
theorem cleanStopped_step_stays_frozen {s : RuntimeState} (h_wf : WellFormed s)
    (h_st : SleepingHasTimer s) (h : CleanStopped s) (op : RuntimeOp) :
    Frozen (step s op).1 :=
  step_preserves_frozen h_wf h_st h.2 op

/-- A whole run from a clean stop preserves `Frozen`. -/
theorem cleanStopped_run_stays_frozen {s : RuntimeState} (h_wf : WellFormed s)
    (h_st : SleepingHasTimer s) (h : CleanStopped s) (ops : List RuntimeOp) :
    Frozen (run s ops) :=
  frozen_run_drained h_wf h_st h.2 ops

/-! ## Contrast: `stopWhenIdle` may stop while not drained

This existential certifies the two stop operations are *intentionally* distinct.
Without it, a future doc could quietly claim bare `.stopped` implies a drained
ledger; this theorem makes that claim refutable. Witness: an actor-owned resource
(RFC 091) is acquired, its task completes (the resource survives task termination),
the scheduler goes quiescent, and `stopWhenIdle` stops with the resource still
`allocated`. -/
theorem stopWhenIdle_can_stop_undrained :
    ∃ ops : List RuntimeOp,
      (run RuntimeState.init ops).runtimeStatus = .stopped ∧
      ¬ Drained (run RuntimeState.init ops) := by
  refine ⟨[.spawn 7, .acquireActor 7, .schedule, .complete 0, .stopWhenIdle], by decide, ?_⟩
  intro hd
  have hrec : (run RuntimeState.init
      [.spawn 7, .acquireActor 7, .schedule, .complete 0, .stopWhenIdle]).resources 0
      = some ⟨.actor 7, .allocated⟩ := by decide
  have := hd 0 _ hrec
  exact absurd this (by decide)

end Henret
