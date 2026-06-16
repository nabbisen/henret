import Henret.Proofs.DrainedPersistence
import Henret.Proofs.SleepingTimer

/-!
# Henret.Proofs.Frozen  (RFC 090 — RFC 057 Tier 2 payoff)

The end-to-end result of the drain/stop thread: a runtime stopped via
`stopWhenDrained` stays **drained** and **quiescent** for the rest of *any*
operation sequence — not just one step (RFC 088).

`Frozen s` bundles the conditions that make a stopped runtime inert on the
resource and scheduling axes:

```
Frozen s := running = none ∧ readyQ = [] ∧ timers = [] ∧ runtimeStatus ≠ running ∧ Drained s
```

`runtimeStatus ≠ running` (rather than `= stopped`) is deliberate: `shutdown`
sends `stopped → shuttingDown`, and both are `≠ running`; no operation ever
returns the runtime to `running`, so the predicate is stable.

* `step_preserves_frozen` — every operation preserves `Frozen`. The `Drained`
  component is RFC 088's `drained_step_drained`; the queue/timer/status
  components hold because every operation that could repopulate them is
  rejected (no running task, empty ready queue, `≠ running` status), and the
  `wake` that RFC 088 could not rule out is blocked by RFC 089's
  `quiescent_no_sleeping`.
* `stopWhenDrained_enters_frozen` — a successful `stopWhenDrained` lands in a
  `Frozen` state.
* `reachable_stopWhenDrained_stays_drained` / `..._stays_quiescent` — the
  headlines: from any reachable state, after a successful `stopWhenDrained`, the
  runtime stays drained and quiescent across every subsequent op sequence.
-/

namespace Henret

def Frozen (s : RuntimeState) : Prop :=
  s.running = none ∧ s.readyQ = [] ∧ s.timers = [] ∧
  s.runtimeStatus ≠ .running ∧ Drained s

theorem step_preserves_frozen {s : RuntimeState} (h_wf : WellFormed s)
    (h_st : SleepingHasTimer s) (h_f : Frozen s) (op : RuntimeOp) :
    Frozen (step s op).1 := by
  obtain ⟨hrun, hready, htimers, hstatus, hdr⟩ := h_f
  have hdr' := drained_step_drained h_wf hrun hdr op
  cases op with
  | spawn a => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | spawnChild t a => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | schedule => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | yield t => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | complete t => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | send t b m => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | receive t => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | inject a m => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | sleep t d => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | restartOne p c a => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | acquire t => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | release t r => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | receiveUntil t d => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | receiveByOccurrence t o => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | receiveFrom t src => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hrun, hready, htimers, hstatus]
  | wake t =>
      have hns := quiescent_no_sleeping h_st ⟨hrun, hready, htimers⟩ t
      refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hns, hrun, hready, htimers, hstatus]
  | finalize r =>
      cases hr : s.resources r with
      | none => refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hr, hrun, hready, htimers, hstatus]
      | some rr =>
          obtain ⟨ro, rst⟩ := rr
          have hrel : rst = .released := hdr r _ hr
          subst hrel
          refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;> simp [step, hr, hrun, hready, htimers, hstatus]
  | tick now =>
      refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;>
        (simp only [step]; split <;>
          simp_all [hrun, hready, htimers, hstatus, Timer.expired, Timer.remaining])
  | cancel t =>
      refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;>
        (simp only [step]; (repeat' split) <;> simp_all [hrun, hready, htimers, hstatus])
  | fail t =>
      refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;>
        (simp only [step]; (repeat' split) <;> simp_all [hrun, hready, htimers, hstatus])
  | cancelTree root =>
      refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;>
        (simp only [step, applyCancelTree] <;> simp_all [hrun, hready, htimers, hstatus])
  | setPriority t p =>
      refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;>
        (simp only [step]; (repeat' split) <;> simp_all [hrun, hready, htimers, hstatus])
  | setDeadline t d =>
      refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;>
        (simp only [step]; (repeat' split) <;> simp_all [hrun, hready, htimers, hstatus])
  | closeActor a =>
      refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;>
        (simp only [step]; (repeat' split) <;> simp_all [hrun, hready, htimers, hstatus])
  | shutdown =>
      exact ⟨by simp [step, hrun], by simp [step, hready], by simp [step, htimers], by simp [step], hdr'⟩
  | stopWhenIdle =>
      refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;>
        (simp only [step]; (repeat' split) <;> simp_all [hrun, hready, htimers])
  | stopWhenDrained =>
      refine ⟨?_, ?_, ?_, ?_, hdr'⟩ <;>
        (simp only [step]; (repeat' split) <;> simp_all [hrun, hready, htimers])

theorem stopWhenDrained_enters_frozen {s : RuntimeState} (h_wf : WellFormed s)
    (h : (step s .stopWhenDrained).2 = .ok) : Frozen (step s .stopWhenDrained).1 := by
  have hguard : s.running = none ∧ s.readyQ = [] ∧ s.timers = [] ∧ s.resourceDrained = true := by
    simp only [step] at h; split at h
    · rename_i hg; exact hg
    · exact absurd h (by simp)
  have hstate : (step s .stopWhenDrained).1 = { s with runtimeStatus := .stopped } := by
    simp only [step]; split
    · rfl
    · rename_i hg; exact absurd hguard hg
  have hdr : Drained s := resourceDrained_drained h_wf hguard.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hstate]
  · exact hguard.1
  · exact hguard.2.1
  · exact hguard.2.2.1
  · simp
  · exact hdr

theorem frozen_run_drained {s : RuntimeState} (h_wf : WellFormed s)
    (h_st : SleepingHasTimer s) (h_f : Frozen s) (ops : List RuntimeOp) :
    Frozen (run s ops) := by
  induction ops generalizing s with
  | nil => exact h_f
  | cons op rest ih =>
      exact ih (step_preserves_wf h_wf op) (step_preserves_sleepingHasTimer h_st op)
               (step_preserves_frozen h_wf h_st h_f op)

theorem reachable_stopWhenDrained_stays_drained (ops : List RuntimeOp)
    (h : (step (run RuntimeState.init ops) .stopWhenDrained).2 = .ok)
    (ops' : List RuntimeOp) :
    Drained (run (step (run RuntimeState.init ops) .stopWhenDrained).1 ops') :=
  (frozen_run_drained
      (step_preserves_wf (reachable_wf ops) _)
      (step_preserves_sleepingHasTimer (reachable_sleepingHasTimer ops) _)
      (stopWhenDrained_enters_frozen (reachable_wf ops) h) ops').2.2.2.2

theorem reachable_stopWhenDrained_stays_quiescent (ops : List RuntimeOp)
    (h : (step (run RuntimeState.init ops) .stopWhenDrained).2 = .ok)
    (ops' : List RuntimeOp) :
    RuntimeQuiescent (run (step (run RuntimeState.init ops) .stopWhenDrained).1 ops') := by
  have hf := frozen_run_drained
      (step_preserves_wf (reachable_wf ops) _)
      (step_preserves_sleepingHasTimer (reachable_sleepingHasTimer ops) _)
      (stopWhenDrained_enters_frozen (reachable_wf ops) h) ops'
  exact ⟨hf.1, hf.2.1, hf.2.2.1⟩

end Henret
