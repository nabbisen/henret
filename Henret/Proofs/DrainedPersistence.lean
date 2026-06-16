import Henret.Proofs.ResourceDrain
import Henret.Proofs.ResourceReachable
import Henret.Proofs.InvariantsPreservation

/-!
# Henret.Proofs.DrainedPersistence  (RFC 088 — RFC 057 Tier 2)

RFC 087 gave *drain-before-stop*: `stopWhenDrained` reaches `.stopped` only from
a quiescent, drained state. This module closes the one-step gap that follows:
from a drained state with **no running task**, no single operation can leak a
resource.

* `step_resources_none_run_none` — with `running = none`, no operation writes a
  resource at a previously-empty slot (only `acquire` ever does, and it needs a
  running task).
* `drained_step_drained` — one step from a drained, non-running state stays
  drained: existing resources are `released` and stay so (RFC 057's
  `step_resources_eq_of_released`); no new one appears.
* `stopWhenDrained_then_step_drained` — composition with RFC 087: immediately
  after a successful `stopWhenDrained`, the next operation preserves `Drained`.

**Scope.** Single-step only. Multi-step permanence needs `running = none`
preserved across a whole run, which depends on a `sleeping → timer` invariant
the model does not yet carry; that, the breaking global `stopped → Drained`
invariant, actor-owned resources, and wall-clock liveness remain deferred.
-/

namespace Henret

/-- With no running task **and the runtime not running**, no operation writes a
resource at a slot that was previously empty. Two operations allocate fresh
resources: `acquire` (needs a running task, excluded by `h_run`) and
`acquireActor` (needs `runtimeStatus = .running`, excluded by `h_stat`); every
other operation either leaves the ledger alone or only mutates existing
records (RFC 057/088/091). -/
theorem step_resources_none_run_none {s : RuntimeState} (h_run : s.running = none)
    (h_stat : s.runtimeStatus ≠ .running)
    {r : ResourceId} (hn : s.resources r = none) (op : RuntimeOp) :
    (step s op).1.resources r = none := by
  cases op with
  | acquire t => simp [step, h_run, hn]
  | acquireActor a => simp [step, h_stat, hn]
  | release t rr => simp only [step]; (repeat' split) <;> simp_all
  | finalize rr =>
      simp only [step]; (repeat' split) <;>
        first | exact hn
              | (have hrne : r ≠ rr := by intro he; subst he; simp_all
                 simp_all)
  | complete t => simp only [step]; (repeat' split) <;>
        first | rfl | exact hn | simp only [markClosingIf, markClosingIfOwner, hn]
  | cancel t => simp only [step]; (repeat' split) <;>
        first | rfl | exact hn | simp only [markClosingIf, markClosingIfOwner, hn]
  | fail t => simp only [step]; (repeat' split) <;>
        first | rfl | exact hn | simp only [markClosingIf, markClosingIfOwner, hn]
  | cancelTree root => simp only [step]; (repeat' split) <;>
        first | rfl | exact hn | simp only [applyCancelTree, markClosingIf, markClosingIfOwner, hn]
  | _ => simp only [step]; (repeat' split) <;> simp_all [upd]

/-- **Single-step drained persistence.** From a drained state with no running
task and a non-running runtime, every operation preserves `Drained`: an
already-present resource is `released` (`h_d`) and stays so under any op (RFC
057's `step_resources_eq_of_released`), and no new resource can appear because
both allocation surfaces (`acquire`, `acquireActor`) are blocked. -/
theorem drained_step_drained {s : RuntimeState} (h_wf : WellFormed s)
    (h_run : s.running = none) (h_stat : s.runtimeStatus ≠ .running)
    (h_d : Drained s) (op : RuntimeOp) :
    Drained (step s op).1 := by
  intro r rr hr
  cases hex : s.resources r with
  | none =>
      rw [step_resources_none_run_none h_run h_stat hex op] at hr
      exact Option.noConfusion hr
  | some rr' =>
      have hrel' : rr'.state = .released := h_d r rr' hex
      have heq := step_resources_eq_of_released h_wf hex hrel' op
      rw [heq, hex] at hr
      injection hr with hr; subst hr; exact hrel'

/-- **Composition with RFC 087.** A successful `stopWhenDrained` leaves the
runtime `.stopped` (hence not running) while keeping `running = none` and the
ledger unchanged. The post-stop state meets the `drained_step_drained`
hypotheses, so the next operation cannot leak a resource. -/
theorem stopWhenDrained_then_step_drained {s : RuntimeState} (h_wf : WellFormed s)
    (h : (step s .stopWhenDrained).2 = .ok) (op : RuntimeOp) :
    Drained (step (step s .stopWhenDrained).1 op).1 := by
  have h_d : Drained s := stopWhenDrained_stops_drained h_wf h
  have hguard : s.running = none ∧ s.readyQ = [] ∧ s.timers = [] ∧ s.resourceDrained = true := by
    simp only [step] at h; split at h
    · rename_i hg; exact hg
    · exact absurd h (by simp)
  have hstate : (step s .stopWhenDrained).1 = { s with runtimeStatus := .stopped } := by
    simp only [step]; split
    · rfl
    · rename_i hg; exact absurd hguard hg
  have h_wf' : WellFormed { s with runtimeStatus := .stopped } := by
    have hw := preserves_wf_stopWhenDrained h_wf
    rwa [hstate] at hw
  rw [hstate]
  exact drained_step_drained h_wf' hguard.1 (by simp) h_d op

end Henret
