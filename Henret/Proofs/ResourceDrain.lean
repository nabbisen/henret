import Henret.Scheduler.Model
import Henret.Proofs.Invariants
import Henret.Proofs.Resource

/-!
# Henret.Proofs.ResourceDrain  (RFC 087 — RFC 057 Tier 2)

Drain discipline on the safety/possibility axis:

* **drain progress** — from any state, a `closing` resource is immediately
  finalizable (`closing_finalize_releases`); combined with Tier 1's
  "terminal marks closing", the drain path is always open.
* **drain-before-stop** — the additive `stopWhenDrained` operation reaches
  `stopped` only when the runtime is quiescent *and* drained
  (`stopWhenDrained_stops_drained`).

No theorem here claims a resource is *eventually* finalized — only that
finalization is always *available* and a drained stop is *possible*.
-/

namespace Henret

/-- No resource is still `allocated` or `closing`: the ledger is fully drained. -/
def Drained (s : RuntimeState) : Prop :=
  ∀ r rr, s.resources r = some rr → rr.state = .released

/-- **Drain progress.** A `closing` resource can always be finalized in one
step, which releases it. The drain path is never blocked. -/
theorem closing_finalize_releases (s : RuntimeState) (r : ResourceId) (o : ResourceOwner)
    (h : s.resources r = some ⟨o, .closing⟩) :
    (step s (.finalize r)).2 = .ok ∧
    (step s (.finalize r)).1.resources r = some ⟨o, .released⟩ := by
  simp [step, h]

/-- **The decidable drain check captures `Drained`** (under well-formedness):
allocated ids are all `< nextResourceId`, so the bounded check suffices. -/
theorem resourceDrained_drained {s : RuntimeState} (h_wf : WellFormed s)
    (h : s.resourceDrained = true) : Drained s := by
  intro r rr hr
  have hlt : r < s.nextResourceId := by
    rcases Nat.lt_or_ge r s.nextResourceId with h' | h'
    · exact h'
    · rw [h_wf.resource_fresh r h'] at hr; simp at hr
  unfold RuntimeState.resourceDrained at h
  rw [List.all_eq_true] at h
  have hd := h r (List.mem_range.mpr hlt)
  rw [hr] at hd
  simpa using hd

/-- **Drain-before-stop.** If `stopWhenDrained` succeeds (transitions to
`stopped`), the resource ledger was fully drained — a drained stop never leaves a
resource leaked. -/
theorem stopWhenDrained_stops_drained {s : RuntimeState} (h_wf : WellFormed s)
    (h : (step s .stopWhenDrained).2 = .ok) : Drained s := by
  simp only [step] at h
  split at h
  · rename_i hg; exact resourceDrained_drained h_wf hg.2.2.2
  · exact absurd h (by simp)

/-- A quiescent, drained state lets `stopWhenDrained` reach `.stopped`. -/
theorem stopWhenDrained_stops {s : RuntimeState}
    (hq : s.running = none ∧ s.readyQ = [] ∧ s.timers = [] ∧ s.resourceDrained = true) :
    (step s .stopWhenDrained).1.runtimeStatus = .stopped ∧
    (step s .stopWhenDrained).2 = .ok := by
  simp [step, hq]

/-- Otherwise `stopWhenDrained` is a no-op (`.invalid`, state unchanged). -/
theorem stopWhenDrained_noop {s : RuntimeState}
    (hq : ¬ (s.running = none ∧ s.readyQ = [] ∧ s.timers = [] ∧ s.resourceDrained = true)) :
    step s .stopWhenDrained = (s, .invalid) := by
  simp [step, hq]

/-- **RFC 091.** Under `Drained`, `markActorResourcesClosing` is the identity:
no resource is `allocated`, so there is nothing to mark `closing`. The
actor-owned analogue of `markClosingIf_eq_of_released`; used to show
`closeActor` is inert on a drained ledger (drain/frozen spine). -/
theorem markActorResourcesClosing_eq_of_drained {s : RuntimeState} (a : ActorId)
    (h_d : Drained s) :
    markActorResourcesClosing a s.resources = s.resources := by
  funext r
  cases hex : s.resources r with
  | none => simp [markActorResourcesClosing, markClosingIfOwner, hex]
  | some rr =>
    have hrel : rr.state = .released := h_d r rr hex
    exact (markActorResourcesClosing_eq_of_released hex hrel).trans hex

end Henret
