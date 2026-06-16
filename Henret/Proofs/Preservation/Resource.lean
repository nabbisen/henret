import Henret.Proofs.Invariants
import Henret.Proofs.Ownership
import Henret.Proofs.Resource

/-!
# Henret.Proofs.Preservation.Resource  (RFC 057)

`WellFormed` preservation for the three ledger operations `acquire`,
`release`, and `finalize`. Each changes only `resources` (and, for `acquire`,
`nextResourceId`); every other field is untouched, so the 29 non-resource
fields transfer through `wf_resources_only`.
-/

namespace Henret

variable {s : RuntimeState}

/-- `acquire` by a running task allocates a fresh `allocated` resource owned by
that task; non-terminal because the owner is running. -/
theorem preserves_wf_acquire (h : WellFormed s) (t : TaskId) :
    WellFormed ((step s (.acquire t)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some st =>
      cases st with
      | running =>
        have hstep : (step s (.acquire t)).1 = { s with
            resources := upd s.resources s.nextResourceId (some ⟨t, .allocated⟩)
            nextResourceId := s.nextResourceId + 1 } := by simp [step, hrt, hts]
        rw [hstep]
        refine wf_resources_only h ?_ ?_ ?_ ?_
        · intro r hr
          have hrne : r ≠ s.nextResourceId := by omega
          rw [upd_ne _ _ hrne]; exact h.resource_fresh r (by omega)
        · intro r rr hrr
          by_cases hrn : r = s.nextResourceId
          · subst hrn; rw [upd_self] at hrr; injection hrr with hrr; subst hrr
            exact ⟨.running, h.running_runs t hrt⟩
          · rw [upd_ne _ _ hrn] at hrr; exact h.resource_owner_spawned r rr hrr
        · intro r t' hrr
          by_cases hrn : r = s.nextResourceId
          · subst hrn; rw [upd_self] at hrr
            simp only [Option.some.injEq, ResourceRecord.mk.injEq] at hrr
            obtain ⟨rfl, -⟩ := hrr
            exact ⟨.running, h.running_runs t hrt, by decide⟩
          · rw [upd_ne _ _ hrn] at hrr; exact h.allocated_owner_nonterminal r t' hrr
        · intro r t' hrr
          by_cases hrn : r = s.nextResourceId
          · subst hrn; rw [upd_self] at hrr; simp at hrr
          · rw [upd_ne _ _ hrn] at hrr; exact h.closing_owner_terminal r t' hrr
      | new | ready | yielded | sleeping | waiting | waitingTimed
      | completed | cancelled | failed => simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h

/-- `release` by the owning running task flips its `allocated` resource to
`released`. -/
theorem preserves_wf_release (h : WellFormed s) (t : TaskId) (r : ResourceId) :
    WellFormed ((step s (.release t r)).1) := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simpa [step, hrt, hts] using h
    | some st =>
      cases st with
      | running =>
        cases hres : s.resources r with
        | none => simpa [step, hrt, hts, hres] using h
        | some rec =>
          obtain ⟨o, rst⟩ := rec
          cases rst with
          | allocated =>
            by_cases ho : o = t
            · have hstep : (step s (.release t r)).1
                  = { s with resources := upd s.resources r (some ⟨t, .released⟩) } := by
                simp [step, hrt, hts, hres, ho]
              rw [hstep]; rw [ho] at hres
              exact wf_flip_to_released h hres
            · simpa [step, hrt, hts, hres, ho] using h
          | released => simpa [step, hrt, hts, hres] using h
          | closing => simpa [step, hrt, hts, hres] using h
      | new | ready | yielded | sleeping | waiting | waitingTimed
      | completed | cancelled | failed => simpa [step, hrt, hts] using h
  · simpa [step, hrt] using h

/-- `finalize` reclaims a `closing` resource, flipping it to `released`. -/
theorem preserves_wf_finalize (h : WellFormed s) (r : ResourceId) :
    WellFormed ((step s (.finalize r)).1) := by
  cases hres : s.resources r with
  | none => simpa [step, hres] using h
  | some rec =>
    obtain ⟨o, rst⟩ := rec
    cases rst with
    | closing =>
      have hstep : (step s (.finalize r)).1
          = { s with resources := upd s.resources r (some ⟨o, .released⟩) } := by
        simp [step, hres]
      rw [hstep]
      exact wf_flip_to_released h hres
    | allocated => simpa [step, hres] using h
    | released => simpa [step, hres] using h

end Henret
