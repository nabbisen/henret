import Henret.Proofs.Invariants
import Henret.Proofs.InvariantsPreservation
import Henret.Proofs.Ownership
import Henret.Proofs.Parenthood
import Henret.Proofs.StepProjections
/-!
  # Henret.Proofs.Restart  (RFC 049)

  Restart-provenance invariants, kept **separate** from the 28-field
  `WellFormed` so the base safety contract is untouched.  Three facts
  about the `restartOf` map hold in every reachable state:

  - `restart_parent_consistent`: a restart replacement and the task it
    replaces share the same parent (supervisor);
  - `restart_old_failed`: the replaced task is `.failed`;
  - `restart_fresh`: the replaced task has a strictly smaller id than its
    replacement (acyclicity of the restart relation).

  Preservation leans on the base layer: 16 ops plus `fail` leave
  `restartOf` unchanged (so the pairs are stable, and `step_preserves_parent`
  / `step_preserves_terminal` carry the per-pair facts forward); `restartOne`
  establishes the new pair from its guards.
-/
namespace Henret

open Henret

/-- Restart-provenance invariant (RFC 049). -/
structure RestartWellFormed (s : RuntimeState) : Prop where
  /-- A restart replacement and the task it replaces share a parent. -/
  restart_parent_consistent :
    ∀ new old, s.restartOf new = some old →
      ∃ p, s.taskParent new = some p ∧ s.taskParent old = some p
  /-- The replaced task is failed. -/
  restart_old_failed :
    ∀ new old, s.restartOf new = some old → s.taskState old = some .failed
  /-- The replaced task has a strictly smaller id (restart acyclicity). -/
  restart_fresh :
    ∀ new old, s.restartOf new = some old → old < new

/-- The initial state has empty restart provenance, vacuously well-formed. -/
theorem restart_wf_init : RestartWellFormed RuntimeState.init :=
  ⟨fun _ _ h => by simp [RuntimeState.init] at h,
   fun _ _ h => by simp [RuntimeState.init] at h,
   fun _ _ h => by simp [RuntimeState.init] at h⟩

/-- No operation other than `restartOne` writes `restartOf`. -/
theorem step_restartOf_stable (s : RuntimeState) (op : RuntimeOp)
    (h2 : ∀ p c a, op ≠ .restartOne p c a) :
    (step s op).1.restartOf = s.restartOf := by
  match op with
  | .spawn _ | .schedule | .yield _ | .complete _ | .cancel _
  | .send _ _ _ | .receive _ | .inject _ _ | .sleep _ _ | .tick _ | .wake _
  | .receiveUntil _ _ | .receiveByOccurrence _ _ | .receiveFrom _ _
  | .fail _ | .spawnChild _ _ =>
      simp only [step]
      (repeat' split) <;> rfl
  | .closeActor _ | .shutdown | .stopWhenIdle =>
      simp only [step] <;> (try split) <;> rfl
  | .cancelTree _ => rfl
  | .restartOne p c a => exact absurd rfl (h2 p c a)

/-- Operations that leave `restartOf` unchanged preserve the restart
    invariant: the pairs are stable, and `step_preserves_parent` /
    `step_preserves_terminal` carry the per-pair facts forward. -/
theorem restart_wf_of_restartOf_stable {s : RuntimeState}
    (h_wf : WellFormed s) (hr : RestartWellFormed s) (op : RuntimeOp)
    (hru : (step s op).1.restartOf = s.restartOf) :
    RestartWellFormed (step s op).1 := by
  have hfresh : s.taskState s.nextId = none := h_wf.fresh_none s.nextId (Nat.le_refl _)
  -- Any task with a parent is spawned, hence below nextId, hence ≠ nextId.
  have hlt : ∀ u p, s.taskParent u = some p → u ≠ s.nextId := by
    intro u p hp he
    obtain ⟨st, hst⟩ := h_wf.parent_child_spawned u p hp
    rw [he, hfresh] at hst; cases hst
  refine ⟨?_, ?_, ?_⟩
  · intro new old hne
    rw [hru] at hne
    obtain ⟨p, hpnew, hpold⟩ := hr.restart_parent_consistent new old hne
    refine ⟨p, ?_, ?_⟩
    · rw [step_preserves_parent (hlt new p hpnew)]; exact hpnew
    · rw [step_preserves_parent (hlt old p hpold)]; exact hpold
  · intro new old hne
    rw [hru] at hne
    exact step_preserves_terminal h_wf (hr.restart_old_failed new old hne) rfl op
  · intro new old hne
    rw [hru] at hne
    exact hr.restart_fresh new old hne

/-- `restartOne` preserves the restart invariant: it establishes the new
    `(nextId, failedChild)` pair from its guards, and leaves existing pairs
    intact. -/
theorem restart_wf_restartOne {s : RuntimeState}
    (h_wf : WellFormed s) (hr : RestartWellFormed s)
    (t failedChild : TaskId) (a : ActorId) :
    RestartWellFormed (step s (.restartOne t failedChild a)).1 := by
  have hfresh0 : s.taskState s.nextId = none := h_wf.fresh_none s.nextId (Nat.le_refl _)
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | some st => cases st with
      | running =>
        by_cases hpar : s.taskParent failedChild = some t
        · cases hfc : s.taskState failedChild with
          | some stf => cases stf with
            | failed =>
              cases hfresh : s.taskState s.nextId with
              | none =>
                -- Valid restart: state explicitly known.
                have hfclt : failedChild < s.nextId := by
                  rcases Nat.lt_or_ge failedChild s.nextId with hlt | hge
                  · exact hlt
                  · have := h_wf.fresh_none failedChild hge
                    rw [this] at hfc; cases hfc
                have hfcne : failedChild ≠ s.nextId := Nat.ne_of_lt hfclt
                -- Explicit projections of the resulting state.
                have hro : (step s (.restartOne t failedChild a)).1.restartOf
                    = upd s.restartOf s.nextId (some failedChild) := by
                  simp [step, hrt, hts, hpar, hfc, hfresh]
                have hpa : (step s (.restartOne t failedChild a)).1.taskParent
                    = upd s.taskParent s.nextId (some t) := by
                  simp [step, hrt, hts, hpar, hfc, hfresh]
                have hst : (step s (.restartOne t failedChild a)).1.taskState
                    = upd s.taskState s.nextId (some .new) := by
                  simp [step, hrt, hts, hpar, hfc, hfresh]
                refine ⟨?_, ?_, ?_⟩
                · intro new old hne
                  rw [hro] at hne
                  by_cases hnn : new = s.nextId
                  · subst hnn
                    rw [upd_self] at hne; cases hne
                    refine ⟨t, ?_, ?_⟩
                    · rw [hpa, upd_self]
                    · rw [hpa, upd, if_neg hfcne]; exact hpar
                  · rw [upd, if_neg hnn] at hne
                    obtain ⟨p, hpnew, hpold⟩ := hr.restart_parent_consistent new old hne
                    -- new, old are existing tasks with parents, hence < nextId
                    have hnewlt : new ≠ s.nextId := by
                      intro he; obtain ⟨q, hq⟩ := h_wf.parent_child_spawned new p hpnew
                      rw [he, hfresh0] at hq; cases hq
                    have holdlt : old ≠ s.nextId := by
                      intro he; obtain ⟨q, hq⟩ := h_wf.parent_child_spawned old p hpold
                      rw [he, hfresh0] at hq; cases hq
                    refine ⟨p, ?_, ?_⟩
                    · rw [hpa, upd, if_neg hnewlt]; exact hpnew
                    · rw [hpa, upd, if_neg holdlt]; exact hpold
                · intro new old hne
                  rw [hro] at hne
                  by_cases hnn : new = s.nextId
                  · subst hnn
                    rw [upd_self] at hne; cases hne
                    rw [hst, upd, if_neg hfcne]; exact hfc
                  · rw [upd, if_neg hnn] at hne
                    have hof := hr.restart_old_failed new old hne
                    have holdlt : old ≠ s.nextId := by
                      intro he; rw [he, hfresh0] at hof; cases hof
                    rw [hst, upd, if_neg holdlt]; exact hof
                · intro new old hne
                  rw [hro] at hne
                  by_cases hnn : new = s.nextId
                  · subst hnn; rw [upd_self] at hne; cases hne; exact hfclt
                  · rw [upd, if_neg hnn] at hne; exact hr.restart_fresh new old hne
              | some _ =>
                exact restart_wf_of_restartOf_stable h_wf hr _
                  (by simp [step, hrt, hts, hpar, hfc, hfresh])
            | new | ready | running | yielded | sleeping | completed | cancelled | waiting | waitingTimed =>
              exact restart_wf_of_restartOf_stable h_wf hr _
                (by simp [step, hrt, hts, hpar, hfc])
          | none =>
            exact restart_wf_of_restartOf_stable h_wf hr _
              (by simp [step, hrt, hts, hpar, hfc])
        · exact restart_wf_of_restartOf_stable h_wf hr _
            (by simp [step, hrt, hts, hpar])
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed | failed =>
        exact restart_wf_of_restartOf_stable h_wf hr _ (by simp [step, hrt, hts])
    | none =>
      exact restart_wf_of_restartOf_stable h_wf hr _ (by simp [step, hrt, hts])
  · exact restart_wf_of_restartOf_stable h_wf hr _ (by simp [step, hrt])

/-- Every operation preserves the restart invariant. -/
theorem step_preserves_restart_wf {s : RuntimeState}
    (h_wf : WellFormed s) (hr : RestartWellFormed s) (op : RuntimeOp) :
    RestartWellFormed (step s op).1 := by
  match op with
  | .restartOne t c a => exact restart_wf_restartOne h_wf hr t c a
  | .spawn _ | .schedule | .yield _ | .complete _ | .cancel _
  | .send _ _ _ | .receive _ | .inject _ _ | .sleep _ _ | .tick _ | .wake _
  | .receiveUntil _ _ | .receiveByOccurrence _ _ | .receiveFrom _ _
  | .fail _ | .spawnChild _ _ | .cancelTree _
  | .closeActor _ | .shutdown | .stopWhenIdle =>
      exact restart_wf_of_restartOf_stable h_wf hr _
        (step_restartOf_stable s _ (by rintro _ _ _ ⟨⟩))

/-- Whole-program preservation of the restart invariant. -/
theorem run_preserves_restart_wf : ∀ (s : RuntimeState),
    WellFormed s → RestartWellFormed s → ∀ ops, RestartWellFormed (run s ops)
  | _, _,    hr, []        => hr
  | s, hwf, hr, op :: rest => by
      rw [run_cons]
      exact run_preserves_restart_wf (step s op).1 (step_preserves_wf hwf op)
              (step_preserves_restart_wf hwf hr op) rest

/-- The restart invariant holds in every reachable state. -/
theorem reachable_restart_wf (ops : List RuntimeOp) :
    RestartWellFormed (run RuntimeState.init ops) :=
  run_preserves_restart_wf RuntimeState.init wf_init restart_wf_init ops

/-! ## Headline theorems (RFC 049) -/

/-- In every reachable state, a restart replacement has a strictly larger
    id than the failed task it replaces. -/
theorem reachable_restart_fresh (ops : List RuntimeOp) {new old : TaskId}
    (h : (run RuntimeState.init ops).restartOf new = some old) : old < new :=
  (reachable_restart_wf ops).restart_fresh new old h

/-- In every reachable state, the task replaced by a restart is failed. -/
theorem reachable_restart_old_failed (ops : List RuntimeOp) {new old : TaskId}
    (h : (run RuntimeState.init ops).restartOf new = some old) :
    (run RuntimeState.init ops).taskState old = some .failed :=
  (reachable_restart_wf ops).restart_old_failed new old h

/-- In every reachable state, a restart replacement and the task it
    replaces share the same supervising parent. -/
theorem reachable_restart_parent_consistent (ops : List RuntimeOp) {new old : TaskId}
    (h : (run RuntimeState.init ops).restartOf new = some old) :
    ∃ p, (run RuntimeState.init ops).taskParent new = some p ∧
         (run RuntimeState.init ops).taskParent old = some p :=
  (reachable_restart_wf ops).restart_parent_consistent new old h

/-- **Parent acyclicity is preserved by restart.**  Restart never
    introduces a parent cycle, because the base `parent_lt` invariant
    (every parent id is strictly smaller than its child) holds in every
    reachable state — including after `restartOne`. -/
theorem restart_preserves_parent_acyclicity (ops : List RuntimeOp)
    {t p : TaskId} (h : (run RuntimeState.init ops).taskParent t = some p) : p < t :=
  (reachable_wf ops).parent_lt t p h

/-- **A restarted task has an owner.**  The fresh replacement created by
    `restartOne` is spawned, so the base `spawned_has_owner` invariant
    gives it an owning actor. -/
theorem restarted_task_has_owner (ops : List RuntimeOp) {new old : TaskId}
    (h : (run RuntimeState.init ops).restartOf new = some old) :
    ∃ a, (run RuntimeState.init ops).taskOwner new = some a := by
  -- `new` has a parent (shares it with `old`), hence is spawned, hence owned.
  obtain ⟨p, hpnew, _⟩ := reachable_restart_parent_consistent ops h
  obtain ⟨st, hst⟩ := (reachable_wf ops).parent_child_spawned new p hpnew
  exact (reachable_wf ops).spawned_has_owner new st hst

end Henret
