import Henret.Proofs.InvariantsPreservation
import Henret.Proofs.Resource

/-!
# Henret.Proofs.ResourceReachable  (RFC 057)

Headline reachable theorems for the resource-lifetime ledger:

* the four `WellFormed` resource fields, projected onto reachable states;
* `nextResourceId` monotonicity (allocation ids are strictly increasing);
* the terminal-coupling theorems — a task going terminal moves every
  `allocated` resource it owns to `closing`;
* `released_resource_never_live` — a released resource never returns to
  `allocated`/`closing`.
-/

namespace Henret

open RuntimeState

/-! ## Reachable projections of the resource invariant -/

/-- Resource ids at or above the fresh counter are unallocated, in every
reachable state. -/
theorem reachable_resource_fresh (ops : List RuntimeOp) {r : ResourceId}
    (h : r ≥ (run RuntimeState.init ops).nextResourceId) :
    (run RuntimeState.init ops).resources r = none :=
  (reachable_wf ops).resource_fresh r h

/-- Every reachable resource is owned by a spawned task. -/
theorem reachable_resource_owner_spawned (ops : List RuntimeOp) {r : ResourceId}
    {rr : ResourceRecord} (h : (run RuntimeState.init ops).resources r = some rr) :
    ∃ st, (run RuntimeState.init ops).taskState rr.owner = some st :=
  (reachable_wf ops).resource_owner_spawned r rr h

/-- Every reachable `allocated` resource is owned by a live (non-terminal) task. -/
theorem reachable_allocated_owner_nonterminal (ops : List RuntimeOp)
    {r : ResourceId} {t : TaskId}
    (h : (run RuntimeState.init ops).resources r = some ⟨t, .allocated⟩) :
    ∃ st, (run RuntimeState.init ops).taskState t = some st ∧ ¬ st.isTerminal :=
  (reachable_wf ops).allocated_owner_nonterminal r t h

/-- Every reachable `closing` resource is owned by a terminal task — the
finalization-ledger guarantee that nothing is left dangling on a live task. -/
theorem reachable_closing_owner_terminal (ops : List RuntimeOp)
    {r : ResourceId} {t : TaskId}
    (h : (run RuntimeState.init ops).resources r = some ⟨t, .closing⟩) :
    ∃ st, (run RuntimeState.init ops).taskState t = some st ∧ st.isTerminal :=
  (reachable_wf ops).closing_owner_terminal r t h

/-! ## `nextResourceId` monotonicity -/

/-- A single step never decreases the resource-id counter; `acquire` bumps it
by one, every other operation leaves it fixed. -/
theorem nextResourceId_monotone_step (s : RuntimeState) (op : RuntimeOp) :
    s.nextResourceId ≤ (step s op).1.nextResourceId := by
  cases op <;>
    (simp only [step]; (repeat' split) <;>
      first | exact Nat.le_refl _ | exact Nat.le_succ _)

/-- Allocation ids are non-decreasing along any run. -/
theorem nextResourceId_monotone_run (s : RuntimeState) (ops : List RuntimeOp) :
    s.nextResourceId ≤ (run s ops).nextResourceId := by
  induction ops generalizing s with
  | nil => exact Nat.le_refl _
  | cons op rest ih =>
    rw [run_cons]
    exact Nat.le_trans (nextResourceId_monotone_step s op) (ih (step s op).1)

/-! ## Terminal coupling: going terminal closes owned resources -/

/-- When a task `t` completes, every `allocated` resource it owned becomes
`closing` (RFC 057). The same statement holds for `cancel` and `fail`. -/
theorem complete_marks_owned_resource_closing (s : RuntimeState)
    {t : TaskId} {r : ResourceId} (hrt : s.running = some t)
    (hts : s.taskState t = some .running)
    (hres : s.resources r = some ⟨t, .allocated⟩) :
    (step s (.complete t)).1.resources r = some ⟨t, .closing⟩ := by
  have hstep : (step s (.complete t)).1.resources = markClosingIf (· == t) s.resources := by
    simp [step, hrt, hts]
  rw [hstep]; unfold markClosingIf; rw [hres]; simp

theorem cancel_marks_owned_resource_closing (s : RuntimeState)
    {t : TaskId} {st : TaskState} {r : ResourceId}
    (hts : s.taskState t = some st) (hterm : st.isTerminal = false)
    (hres : s.resources r = some ⟨t, .allocated⟩) :
    (step s (.cancel t)).1.resources r = some ⟨t, .closing⟩ := by
  have hstep : (step s (.cancel t)).1.resources = markClosingIf (· == t) s.resources := by
    simp [step, hts, hterm]
  rw [hstep]; unfold markClosingIf; rw [hres]; simp

theorem fail_marks_owned_resource_closing (s : RuntimeState)
    {t : TaskId} {st : TaskState} {r : ResourceId}
    (hts : s.taskState t = some st) (hterm : st.isTerminal = false)
    (hres : s.resources r = some ⟨t, .allocated⟩) :
    (step s (.fail t)).1.resources r = some ⟨t, .closing⟩ := by
  have hstep : (step s (.fail t)).1.resources = markClosingIf (· == t) s.resources := by
    simp [step, hts, hterm]
  rw [hstep]; unfold markClosingIf; rw [hres]; simp

/-- When the subtree rooted at `root` is cancelled, every `allocated` resource
owned by a cancelled task moves to `closing`. -/
theorem cancelTree_marks_descendant_resource_closing (s : RuntimeState)
    {root t : TaskId} {r : ResourceId}
    (hmem : t ∈ descendantsOf s root) (hres : s.resources r = some ⟨t, .allocated⟩) :
    (step s (.cancelTree root)).1.resources r = some ⟨t, .closing⟩ := by
  rw [cancelTree_step_eq]
  show markClosingIf (fun u => decide (u ∈ descendantsOf s root)) s.resources r = _
  unfold markClosingIf; rw [hres]; simp [hmem]

/-! ## Released resources never return to life -/

/-- A released resource's record is the target of no `upd` or `markClosingIf`
change: every operation leaves `resources r` fixed when `r` is released. -/
theorem step_resources_eq_of_released {s : RuntimeState} (h_wf : WellFormed s)
    {r : ResourceId} {rr : ResourceRecord} (hrr : s.resources r = some rr)
    (hrel : rr.state = .released) (op : RuntimeOp) :
    (step s op).1.resources r = s.resources r := by
  cases op with
  | acquire t =>
    have hrne : r ≠ s.nextResourceId := by
      intro he; rw [he, h_wf.resource_fresh _ (Nat.le_refl _)] at hrr
      exact absurd hrr (by simp)
    simp only [step]; (repeat' split) <;> first | rfl | exact upd_ne _ _ hrne
  | release t rOp =>
    simp only [step]; (repeat' split) <;>
      first | rfl | exact upd_ne _ _ (by intro he; subst he; cases rr; simp_all)
  | finalize rOp =>
    simp only [step]; (repeat' split) <;>
      first | rfl | exact upd_ne _ _ (by intro he; subst he; cases rr; simp_all)
  | setPriority t p =>
    simp only [step]; (repeat' split) <;>
      first | rfl | exact upd_ne _ _ (by intro he; subst he; cases rr; simp_all)
  | setDeadline t d =>
    simp only [step]; (repeat' split) <;>
      first | rfl | exact upd_ne _ _ (by intro he; subst he; cases rr; simp_all)
  | complete t =>
    simp only [step]; (repeat' split) <;>
      first | rfl | exact markClosingIf_eq_of_released (p := (· == t)) hrr hrel
  | cancel t =>
    simp only [step]; (repeat' split) <;>
      first | rfl | exact markClosingIf_eq_of_released (p := (· == t)) hrr hrel
  | fail t =>
    simp only [step]; (repeat' split) <;>
      first | rfl | exact markClosingIf_eq_of_released (p := (· == t)) hrr hrel
  | cancelTree root =>
    simp only [step]
    exact markClosingIf_eq_of_released (p := (· ∈ descendantsOf s root)) hrr hrel
  | spawn a => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | schedule => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | yield t => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | send t b m => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | receive t => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | inject a m => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | sleep t d => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | tick now => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | wake t => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | spawnChild t a => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | receiveUntil t d => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | receiveByOccurrence t occ => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | receiveFrom t src => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | restartOne p c a => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | closeActor a => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | shutdown => first | rfl | (simp only [step]; (repeat' split) <;> rfl)
  | stopWhenIdle => first | rfl | (simp only [step]; (repeat' split) <;> rfl)

/-- A released resource keeps its `released` record under every operation: the
ledger only flips `allocated`/`closing` forward, never back. -/
theorem released_resource_never_live_step {s : RuntimeState} (h_wf : WellFormed s)
    {r : ResourceId} (op : RuntimeOp) (h : ResourceReleased s r) :
    ResourceReleased (step s op).1 r := by
  obtain ⟨rr, hrr, hrel⟩ := h
  exact ⟨rr, (step_resources_eq_of_released h_wf hrr hrel op).trans hrr, hrel⟩

/-- A released resource stays released along any run. -/
theorem released_resource_never_live_run {s : RuntimeState} (h_wf : WellFormed s)
    {r : ResourceId} (ops : List RuntimeOp) (h : ResourceReleased s r) :
    ResourceReleased (run s ops) r := by
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih =>
    rw [run_cons]
    exact ih (step_preserves_wf h_wf op) (released_resource_never_live_step h_wf op h)

/-- In every reachable future, a released resource remains released:
`released` is a terminal ledger state. -/
theorem reachable_released_resource_never_live (ops ops' : List RuntimeOp)
    {r : ResourceId} (h : ResourceReleased (run RuntimeState.init ops) r) :
    ResourceReleased (run (run RuntimeState.init ops) ops') r :=
  released_resource_never_live_run (reachable_wf ops) ops' h

end Henret
