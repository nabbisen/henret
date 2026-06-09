import Henret.Proofs.InvariantsPreservation
import Henret.Scheduler.Model

namespace Henret

/-!
# Henret.Proofs.Parenthood

Direct theorems about `spawnChild` and the parenthood relation (RFC 032 + RFC 038).

## Headline theorems
* `spawnChild_sets_parent` — the child records the running task as its parent.
* `spawnChild_sets_owner` — the child is owned by the specified `childActor`
  (generalized in RFC 038: `parentOwner` and `childActor` are now distinct).
* `spawnChild_child_spawned` — the child's task state is `.new` after creation.
* `spawnChild_not_running_invalid` / `spawnChild_unowned_invalid` — guard theorems.
* `step_preserves_parent` — parenthood is immutable after creation.
* `reachable_parent_lt` — in every reachable state, every parent has a
  strictly smaller id than its child.
* `parent_chain_terminates` — every ancestor chain reaches a root in at
  most `t` steps (acyclicity deliverable).
* `reachable_owner_spawned` — every owned task is spawned (RFC 038).
* `reachable_parent_child_spawned` — every task with a parent is spawned (RFC 038).
-/

/-! ## Creation effects -/

/-- A successful `spawnChild` sets the new task's parent to the caller.
    `parentOwner` and `childActor` are distinct: the child actor is `childActor`,
    not necessarily `taskOwner t`. (RFC 038 generalization.) -/
theorem spawnChild_sets_parent {s : RuntimeState} {t : TaskId}
    {parentOwner childActor : ActorId}
    (hrt    : s.running = some t)
    (hts    : s.taskState t = some .running)
    (how    : s.taskOwner t = some parentOwner)
    (hfresh : s.taskState s.nextId = none) :
    ((step s (.spawnChild t childActor)).1).taskParent s.nextId = some t := by
  simp [step, hrt, hts, how, hfresh, upd_self]

/-- `spawnChild` sets the child's owner to `childActor`.
    `parentOwner` is the parent task's actor; `childActor` is the child's actor.
    These need not be equal. (RFC 038 generalization.) -/
theorem spawnChild_sets_owner {s : RuntimeState} {t : TaskId}
    {parentOwner childActor : ActorId}
    (hrt    : s.running = some t)
    (hts    : s.taskState t = some .running)
    (how    : s.taskOwner t = some parentOwner)
    (hfresh : s.taskState s.nextId = none) :
    ((step s (.spawnChild t childActor)).1).taskOwner s.nextId = some childActor := by
  simp [step, hrt, hts, how, hfresh, upd_self]

/-- `spawnChild` queues the child task. (RFC 038 generalization.) -/
theorem spawnChild_queues_child {s : RuntimeState} {t : TaskId}
    {parentOwner childActor : ActorId}
    (hrt    : s.running = some t)
    (hts    : s.taskState t = some .running)
    (how    : s.taskOwner t = some parentOwner)
    (hfresh : s.taskState s.nextId = none) :
    s.nextId ∈ ((step s (.spawnChild t childActor)).1).readyQ := by
  simp [step, hrt, hts, how, hfresh]

/-- The freshly spawned child task has state `.new`. (RFC 038) -/
theorem spawnChild_child_spawned {s : RuntimeState} {t : TaskId}
    {parentOwner childActor : ActorId}
    (hrt    : s.running = some t)
    (hts    : s.taskState t = some .running)
    (how    : s.taskOwner t = some parentOwner)
    (hfresh : s.taskState s.nextId = none) :
    ((step s (.spawnChild t childActor)).1).taskState s.nextId = some .new := by
  simp [step, hrt, hts, how, hfresh, upd_self]

/-! ## Guard theorems -/

/-- Only the running task can spawn a child. -/
theorem spawnChild_not_running_invalid {s : RuntimeState} {t : TaskId} {a : ActorId}
    (h : s.running ≠ some t) :
    (step s (.spawnChild t a)).2 = .invalid := by
  simp [step, h]

/-- A task without an owning actor cannot spawn a child. -/
theorem spawnChild_unowned_invalid {s : RuntimeState} {t : TaskId} {a : ActorId}
    (hrt : s.running = some t)
    (hts : s.taskState t = some .running)
    (how : s.taskOwner t = none) :
    (step s (.spawnChild t a)).2 = .invalid := by
  simp [step, hrt, hts, how]

/-! ## Immutability -/

/-- Parenthood is set at creation and never changed. No operation other than
    `spawnChild` writes `taskParent`; `spawnChild` only writes the fresh slot. -/
theorem step_preserves_parent {s : RuntimeState} {op : RuntimeOp} {u : TaskId}
    (hu : u ≠ s.nextId)
    (hfresh : s.taskState s.nextId = none) :
    ((step s op).1).taskParent u = s.taskParent u := by
  match op with
  | .spawn _ | .schedule | .yield _ | .complete _ | .cancel _
  | .send _ _ _ | .receive _ | .inject _ _ | .sleep _ _ | .tick _ | .wake _ =>
      simp only [step]
      split <;> (try split) <;> (try split) <;> (try split) <;>
        (try split) <;> simp [upd, hu]
  | .spawnChild _ _ =>
      simp only [step]
      split <;> (try split) <;> (try split) <;> (try split) <;>
        simp [upd, hu]
  | .cancelTree _ => rfl

/-! ## Headline theorems -/

/-- In every reachable state, every parent has a strictly smaller id
    than its child.  Follows directly from `WellFormed.parent_lt`. -/
theorem reachable_parent_lt (ops : List RuntimeOp)
    {t p : TaskId}
    (h : (run RuntimeState.init ops).taskParent t = some p) :
    p < t :=
  (reachable_wf ops).parent_lt t p h

/-- In every reachable state, every owned task is spawned. (RFC 038) -/
theorem reachable_owner_spawned (ops : List RuntimeOp)
    {t : TaskId} {a : ActorId}
    (h : (run RuntimeState.init ops).taskOwner t = some a) :
    ∃ st, (run RuntimeState.init ops).taskState t = some st :=
  (reachable_wf ops).owner_spawned t a h

/-- In every reachable state, every task with a parent is itself spawned. (RFC 038) -/
theorem reachable_parent_child_spawned (ops : List RuntimeOp)
    {t p : TaskId}
    (h : (run RuntimeState.init ops).taskParent t = some p) :
    ∃ st, (run RuntimeState.init ops).taskState t = some st :=
  (reachable_wf ops).parent_child_spawned t p h

/-! ## Ancestor chain and termination -/

/-- Walk the parent chain at most `fuel` steps; returns the ancestor reached
    or `none` if the chain has length > `fuel`. -/
def ancestor (s : RuntimeState) : TaskId → Nat → Option TaskId
  | t, 0      => some t
  | t, fuel+1 =>
      match s.taskParent t with
      | none   => some t          -- root reached
      | some p => ancestor s p fuel

/-- A chain of length `t+1` always reaches a root.  The fuel `t` is
    sufficient because `parent_lt` guarantees the chain strictly
    decreases, so it terminates in at most `t` steps. -/
-- Helper: once a root is found, more fuel returns the same root.
-- Requires the reached node r to be a root (no parent).
private theorem ancestor_mono (s : RuntimeState) (r : TaskId) (hr : s.taskParent r = none) :
    ∀ (t : TaskId) (f₁ f₂ : Nat),
      f₁ ≤ f₂ → ancestor s t f₁ = some r → ancestor s t f₂ = some r := by
  intro t f₁
  induction f₁ generalizing t with
  | zero =>
    intro f₂ _ h
    simp only [ancestor] at h
    have htr : t = r := Option.some.inj h; subst htr
    cases f₂ with
    | zero => simp [ancestor]
    | succ n => simp [ancestor, hr]
  | succ k ihk =>
    intro f₂ hle h
    simp only [ancestor] at h
    cases hpt : s.taskParent t with
    | none =>
      simp only [hpt] at h
      have htr : t = r := Option.some.inj h; subst htr
      cases f₂ with
      | zero => exact absurd hle (Nat.not_succ_le_zero _)
      | succ n => simp [ancestor, hr]
    | some p =>
      simp only [hpt] at h
      cases f₂ with
      | zero => exact absurd hle (Nat.not_succ_le_zero _)
      | succ n =>
        simp only [ancestor, hpt]
        exact ihk p n (Nat.le_of_succ_le_succ hle) h

theorem parent_chain_terminates (ops : List RuntimeOp) (t : TaskId) :
    ∃ r, ancestor (run RuntimeState.init ops) t (t + 1) = some r ∧
         (run RuntimeState.init ops).taskParent r = none := by
  induction t using Nat.strongRecOn with
  | _ t ih =>
  simp only [ancestor]
  cases hp : (run RuntimeState.init ops).taskParent t with
  | none => exact ⟨t, rfl, hp⟩
  | some p =>
    have hlt : p < t := reachable_parent_lt ops hp
    obtain ⟨r, hr1, hr2⟩ := ih p hlt
    -- Fuel needed: ancestor s p t, have ancestor s p (p+1); p+1 ≤ t from hlt
    exact ⟨r, ancestor_mono _ r hr2 p (p + 1) t hlt hr1, hr2⟩

end Henret
