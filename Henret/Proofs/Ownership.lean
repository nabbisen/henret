import Henret.Proofs.Lifecycle
import Henret.Proofs.StepProjections

namespace Henret

/-! ## Wake helpers preserve definedness -/

/-- `wakeOne` maps `some` to `some`: waking never un-spawns a task. -/
theorem wakeOne_isSome {ts : TaskMap} {u : TaskId} {st : TaskState}
    (h : ts u = some st) (t : TaskId) :
    ∃ st', wakeOne ts t u = some st' := by
  by_cases hu : u = t
  · subst hu
    unfold wakeOne
    rw [h]
    cases st <;> simp_all [upd]
  · unfold wakeOne
    cases hts : ts t with
    | none => exact ⟨st, h⟩
    | some s' => cases s' <;> simp_all [upd, hu]

/-- `wakeMany` maps `some` to `some`. -/
theorem wakeMany_isSome {u : TaskId} :
    ∀ {l : List TaskId} {ts : TaskMap} {st : TaskState},
      ts u = some st → ∃ st', wakeMany ts l u = some st' := by
  intro l
  induction l with
  | nil => intro ts st h; exact ⟨st, h⟩
  | cons t r ih =>
    intro ts st h
    obtain ⟨st1, h1⟩ := wakeOne_isSome h t
    exact ih h1

/-- `wakeOne` maps `none` to `none`: waking never spawns a task. -/
theorem wakeOne_none {ts : TaskMap} {u : TaskId} (h : ts u = none)
    (t : TaskId) : wakeOne ts t u = none := by
  unfold wakeOne
  cases hts : ts t with
  | none => exact h
  | some s' =>
    cases s' with
    | sleeping =>
      have hu : u ≠ t := fun he => by rw [he, hts] at h; cases h
      simp [upd, hu]
      exact h
    | new => exact h
    | ready => exact h
    | running => exact h
    | yielded => exact h
    | completed => exact h
    | cancelled => exact h

/-- `wakeMany` maps `none` to `none`. -/
theorem wakeMany_none {u : TaskId} :
    ∀ {l : List TaskId} {ts : TaskMap}, ts u = none →
      wakeMany ts l u = none := by
  intro l
  induction l with
  | nil => intro ts h; exact h
  | cons t r ih => intro ts h; exact ih (wakeOne_none h t)

/-! ## Once spawned, always spawned -/

/-- No operation maps a spawned task's state back to `none`. -/
theorem step_preserves_spawned {s : RuntimeState} {u : TaskId} {st : TaskState}
    (h : s.taskState u = some st) (op : RuntimeOp) :
    ∃ st', ((step s op).1).taskState u = some st' := by
  cases op with
  | spawn a =>
    cases hts : s.taskState s.nextId with
    | some _ => exact ⟨st, by simp [step, hts, h]⟩
    | none =>
      by_cases hu : u = s.nextId
      · subst hu; rw [h] at hts; cases hts
      · exact ⟨st, by simp [step, hts, upd, hu, h]⟩
  | schedule =>
    cases hr : s.running with
    | some _ => exact ⟨st, by simp [step, hr, h]⟩
    | none =>
      cases hq : s.readyQ with
      | nil => exact ⟨st, by simp [step, hr, hq, h]⟩
      | cons t q =>
        by_cases hrun : (s.taskState t).any TaskState.isRunnable = true
        · by_cases hu : u = t
          · subst hu; exact ⟨.running, by simp [step, hr, hq, hrun, upd]⟩
          · exact ⟨st, by simp [step, hr, hq, hrun, upd, hu, h]⟩
        · simp at hrun; exact ⟨st, by simp [step, hr, hq, hrun, h]⟩
  | yield t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => exact ⟨st, by simp [step, hrt, hts, h]⟩
      | some s' =>
        by_cases hu : u = t
        · subst hu
          cases s' <;> simp [step, hrt, hts, upd, h]
        · cases s' <;> exact ⟨st, by simp [step, hrt, hts, upd, hu, h]⟩
    · exact ⟨st, by simp [step, hrt, h]⟩
  | complete t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => exact ⟨st, by simp [step, hrt, hts, h]⟩
      | some s' =>
        by_cases hu : u = t
        · subst hu
          cases s' <;> simp [step, hrt, hts, upd, h]
        · cases s' <;> exact ⟨st, by simp [step, hrt, hts, upd, hu, h]⟩
    · exact ⟨st, by simp [step, hrt, h]⟩
  | cancel t =>
    cases hts : s.taskState t with
    | none => exact ⟨st, by simp [step, hts, h]⟩
    | some s' =>
      by_cases hterm : s'.isTerminal = true
      · exact ⟨st, by simp [step, hts, hterm, h]⟩
      · simp at hterm
        by_cases hu : u = t
        · subst hu; exact ⟨.cancelled, by simp [step, hts, hterm, upd]⟩
        · exact ⟨st, by simp [step, hts, hterm, upd, hu, h]⟩
  | send t' b m => exact ⟨st, by simp [h]⟩
  | receive t' => exact ⟨st, by simp [h]⟩
  | inject a m => exact ⟨st, by simp [h]⟩
  | sleep t d =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => exact ⟨st, by simp [step, hrt, hts, h]⟩
      | some s' =>
        by_cases hu : u = t
        · subst hu
          cases s' <;> simp [step, hrt, hts, upd, h]
        · cases s' <;> exact ⟨st, by simp [step, hrt, hts, upd, hu, h]⟩
    · exact ⟨st, by simp [step, hrt, h]⟩
  | tick t =>
    by_cases hle : s.now ≤ t
    · obtain ⟨st', h'⟩ := wakeMany_isSome (l :=
        ((Timer.expired s.timers t).map TimerEntry.task).filter
          (fun u => s.taskState u = some .sleeping)) h
      exact ⟨st', by simp only [step, if_pos hle]; exact h'⟩
    · exact ⟨st, by simp [step, hle, h]⟩
  | wake t =>
    cases hts : s.taskState t with
    | none => exact ⟨st, by simp [step, hts, h]⟩
    | some s' =>
      by_cases hu : u = t
      · subst hu
        cases s' <;> simp [step, hts, upd, h]
      · cases s' <;> exact ⟨st, by simp [step, hts, upd, hu, h]⟩

/-! ## Ownership (RFC 014) -/

/-- Spawn assigns the fresh task to the spawning actor. -/
theorem spawn_sets_owner {s : RuntimeState} {a : ActorId}
    (h : s.taskState s.nextId = none) :
    ((step s (.spawn a)).1).taskOwner s.nextId = some a := by
  simp [step, h, upd]

/-- A spawned task's owner is immutable: no operation changes it.
The `hspawned` hypothesis rules out the one write site (`spawn` only
writes `taskOwner` at a fresh id, whose state is `none`). -/
theorem step_preserves_owner {s : RuntimeState} {u : TaskId} {o : ActorId}
    (hown : s.taskOwner u = some o) {st : TaskState}
    (hspawned : s.taskState u = some st) (op : RuntimeOp) :
    ((step s op).1).taskOwner u = some o := by
  cases op with
  | spawn a =>
    cases hts : s.taskState s.nextId with
    | some _ => simp [step, hts, hown]
    | none =>
      have hu : u ≠ s.nextId := by
        intro he; rw [he, hts] at hspawned; cases hspawned
      simp [step, hts, upd, hu, hown]
  | schedule =>
    cases hr : s.running with
    | some _ => simp [step, hr, hown]
    | none =>
      cases hq : s.readyQ with
      | nil => simp [step, hr, hq, hown]
      | cons t q =>
        by_cases hrun : (s.taskState t).any TaskState.isRunnable = true
        · simp [step, hr, hq, hrun, hown]
        · simp at hrun; simp [step, hr, hq, hrun, hown]
  | yield t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts, hown]
      | some s' => cases s' <;> simp [step, hrt, hts, hown]
    · simp [step, hrt, hown]
  | complete t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts, hown]
      | some s' => cases s' <;> simp [step, hrt, hts, hown]
    · simp [step, hrt, hown]
  | cancel t =>
    cases hts : s.taskState t with
    | none => simp [step, hts, hown]
    | some s' =>
      by_cases hterm : s'.isTerminal = true
      · simp [step, hts, hterm, hown]
      · simp at hterm; simp [step, hts, hterm, hown]
  | send t' b m => simp [hown]
  | receive t' => simp [hown]
  | inject a m => simp [hown]
  | sleep t d =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [step, hrt, hts, hown]
      | some s' => cases s' <;> simp [step, hrt, hts, hown]
    · simp [step, hrt, hown]
  | tick t =>
    by_cases hle : s.now ≤ t <;> simp [step, hle, hown]
  | wake t =>
    cases hts : s.taskState t with
    | none => simp [step, hts, hown]
    | some s' => cases s' <;> simp [step, hts, hown]

/-- Whole-program corollary: a task keeps its owning actor across any
program (RFC 014 acceptance: ownership is explicit and stable). -/
theorem run_preserves_owner {u : TaskId} {o : ActorId} :
    ∀ {s : RuntimeState} {st : TaskState}, s.taskOwner u = some o →
      s.taskState u = some st →
      ∀ ops : List RuntimeOp, (run s ops).taskOwner u = some o := by
  intro s st hown hspawned ops
  induction ops generalizing s st with
  | nil => exact hown
  | cons op rest ih =>
    obtain ⟨st', h'⟩ := step_preserves_spawned hspawned op
    exact ih (step_preserves_owner hown hspawned op) h'

end Henret

/-!
# Henret.Proofs.Ownership

Actor-ownership theorems (RFC 014).

* `spawn_sets_owner` — `spawn a` records actor `a` as the owner of the
  fresh task.
* `step_preserves_owner` / `run_preserves_owner` — a spawned task's
  owner never changes, across any single operation or whole program.
* `step_preserves_spawned` — no operation un-spawns a task (`some`
  states never return to `none`), which is what makes the ownership
  preservation inductive.
-/
