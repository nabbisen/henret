import Henret.Scheduler.Model

namespace Henret

/-- Complete one task if it is runnable; otherwise leave it alone. -/
def completeOne (ts : TaskMap) (t : TaskId) : TaskMap :=
  match ts t with
  | some .new | some .ready | some .yielded => upd ts t (some .completed)
  | _ => ts

/-- Complete every task in the list, in order. -/
def completeAll (ts : TaskMap) : List TaskId → TaskMap
  | []      => ts
  | t :: r  => completeAll (completeOne ts t) r

/-- The drain driver: complete every queued runnable task, empty the
queue. -/
def drain (s : RuntimeState) : RuntimeState :=
  { s with taskState := completeAll s.taskState s.readyQ, readyQ := [] }

@[simp] theorem drain_empties (s : RuntimeState) :
    (drain s).readyQ = [] := rfl

/-- States from which `completeOne` can move a task, plus the target
state itself — the set is closed under `completeOne`. -/
def Drainable (st : TaskState) : Prop :=
  st = .new ∨ st = .ready ∨ st = .yielded ∨ st = .completed

theorem completeOne_completed {ts : TaskMap} {t : TaskId}
    (h : ts t = some .completed) (u : TaskId) :
    completeOne ts u t = some .completed := by
  by_cases hu : t = u
  · subst hu
    simp [completeOne, h]
  · unfold completeOne
    cases hts : ts u with
    | none => exact h
    | some s' => cases s' <;> simp [upd, hu, h]

theorem completeAll_preserves_completed {t : TaskId} :
    ∀ {l : List TaskId} {ts : TaskMap}, ts t = some .completed →
      completeAll ts l t = some .completed := by
  intro l
  induction l with
  | nil => intro ts h; exact h
  | cons u r ih =>
    intro ts h
    exact ih (completeOne_completed h u)

theorem completeOne_drainable {ts : TaskMap} {t : TaskId}
    {st : TaskState} (h : ts t = some st) (hd : Drainable st)
    (u : TaskId) :
    ∃ st', completeOne ts u t = some st' ∧ Drainable st' := by
  by_cases hu : t = u
  · subst hu
    refine ⟨.completed, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
    rcases hd with rfl | rfl | rfl | rfl <;> simp [completeOne, h, upd]
  · refine ⟨st, ?_, hd⟩
    unfold completeOne
    cases hts : ts u with
    | none => exact h
    | some s' => cases s' <;> simp [upd, hu, h]

theorem completeAll_completes {t : TaskId} :
    ∀ {l : List TaskId} {ts : TaskMap} {st : TaskState},
      t ∈ l → ts t = some st → Drainable st →
      completeAll ts l t = some .completed := by
  intro l
  induction l with
  | nil => intro ts st hmem _ _; cases hmem
  | cons u r ih =>
    intro ts st hmem hst hd
    by_cases hu : t = u
    · subst hu
      have hc : completeOne ts t t = some .completed := by
        unfold completeOne
        rcases hd with rfl | rfl | rfl | rfl <;> simp [hst, upd]
      show completeAll (completeOne ts t) r t = some .completed
      exact completeAll_preserves_completed hc
    · cases hmem with
      | head => exact absurd rfl hu
      | tail _ hr =>
        obtain ⟨st', hst', hd'⟩ := completeOne_drainable hst hd u
        exact ih hr hst' hd'

/-- Model-level liveness: the drain driver completes every queued
runnable (or already completed) task. -/
theorem drain_completes {s : RuntimeState} {t : TaskId}
    {st : TaskState} (hmem : t ∈ s.readyQ)
    (hst : s.taskState t = some st) (hd : Drainable st) :
    (drain s).taskState t = some .completed :=
  completeAll_completes hmem hst hd

/-- Op-level round-robin driver: schedule the head, complete it,
repeat while fuel lasts. Used by the demo; behavior is TESTED. -/
def driveOps : Nat → RuntimeState → RuntimeState
  | 0, s => s
  | fuel + 1, s =>
    match s.readyQ with
    | [] => s
    | t :: _ =>
      let s1 := (step s .schedule).1
      let s2 := (step s1 (.complete t)).1
      driveOps fuel s2

end Henret

/-!
# Henret.Scheduler.Driver

Reference driver and model-level liveness (RFC 005, Stage 5).

`drain` is the simplest fair driver: it walks the ready queue once,
completing every runnable task. The liveness theorem `drain_completes`
states that every queued runnable task is completed afterwards, and
`drain_empties` that the queue is empty — "a fair fueled driver
completes all ready fueled tasks" at the model level.

`driveOps` is the op-level round-robin driver used by the demo
executable; its behavior is exercised by the executable test stage
(TESTED, not separately proven — see the proof/trust/test matrix).
-/
