import Henret.Scheduler.Model

/-!
# Henret.Proofs.StepProjections

The three messaging operations — `send`, `receive`, `inject` — mutate
only `mailboxes`. This module proves that once, per projection, as
`@[simp]` lemmas, so every downstream case-analysis proof (terminal
preservation, clock monotonicity, well-formedness, ...) discharges its
messaging cases with a one-line `simp` instead of re-walking the guard
tree.
-/

namespace Henret

section SendProjections
variable (s : RuntimeState) (t : TaskId) (b : ActorId) (m : Message)

@[simp] theorem send_taskState :
    ((step s (.send t b m)).1).taskState = s.taskState := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem send_taskOwner :
    ((step s (.send t b m)).1).taskOwner = s.taskOwner := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem send_readyQ :
    ((step s (.send t b m)).1).readyQ = s.readyQ := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem send_running :
    ((step s (.send t b m)).1).running = s.running := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem send_timers :
    ((step s (.send t b m)).1).timers = s.timers := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem send_now :
    ((step s (.send t b m)).1).now = s.now := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem send_nextId :
    ((step s (.send t b m)).1).nextId = s.nextId := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> rfl
  · rfl

end SendProjections

section ReceiveProjections
variable (s : RuntimeState) (t : TaskId)

@[simp] theorem receive_taskState :
    ((step s (.receive t)).1).taskState = s.taskState := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem receive_taskOwner :
    ((step s (.receive t)).1).taskOwner = s.taskOwner := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem receive_readyQ :
    ((step s (.receive t)).1).readyQ = s.readyQ := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem receive_running :
    ((step s (.receive t)).1).running = s.running := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem receive_timers :
    ((step s (.receive t)).1).timers = s.timers := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem receive_now :
    ((step s (.receive t)).1).now = s.now := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> (try split) <;> rfl
  · rfl

@[simp] theorem receive_nextId :
    ((step s (.receive t)).1).nextId = s.nextId := by
  simp only [step]
  split
  · split <;> (try split) <;> (try split) <;> (try split) <;> rfl
  · rfl

end ReceiveProjections

section InjectProjections
variable (s : RuntimeState) (a : ActorId) (m : Message)

@[simp] theorem inject_taskState :
    ((step s (.inject a m)).1).taskState = s.taskState := by
  simp only [step]; split <;> rfl

@[simp] theorem inject_taskOwner :
    ((step s (.inject a m)).1).taskOwner = s.taskOwner := by
  simp only [step]; split <;> rfl

@[simp] theorem inject_readyQ :
    ((step s (.inject a m)).1).readyQ = s.readyQ := by
  simp only [step]; split <;> rfl

@[simp] theorem inject_running :
    ((step s (.inject a m)).1).running = s.running := by
  simp only [step]; split <;> rfl

@[simp] theorem inject_timers :
    ((step s (.inject a m)).1).timers = s.timers := by
  simp only [step]; split <;> rfl

@[simp] theorem inject_now :
    ((step s (.inject a m)).1).now = s.now := by
  simp only [step]; split <;> rfl

@[simp] theorem inject_nextId :
    ((step s (.inject a m)).1).nextId = s.nextId := by
  simp only [step]; split <;> rfl

end InjectProjections

end Henret
