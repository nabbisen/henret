import Henret.Scheduler.Model

/-!
# Henret.Proofs.StepProjections

Projections of `step` onto the fields that messaging operations leave
**unconditionally unchanged**.

After RFC 031, `send` and `inject` may touch `taskState` and `readyQ`
(wake-one semantics: a head waiter is readied on delivery).  `receive`
may touch `taskState`, `running`, and `mailboxWaiters` (parking
semantics: empty-own-mailbox parks the task).  The lemmas below cover
only the fields that remain invariant in **every** branch.

Fields provably unchanged per operation (RFC 034 modularisation note):
- `send`:    `taskOwner`, `running`, `timers`, `now`, `nextId`
- `inject`:  `taskOwner`, `running`, `timers`, `now`, `nextId`
- `receive`: `taskOwner`, `readyQ`, `timers`, `now`, `nextId`
-/

namespace Henret

section SendProjections
variable (s : RuntimeState) (t : TaskId) (b : ActorId) (m : Message)

@[simp] theorem send_taskOwner :
    ((step s (.send t b m)).1).taskOwner = s.taskOwner := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

@[simp] theorem send_running :
    ((step s (.send t b m)).1).running = s.running := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

@[simp] theorem send_timers :
    ((step s (.send t b m)).1).timers = s.timers := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

@[simp] theorem send_now :
    ((step s (.send t b m)).1).now = s.now := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

@[simp] theorem send_nextId :
    ((step s (.send t b m)).1).nextId = s.nextId := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

end SendProjections

section ReceiveProjections
variable (s : RuntimeState) (t : TaskId)

@[simp] theorem receive_taskOwner :
    ((step s (.receive t)).1).taskOwner = s.taskOwner := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

@[simp] theorem receive_readyQ :
    ((step s (.receive t)).1).readyQ = s.readyQ := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

@[simp] theorem receive_timers :
    ((step s (.receive t)).1).timers = s.timers := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

@[simp] theorem receive_now :
    ((step s (.receive t)).1).now = s.now := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

@[simp] theorem receive_nextId :
    ((step s (.receive t)).1).nextId = s.nextId := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

end ReceiveProjections

section InjectProjections
variable (s : RuntimeState) (a : ActorId) (m : Message)

@[simp] theorem inject_taskOwner :
    ((step s (.inject a m)).1).taskOwner = s.taskOwner := by
  simp only [step]; split <;> (try split) <;> rfl

@[simp] theorem inject_running :
    ((step s (.inject a m)).1).running = s.running := by
  simp only [step]; split <;> (try split) <;> rfl

@[simp] theorem inject_timers :
    ((step s (.inject a m)).1).timers = s.timers := by
  simp only [step]; split <;> (try split) <;> rfl

@[simp] theorem inject_now :
    ((step s (.inject a m)).1).now = s.now := by
  simp only [step]; split <;> (try split) <;> rfl

@[simp] theorem inject_nextId :
    ((step s (.inject a m)).1).nextId = s.nextId := by
  simp only [step]; split <;> (try split) <;> rfl

end InjectProjections

end Henret
