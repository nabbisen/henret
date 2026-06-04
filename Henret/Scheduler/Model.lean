import Henret.Core.Id
import Henret.Core.Result
import Henret.Actor.Task
import Henret.Actor.Mailbox
import Henret.Scheduler.Op
import Henret.Scheduler.Timer

namespace Henret

/-- Complete state of the modeled runtime. -/
structure RuntimeState where
  /-- Lifecycle state per task id; `none` = never spawned. -/
  taskState : TaskMap
  /-- FIFO queue of runnable task ids. -/
  readyQ    : List TaskId
  /-- The task currently selected by the scheduler, if any. -/
  running   : Option TaskId
  /-- Pending timers, sorted by deadline. -/
  timers    : List TimerEntry
  /-- Mailbox per actor id; `none` = actor does not exist. -/
  mailboxes : ActorMap
  /-- Fresh task-id counter; ids below it may exist, ids at or above
      it are unused. -/
  nextId    : TaskId

namespace RuntimeState

/-- The initial state: nothing spawned, no actors, time empty. -/
def init : RuntimeState where
  taskState := fun _ => none
  readyQ    := []
  running   := none
  timers    := []
  mailboxes := fun _ => none
  nextId    := 0

end RuntimeState

/-- Wake one task: `sleeping → ready`; anything else is untouched.
The guard makes timer wake-ups harmless against stale entries and
keeps terminal-state monotonicity local. -/
def wakeOne (ts : TaskMap) (t : TaskId) : TaskMap :=
  match ts t with
  | some .sleeping => upd ts t (some .ready)
  | _ => ts

/-- Wake a list of tasks in order. -/
def wakeMany (ts : TaskMap) : List TaskId → TaskMap
  | []      => ts
  | t :: r  => wakeMany (wakeOne ts t) r

/-- One transition of the model. Total and executable. -/
def step (s : RuntimeState) : RuntimeOp → RuntimeState × StepResult
  | .spawn a =>
    let t := s.nextId
    match s.taskState t with
    | none =>
      let mbs := match s.mailboxes a with
        | some _ => s.mailboxes
        | none   => upd s.mailboxes a (some Mailbox.empty)
      ({ s with
          taskState := upd s.taskState t (some .new)
          readyQ    := s.readyQ ++ [t]
          mailboxes := mbs
          nextId    := t + 1 }, .spawned t)
    | some _ => (s, .invalid)
  | .schedule =>
    match s.running, s.readyQ with
    | none, t :: q =>
      if (s.taskState t).any TaskState.isRunnable then
        ({ s with
            taskState := upd s.taskState t (some .running)
            readyQ    := q
            running   := some t }, .scheduled t)
      else (s, .invalid)
    | _, _ => (s, .invalid)
  | .yield t =>
    if s.running = some t then
      match s.taskState t with
      | some .running =>
        ({ s with
            taskState := upd s.taskState t (some .yielded)
            readyQ    := s.readyQ ++ [t]
            running   := none }, .ok)
      | _ => (s, .invalid)
    else (s, .invalid)
  | .complete t =>
    if s.running = some t then
      match s.taskState t with
      | some .running =>
        ({ s with
            taskState := upd s.taskState t (some .completed)
            running   := none }, .ok)
      | _ => (s, .invalid)
    else (s, .invalid)
  | .cancel t =>
    match s.taskState t with
    | some st =>
      if st.isTerminal then (s, .invalid)
      else
        ({ s with
            taskState := upd s.taskState t (some .cancelled)
            readyQ    := s.readyQ.filter (fun u => u ≠ t)
            timers    := s.timers.filter (fun e => e.task ≠ t)
            running   := if s.running = some t then none else s.running }, .ok)
    | none => (s, .invalid)
  | .send a m =>
    match s.mailboxes a with
    | some mb =>
      ({ s with mailboxes := upd s.mailboxes a (some (mb.enqueue m)) }, .ok)
    | none => (s, .invalid)
  | .receive a =>
    match s.mailboxes a with
    | some mb =>
      match mb.dequeue with
      | some (m, mb') =>
        ({ s with mailboxes := upd s.mailboxes a (some mb') }, .received m)
      | none => (s, .invalid)
    | none => (s, .invalid)
  | .sleep t deadline =>
    if s.running = some t then
      match s.taskState t with
      | some .running =>
        ({ s with
            taskState := upd s.taskState t (some .sleeping)
            running   := none
            timers    := Timer.insertSorted ⟨deadline, t⟩ s.timers }, .ok)
      | _ => (s, .invalid)
    else (s, .invalid)
  | .tick now =>
    let woken := (Timer.expired s.timers now).map TimerEntry.task
    ({ s with
        taskState := wakeMany s.taskState woken
        readyQ    := s.readyQ ++ woken
        timers    := Timer.remaining s.timers now }, .woke woken)
  | .wake t =>
    match s.taskState t with
    | some .sleeping =>
      ({ s with
          taskState := upd s.taskState t (some .ready)
          readyQ    := s.readyQ ++ [t]
          timers    := s.timers.filter (fun e => e.task ≠ t) }, .ok)
    | _ => (s, .invalid)

/-- Run a list of operations, ignoring results (RFC 005). Invalid
operations are no-ops by construction of `step`. -/
def run (s : RuntimeState) : List RuntimeOp → RuntimeState
  | []        => s
  | op :: ops => run (step s op).1 ops

/-- Run a list of operations, collecting every result. -/
def runTrace (s : RuntimeState) : List RuntimeOp → RuntimeState × List StepResult
  | []        => (s, [])
  | op :: ops =>
    let (s', r) := step s op
    let (s'', rs) := runTrace s' ops
    (s'', r :: rs)

@[simp] theorem run_nil (s : RuntimeState) : run s [] = s := rfl

@[simp] theorem run_cons (s : RuntimeState) (op : RuntimeOp)
    (ops : List RuntimeOp) : run s (op :: ops) = run (step s op).1 ops := rfl

end Henret

/-!
# Henret.Scheduler.Model

Runtime state and the executable transition function (RFC 004, 005).

`step` gives every operation explicit pre/post behavior. Invalid
operations return the state **unchanged** together with
`StepResult.invalid` (RFC 005, invalid-operation option 1).

Ownership locations (RFC 004): a task's lifecycle state lives only in
`taskState`; a queued task id lives in `readyQ`; the running task id
lives in `running`; a sleeping task's wake-up lives in `timers`; a
message lives in exactly one mailbox in `mailboxes`. Every mutation of
a per-id map goes through `upd`, so preservation lemmas are uniform.
-/
