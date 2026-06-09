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
  /-- Owning actor per task id; set at spawn, immutable thereafter
      (RFC 014). `none` = never spawned. -/
  taskOwner : TaskId → Option ActorId
  /-- FIFO queue of runnable task ids. -/
  readyQ    : List TaskId
  /-- The task currently selected by the scheduler, if any. -/
  running   : Option TaskId
  /-- Pending timers, sorted by deadline. -/
  timers    : List TimerEntry
  /-- Mailbox per actor id; `none` = actor does not exist. -/
  mailboxes      : ActorMap
  /-- FIFO wait queue per actor: tasks waiting to receive from that
      actor's mailbox (RFC 031). -/
  mailboxWaiters : ActorId → List TaskId
  /-- Current logical time; advanced only by `tick`, monotonically
      (RFC 015). -/
  now           : Nat
  /-- Parent map: `taskParent t = some p` means task `t` was created
      by running task `p` via `spawnChild`. `none` means root or
      unspawned. Written exactly once, at creation (RFC 032). -/
  taskParent : TaskId → Option TaskId
  /-- Fresh task-id counter; ids below it may exist, ids at or above
      it are unused. -/
  nextId    : TaskId
  /-- Fresh message occurrence-id counter; every delivered envelope
      receives the current value and the counter is bumped.
      Analogue of `nextId` for occurrence uniqueness (RFC 033). -/
  nextMsgId : MessageId

namespace RuntimeState

/-- The initial state: nothing spawned, no actors, time zero. -/
def init : RuntimeState where
  taskState      := fun _ => none
  taskOwner      := fun _ => none
  readyQ         := []
  running        := none
  timers         := []
  mailboxes      := fun _ => none
  mailboxWaiters := fun _ => []
  taskParent     := fun _ => none
  now            := 0
  nextId         := 0
  nextMsgId      := 0

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
          taskOwner := upd s.taskOwner t (some a)
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
        -- For waiting tasks, also remove from owner's waiter list (RFC 031)
        let ownerWaitersUpdate : ActorId → List TaskId :=
          match s.taskOwner t with
          | some a => fun ac => if ac = a then (s.mailboxWaiters a).filter (· ≠ t)
                                else s.mailboxWaiters ac
          | none   => s.mailboxWaiters
        ({ s with
            taskState      := upd s.taskState t (some .cancelled)
            readyQ         := s.readyQ.filter (fun u => u ≠ t)
            timers         := s.timers.filter (fun e => e.task ≠ t)
            running        := if s.running = some t then none else s.running
            mailboxWaiters := ownerWaitersUpdate }, .ok)
    | none => (s, .invalid)
  | .send t b m =>
    if s.running = some t then
      match s.taskState t with
      | some .running =>
        match s.taskOwner t with
        | some _ =>
          match s.mailboxes b with
          | some mb =>
            -- Stamp envelope with occurrence id and sender's actor; wake head waiter of b if any (RFC 033).
            let env : Envelope := ⟨s.nextMsgId, s.taskOwner t, m⟩
            let s' := { s with
                          mailboxes := upd s.mailboxes b (some (mb.enqueue env))
                          nextMsgId := s.nextMsgId + 1 }
            match s.mailboxWaiters b with
            | []      => (s', .ok)
            | w :: ws =>
              ({ s' with
                   taskState      := upd s'.taskState w (some .ready)
                   readyQ         := s'.readyQ ++ [w]
                   mailboxWaiters := fun ac =>
                     if ac = b then ws else s'.mailboxWaiters ac },
               .ok)
          | none => (s, .invalid)
        | none => (s, .invalid)
      | _ => (s, .invalid)
    else (s, .invalid)
  | .receive t =>
    if s.running = some t then
      match s.taskState t with
      | some .running =>
        match s.taskOwner t with
        | some a =>
          match s.mailboxes a with
          | some mb =>
            match mb.dequeue with
            | some (env, mb') =>
              ({ s with mailboxes := upd s.mailboxes a (some mb') }, .received env)
            | none =>
              -- Park: task waits on actor a's mailbox (RFC 031).
              ({ s with
                   taskState      := upd s.taskState t (some .waiting)
                   running        := none
                   mailboxWaiters := fun ac =>
                     if ac = a then s.mailboxWaiters a ++ [t]
                     else s.mailboxWaiters ac },
               .blocked)
          | none => (s, .invalid)
        | none => (s, .invalid)
      | _ => (s, .invalid)
    else (s, .invalid)
  | .inject a m =>
    match s.mailboxes a with
    | some mb =>
      -- Stamp envelope with occurrence id and none source (environment); wake head waiter if any (RFC 033).
      let env : Envelope := ⟨s.nextMsgId, none, m⟩
      let s' := { s with
                    mailboxes := upd s.mailboxes a (some (mb.enqueue env))
                    nextMsgId := s.nextMsgId + 1 }
      match s.mailboxWaiters a with
      | []      => (s', .ok)
      | w :: ws =>
        ({ s' with
             taskState      := upd s'.taskState w (some .ready)
             readyQ         := s'.readyQ ++ [w]
             mailboxWaiters := fun ac => if ac = a then ws else s'.mailboxWaiters ac },
         .ok)
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
  | .tick t =>
    if s.now ≤ t then
      let woken := ((Timer.expired s.timers t).map TimerEntry.task).filter
        (fun u => s.taskState u = some .sleeping)
      ({ s with
          taskState := wakeMany s.taskState woken
          readyQ    := s.readyQ ++ woken
          timers    := Timer.remaining s.timers t
          now       := t }, .woke woken)
    else (s, .invalid)
  | .spawnChild t a =>
    if s.running = some t then
      match s.taskState t with
      | some .running =>
        match s.taskOwner t with
        | some _ =>
          let n := s.nextId
          match s.taskState n with
          | none =>
            let mbs := match s.mailboxes a with
              | some _ => s.mailboxes
              | none   => upd s.mailboxes a (some Mailbox.empty)
            ({ s with
                taskState  := upd s.taskState n (some .new)
                taskOwner  := upd s.taskOwner n (some a)
                taskParent := upd s.taskParent n (some t)
                readyQ     := s.readyQ ++ [n]
                mailboxes  := mbs
                nextId     := n + 1 }, .spawned n)
          | some _ => (s, .invalid)
        | none => (s, .invalid)
      | _ => (s, .invalid)
    else (s, .invalid)
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
