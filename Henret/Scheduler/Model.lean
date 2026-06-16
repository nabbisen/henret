import Henret.Core.Id
import Henret.Core.Result
import Henret.Actor.Task
import Henret.Actor.Meta
import Henret.Actor.Mailbox
import Henret.Scheduler.Op
import Henret.Scheduler.Timer

namespace Henret

/-- Actor admission status (RFC 055). `active` accepts sends/injects;
    `closed` rejects new sends/injects to the actor but does **not**
    delete existing mailbox contents (they may still be drained by
    `receive`). (`open` is a Lean keyword, hence `active`.) -/
inductive ActorStatus where
  | active
  | closed
deriving DecidableEq, Repr, Inhabited

/-- Runtime admission status (RFC 055). `running` is normal; `shuttingDown`
    rejects new root `spawn`s and environment `inject`s; `stopped` is a quiescent
    terminal status reached via `stopWhenIdle` **or** `stopWhenDrained`.

    `stopped` alone does **not** certify the resource ledger is drained — a
    `stopWhenIdle` stop may leave resources live (RFC 092). A clean shutdown is
    `CleanStopped` (stopped ∧ `Frozen`), reached by `stopWhenDrained`. -/
inductive RuntimeStatus where
  | running
  | shuttingDown
  | stopped
deriving DecidableEq, Repr, Inhabited

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
  /-- FIFO timed-wait queue per actor: tasks waiting with a deadline
      (`receiveUntil`). Kept separate from `mailboxWaiters` so the
      `waiters_waiting` invariant is not disturbed (RFC 040). -/
  timedMailboxWaiters : ActorId → List TaskId
  /-- Deadline for each `.waitingTimed` task. `none` means not timed-waiting. -/
  waitDeadline : TaskId → Option Nat
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
  /-- Restart provenance: `restartOf new = some old` means task `new`
      was spawned by `restartOne` as the replacement for failed task
      `old`. `none` means `new` is not a restart replacement. Written
      exactly once, at `restartOne` time (RFC 049). -/
  restartOf : TaskId → Option TaskId
  /-- Per-actor admission status (RFC 055). `active` by default. -/
  actorStatus : ActorId → ActorStatus
  /-- Runtime admission status (RFC 055). `running` by default. -/
  runtimeStatus : RuntimeStatus
  /-- Per-actor mailbox policy (RFC 056). `unbounded` by default, so a state
      that configures no capacity behaves exactly as pre-RFC-056. -/
  mailboxPolicy : ActorId → MailboxPolicy
  /-- Resource ledger (RFC 057): `resources r = some ⟨t, st⟩` records that
      resource `r` is owned by task `t` and is in lifecycle state `st`.
      `none` = the id was never allocated. -/
  resources : ResourceId → Option ResourceRecord
  /-- Fresh-resource counter (RFC 057); monotone, never reused. -/
  nextResourceId : Nat
  /-- Optional per-task scheduling metadata (RFC 059): priority and logical
      deadline. `none` = task uses `defaultMeta`. Metadata is only ever
      attached to spawned tasks (`reachable_metadata_spawned`). -/
  taskMeta : TaskId → Option TaskMeta

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
  timedMailboxWaiters := fun _ => []
  waitDeadline        := fun _ => none
  taskParent     := fun _ => none
  now            := 0
  nextId         := 0
  nextMsgId      := 0
  restartOf      := fun _ => none
  actorStatus    := fun _ => .active
  runtimeStatus  := .running
  mailboxPolicy  := fun _ => .unbounded
  resources      := fun _ => none
  nextResourceId := 0
  taskMeta       := fun _ => none

/-- Decidable "the resource ledger is fully drained" check, bounded by
    `nextResourceId` (RFC 087): every allocated id is `released` (or `none`).
    Together with the `resource_fresh` invariant this captures the unbounded
    `Drained` predicate (`resourceDrained_drained`). -/
def resourceDrained (s : RuntimeState) : Bool :=
  (List.range s.nextResourceId).all fun r =>
    match s.resources r with
    | some rr => decide (rr.state = .released)
    | none    => true

/-- Is actor `b`'s mailbox `mb` at or over its configured capacity? (RFC 056)
    Always `false` for an unbounded policy. `send`/`inject` consult this only
    after every validity/admission guard, so a full mailbox yields
    `.backpressured` (a legal-but-no-progress result), never `.invalid`. -/
def mailboxFull (s : RuntimeState) (b : ActorId) (mb : Mailbox) : Bool :=
  match (s.mailboxPolicy b).capacity with
  | some n => decide (n ≤ mb.messages.length)
  | none   => false

/-! ### Resource ledger predicates (RFC 057)

The stable public predicate surface for the resource ledger — the fixed target
a future native-finalizer (FFI) layer reasons against. Precise names per the
RFC 057 review (§12): no `ResourceLive`/`ResourceClosed`, which are easy to
misread. -/

/-- Resource `r` is owned by task `t`. -/
def ResourceOwnedBy (s : RuntimeState) (r : ResourceId) (t : TaskId) : Prop :=
  ∃ rr, s.resources r = some rr ∧ rr.owner = .task t

/-- Resource `r` is live: allocated and usable by its owner. -/
def ResourceAllocated (s : RuntimeState) (r : ResourceId) : Prop :=
  ∃ rr, s.resources r = some rr ∧ rr.state = .allocated

/-- Resource `r` is closing: the owner can no longer release it; a
finalization obligation remains. -/
def ResourceClosing (s : RuntimeState) (r : ResourceId) : Prop :=
  ∃ rr, s.resources r = some rr ∧ rr.state = .closing

/-- Resource `r` is released: terminal ledger state; never live again. -/
def ResourceReleased (s : RuntimeState) (r : ResourceId) : Prop :=
  ∃ rr, s.resources r = some rr ∧ rr.state = .released

/-- Resource `r` still requires finalization — definitionally `ResourceClosing`
(RFC 057 review §6/§12). -/
def ResourcePendingFinalization (s : RuntimeState) (r : ResourceId) : Prop :=
  ResourceClosing s r

end RuntimeState

/-- The runtime is **quiescent**: no task is running, the ready queue is
    empty, and no timers are pending — the computable idle condition used
    by `stopWhenIdle` (RFC 055). Parked waiters with no sender are a
    deadlock, not active work, and do not block quiescence. -/
def RuntimeQuiescent (s : RuntimeState) : Prop :=
  s.running = none ∧ s.readyQ = [] ∧ s.timers = []

instance (s : RuntimeState) : Decidable (RuntimeQuiescent s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Wake one task: `sleeping → ready` or `waitingTimed → ready`; anything else is untouched.
The guard makes timer wake-ups harmless against stale entries and
keeps terminal-state monotonicity local. (RFC 040: extended to waitingTimed) -/
def wakeOne (ts : TaskMap) (t : TaskId) : TaskMap :=
  match ts t with
  | some .sleeping | some .waitingTimed => upd ts t (some .ready)
  | _ => ts

/-- Wake a list of tasks in order. -/
def wakeMany (ts : TaskMap) : List TaskId → TaskMap
  | []      => ts
  | t :: r  => wakeMany (wakeOne ts t) r

/-! ## Cascade cancel helpers (RFC 039) -/

/-- Check whether task `t` is `root` or has `root` as an ancestor by following
    the `taskParent` chain. Well-founded by strict decrease: the guard
    `hp : p < t` ensures each recursive step uses a strictly smaller id.
    For states where `taskParent` is not strictly decreasing (invalid states),
    returns `false` conservatively. -/
def isInSubtreeOf (s : RuntimeState) (root : TaskId) (t : TaskId) : Bool :=
  if t = root then true
  else match s.taskParent t with
  | none   => false
  | some p => if _hp : p < t then isInSubtreeOf s root p else false
termination_by t
decreasing_by exact _hp

/-- The set of tasks to cancel: tasks in `0..nextId-1` that are spawned and
    whose parent chain reaches `root` (including `root` itself). -/
def descendantsOf (s : RuntimeState) (root : TaskId) : List TaskId :=
  (List.range s.nextId).filter (fun t =>
    s.taskState t != none && isInSubtreeOf s root t)

/-- Apply one `cancelTree` step to the `RuntimeState`. Each component is
    defined directly in terms of the original state and the cancellation set,
    avoiding foldl for easier formal reasoning. -/
def applyCancelTree (s : RuntimeState) (toCancel : List TaskId) : RuntimeState :=
  { s with
    -- Cancelled: if t ∈ toCancel and non-terminal, set to .cancelled.
    -- If t ∈ toCancel but already terminal, leave unchanged (idempotent).
    -- If t ∉ toCancel, leave unchanged.
    taskState :=
      fun t =>
        if t ∈ toCancel then
          match s.taskState t with
          | none    => none
          | some st => if st.isTerminal then some st else some .cancelled
        else s.taskState t
    readyQ         := s.readyQ.filter (· ∉ toCancel)
    running        := if toCancel.any (fun t => s.running = some t) then none else s.running
    timers         := s.timers.filter (fun e => e.task ∉ toCancel)
    mailboxWaiters := fun a => (s.mailboxWaiters a).filter (· ∉ toCancel)
    timedMailboxWaiters := fun a => (s.timedMailboxWaiters a).filter (· ∉ toCancel)
    waitDeadline   := fun t => if t ∈ toCancel then none else s.waitDeadline t
    -- Every allocated resource owned by a cancelled task becomes closing (RFC 057).
    resources      := markClosingIf (· ∈ toCancel) s.resources }

/-- One transition of the model. Total and executable. -/
def step (s : RuntimeState) : RuntimeOp → RuntimeState × StepResult
  | .spawn a =>
    if s.runtimeStatus = .running then
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
    else (s, .invalid)
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
            running   := none
            resources := markClosingIf (· == t) s.resources }, .ok)
      | _ => (s, .invalid)
    else (s, .invalid)
  | .cancel t =>
    match s.taskState t with
    | some st =>
      if st.isTerminal then (s, .invalid)
      else
        -- For waiting/waitingTimed tasks, also remove from owner's waiter list (RFC 031/040)
        let ownerWaitersUpdate : ActorId → List TaskId :=
          match s.taskOwner t with
          | some a => fun ac => if ac = a then (s.mailboxWaiters a).filter (· ≠ t)
                                else s.mailboxWaiters ac
          | none   => s.mailboxWaiters
        let ownerTimedWaitersUpdate : ActorId → List TaskId :=
          fun ac => (s.timedMailboxWaiters ac).filter (· ≠ t)
        ({ s with
            taskState               := upd s.taskState t (some .cancelled)
            readyQ                  := s.readyQ.filter (fun u => u ≠ t)
            timers                  := s.timers.filter (fun e => e.task ≠ t)
            running                 := if s.running = some t then none else s.running
            mailboxWaiters          := ownerWaitersUpdate
            timedMailboxWaiters     := ownerTimedWaitersUpdate
            waitDeadline            := fun u => if u = t then none else s.waitDeadline u
            resources               := markClosingIf (· == t) s.resources }, .ok)
    | none => (s, .invalid)
  | .send t b m =>
    if s.actorStatus b = .closed then (s, .invalid)
    else if s.running = some t then
      match s.taskState t with
      | some .running =>
        match s.taskOwner t with
        | some _ =>
          match s.mailboxes b with
          | some mb =>
            -- RFC 056: a valid delivery to a full mailbox is backpressured (reject),
            -- not invalid. This guard follows every validity/admission check, so it is
            -- never an oracle for an unauthorized sender, and occurrence ids are
            -- allocated only on the successful-enqueue path below.
            if s.mailboxFull b mb then (s, .backpressured) else
            -- Stamp envelope with occurrence id and sender's actor; wake head waiter of b if any (RFC 033).
            let env : Envelope := ⟨s.nextMsgId, s.taskOwner t, m⟩
            let s' := { s with
                          mailboxes := upd s.mailboxes b (some (mb.enqueue env))
                          nextMsgId := s.nextMsgId + 1 }
            match s.mailboxWaiters b with
            | w :: ws =>
              -- Regular waiter takes priority. Unconditionally clear timer/deadline
              -- (harmless no-op for .waiting tasks which have no timer by invariant).
              ({ s' with
                   taskState           := upd s'.taskState w (some .ready)
                   readyQ              := s'.readyQ ++ [w]
                   mailboxWaiters      := fun ac => if ac = b then ws else s'.mailboxWaiters ac
                   timers              := s'.timers.filter (fun e => e.task ≠ w)
                   waitDeadline        := fun u => if u = w then none else s'.waitDeadline u },
               .ok)
            | [] =>
              match s.timedMailboxWaiters b with
              | w :: ws =>
                -- No regular waiter; wake head timed waiter, also remove timer + clear deadline.
                ({ s' with
                     taskState               := upd s'.taskState w (some .ready)
                     readyQ                  := s'.readyQ ++ [w]
                     timedMailboxWaiters     := fun ac => if ac = b then ws else s'.timedMailboxWaiters ac
                     timers                  := s'.timers.filter (fun e => e.task ≠ w)
                     waitDeadline            := fun u => if u = w then none else s'.waitDeadline u },
                 .ok)
              | [] => (s', .ok)
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
    if s.runtimeStatus ≠ .running ∨ s.actorStatus a = .closed then (s, .invalid)
    else
    match s.mailboxes a with
    | some mb =>
      -- RFC 056: backpressure a full mailbox (reject); distinct from invalid, and
      -- occurrence ids are allocated only on the successful-enqueue path below.
      if s.mailboxFull a mb then (s, .backpressured) else
      -- Stamp envelope with occurrence id and none source (environment); wake head waiter if any (RFC 033).
      let env : Envelope := ⟨s.nextMsgId, none, m⟩
      let s' := { s with
                    mailboxes := upd s.mailboxes a (some (mb.enqueue env))
                    nextMsgId := s.nextMsgId + 1 }
      match s.mailboxWaiters a with
      | w :: ws =>
        -- Regular waiter takes priority. Clear timer/deadline unconditionally (no-op for .waiting).
        ({ s' with
             taskState           := upd s'.taskState w (some .ready)
             readyQ              := s'.readyQ ++ [w]
             mailboxWaiters      := fun ac => if ac = a then ws else s'.mailboxWaiters ac
             timers              := s'.timers.filter (fun e => e.task ≠ w)
             waitDeadline        := fun u => if u = w then none else s'.waitDeadline u },
         .ok)
      | [] =>
        match s.timedMailboxWaiters a with
        | w :: ws =>
          ({ s' with
               taskState               := upd s'.taskState w (some .ready)
               readyQ                  := s'.readyQ ++ [w]
               timedMailboxWaiters     := fun ac => if ac = a then ws else s'.timedMailboxWaiters ac
               timers                  := s'.timers.filter (fun e => e.task ≠ w)
               waitDeadline            := fun u => if u = w then none else s'.waitDeadline u },
           .ok)
        | [] => (s', .ok)
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
      let expiredTasks := (Timer.expired s.timers t).map TimerEntry.task
      let wokenSleeping := expiredTasks.filter (fun u => s.taskState u = some .sleeping)
      let wokenTimed   := expiredTasks.filter (fun u => s.taskState u = some .waitingTimed)
      let woken := wokenSleeping ++ wokenTimed
      ({ s with
          taskState           := wakeMany s.taskState woken
          readyQ              := s.readyQ ++ woken
          timers              := Timer.remaining s.timers t
          timedMailboxWaiters := fun a => (s.timedMailboxWaiters a).filter (· ∉ wokenTimed)
          waitDeadline        := fun u => if u ∈ wokenTimed then none else s.waitDeadline u
          now                 := t }, .woke woken)
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
  | .cancelTree root =>
    -- Cancel root and all descendants, regardless of root's spawn status.
    -- Always returns .ok (RFC 039: no-op if nothing is spawned).
    let toCancel := descendantsOf s root
    (applyCancelTree s toCancel, .ok)
  | .receiveUntil t deadline =>
    if s.running = some t then
      match s.taskState t with
      | some .running =>
        match s.taskOwner t with
        | some a =>
          match s.mailboxes a with
          | some mb =>
            match mb.dequeue with
            | some (env, mb') =>
              -- Message available: immediate dequeue, no state change (RFC 040).
              ({ s with mailboxes := upd s.mailboxes a (some mb') }, .received env)
            | none =>
              if deadline ≤ s.now then
                -- Past-deadline fast path: return timedOut without parking (RFC 040).
                (s, .timedOut)
              else
                -- Park with deadline: register in timedMailboxWaiters and timers.
                ({ s with
                     taskState           := upd s.taskState t (some .waitingTimed)
                     running             := none
                     timedMailboxWaiters := fun ac =>
                       if ac = a then s.timedMailboxWaiters a ++ [t]
                       else s.timedMailboxWaiters ac
                     timers              := Timer.insertSorted ⟨deadline, t⟩ s.timers
                     waitDeadline        := upd s.waitDeadline t (some deadline) },
                 .blocked)
          | none => (s, .invalid)
        | none => (s, .invalid)
      | _ => (s, .invalid)
    else (s, .invalid)
  | .receiveByOccurrence t occ =>
    if s.running = some t then
      match s.taskState t with
      | some .running =>
        match s.taskOwner t with
        | some a =>
          match s.mailboxes a with
          | some mb =>
            match mb.dequeueFirst (·.occurrence = occ) with
            | some (env, mb') =>
              -- Matching envelope found: remove it, preserve other order (RFC 041).
              ({ s with mailboxes := upd s.mailboxes a (some mb') }, .received env)
            | none =>
              -- No match: park in ordinary mailboxWaiters (Option A, Mesa-style).
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
  | .receiveFrom t src =>
    if s.running = some t then
      match s.taskState t with
      | some .running =>
        match s.taskOwner t with
        | some a =>
          match s.mailboxes a with
          | some mb =>
            match mb.dequeueFirst (·.source = some src) with
            | some (env, mb') =>
              -- Matching envelope found: remove it, preserve other order (RFC 041).
              ({ s with mailboxes := upd s.mailboxes a (some mb') }, .received env)
            | none =>
              -- No match: park in ordinary mailboxWaiters (Option A, Mesa-style).
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
  | .fail t =>
    -- Abnormal termination: like cancel, but to .failed (RFC 049).
    match s.taskState t with
    | some st =>
      if st.isTerminal then (s, .invalid)
      else
        let ownerWaitersUpdate : ActorId → List TaskId :=
          match s.taskOwner t with
          | some a => fun ac => if ac = a then (s.mailboxWaiters a).filter (· ≠ t)
                                else s.mailboxWaiters ac
          | none   => s.mailboxWaiters
        let ownerTimedWaitersUpdate : ActorId → List TaskId :=
          fun ac => (s.timedMailboxWaiters ac).filter (· ≠ t)
        ({ s with
            taskState               := upd s.taskState t (some .failed)
            readyQ                  := s.readyQ.filter (fun u => u ≠ t)
            timers                  := s.timers.filter (fun e => e.task ≠ t)
            running                 := if s.running = some t then none else s.running
            mailboxWaiters          := ownerWaitersUpdate
            timedMailboxWaiters     := ownerTimedWaitersUpdate
            waitDeadline            := fun u => if u = t then none else s.waitDeadline u
            resources               := markClosingIf (· == t) s.resources }, .ok)
    | none => (s, .invalid)
  | .restartOne parent failedChild actor =>
    -- One-for-one restart: spawn a fresh replacement for a failed child (RFC 049).
    if s.running = some parent then
      match s.taskState parent with
      | some .running =>
        if s.taskParent failedChild = some parent then
          match s.taskState failedChild with
          | some .failed =>
            let n := s.nextId
            match s.taskState n with
            | none =>
              let mbs := match s.mailboxes actor with
                | some _ => s.mailboxes
                | none   => upd s.mailboxes actor (some Mailbox.empty)
              ({ s with
                  taskState  := upd s.taskState n (some .new)
                  taskOwner  := upd s.taskOwner n (some actor)
                  taskParent := upd s.taskParent n (some parent)
                  readyQ     := s.readyQ ++ [n]
                  mailboxes  := mbs
                  nextId     := n + 1
                  restartOf  := upd s.restartOf n (some failedChild) }, .spawned n)
            | some _ => (s, .invalid)
          | _ => (s, .invalid)
        else (s, .invalid)
      | _ => (s, .invalid)
    else (s, .invalid)
  | .closeActor a =>
    -- Reject admission to actor `a`; keep existing mailbox contents (RFC 055).
    -- RFC 091: closing the actor also marks its actor-owned `allocated`
    -- resources `closing` (its cleanup obligations), leaving task-owned and
    -- already-closing/released resources untouched.
    match s.mailboxes a with
    | some _ => ({ s with actorStatus := upd s.actorStatus a .closed
                          resources   := markActorResourcesClosing a s.resources }, .ok)
    | none   => (s, .invalid)
  | .shutdown =>
    -- Begin runtime shutdown; idempotent (RFC 055).
    ({ s with runtimeStatus := .shuttingDown }, .ok)
  | .stopWhenIdle =>
    -- Stop iff the SCHEDULER is quiescent. Resource-blind: may stop with live
    -- resources (RFC 055; the distinction is intentional, see RFC 092).
    if s.running = none ∧ s.readyQ = [] ∧ s.timers = [] then
      ({ s with runtimeStatus := .stopped }, .ok)
    else (s, .invalid)
  | .stopWhenDrained =>
    -- Stop iff quiescent AND the ledger is fully drained; enters CleanStopped
    -- (RFC 087 / RFC 092).
    if s.running = none ∧ s.readyQ = [] ∧ s.timers = [] ∧ s.resourceDrained = true then
      ({ s with runtimeStatus := .stopped }, .ok)
    else (s, .invalid)
  | .acquire t =>
    -- A running task allocates a fresh resource (RFC 057).
    if s.running = some t then
      match s.taskState t with
      | some .running =>
        ({ s with
            resources := upd s.resources s.nextResourceId (some ⟨.task t, .allocated⟩)
            nextResourceId := s.nextResourceId + 1 }, .acquired s.nextResourceId)
      | _ => (s, .invalid)
    else (s, .invalid)
  | .acquireActor a =>
    -- Control-plane allocation (RFC 091): while the runtime is running, an
    -- existing, open actor `a` acquires a fresh actor-owned resource. Actor
    -- existence is witnessed by a mailbox (`actorStatus` is total/default-active,
    -- so status alone cannot witness existence).
    if s.runtimeStatus = .running then
      if s.actorStatus a = .closed then (s, .invalid)
      else
        match s.mailboxes a with
        | some _ =>
          ({ s with
              resources := upd s.resources s.nextResourceId (some ⟨.actor a, .allocated⟩)
              nextResourceId := s.nextResourceId + 1 }, .acquired s.nextResourceId)
        | none => (s, .invalid)
    else (s, .invalid)
  | .releaseActor a r =>
    -- Control-plane voluntary release of an actor-owned resource (RFC 093);
    -- running-gated, symmetric with `acquireActor`.
    if s.runtimeStatus = .running then
      match s.resources r with
      | some ⟨.actor a', .allocated⟩ =>
        if a' = a then
          ({ s with resources := upd s.resources r (some ⟨.actor a, .released⟩) }, .ok)
        else (s, .invalid)
      | _ => (s, .invalid)
    else (s, .invalid)
  | .release t r =>
    -- The owning running task releases a live resource (RFC 057).
    if s.running = some t then
      match s.taskState t with
      | some .running =>
        match s.resources r with
        | some ⟨o, .allocated⟩ =>
          if o = .task t then
            ({ s with resources := upd s.resources r (some ⟨o, .released⟩) }, .ok)
          else (s, .invalid)
        | _ => (s, .invalid)
      | _ => (s, .invalid)
    else (s, .invalid)
  | .finalize r =>
    -- The environment reclaims a closing resource (RFC 057); no running-task
    -- guard, since a closing resource's owner is by construction terminal.
    match s.resources r with
    | some ⟨o, .closing⟩ =>
      ({ s with resources := upd s.resources r (some ⟨o, .released⟩) }, .ok)
    | _ => (s, .invalid)
  | .setPriority t p =>
    -- Set priority on a spawned task, keeping any existing deadline (RFC 059).
    match s.taskState t with
    | some _ =>
      let m := (s.taskMeta t).getD defaultMeta
      ({ s with taskMeta := upd s.taskMeta t (some { m with priority := p }) }, .ok)
    | none => (s, .invalid)
  | .setDeadline t d =>
    -- Set deadline on a spawned task, keeping any existing priority (RFC 059).
    match s.taskState t with
    | some _ =>
      let m := (s.taskMeta t).getD defaultMeta
      ({ s with taskMeta := upd s.taskMeta t (some { m with deadline := some d }) }, .ok)
    | none => (s, .invalid)

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
