import Henret.Scheduler.Model
import Henret.Actor.Task
/-!
  # Henret.Render.State  (RFC 050)

  Human-readable renderers for `RuntimeState`: a summary header, a
  per-task location map (which explains the `WellFormed` location
  invariants), and the actor mailbox view.  Pure `String` functions.
-/
namespace Henret

open Henret

namespace Render

/-- A task's `TaskState` as a short word. -/
def stateWord : TaskState → String
  | .new          => "new"
  | .ready        => "ready"
  | .running      => "running"
  | .yielded      => "yielded"
  | .sleeping     => "sleeping"
  | .completed    => "completed"
  | .cancelled    => "cancelled"
  | .waiting      => "waiting"
  | .waitingTimed => "waitingTimed"
  | .failed       => "failed"

/-- The index of `t` in `readyQ`, if present. -/
private def readyIndex (s : RuntimeState) (t : TaskId) : Option Nat :=
  (s.readyQ.enum.find? (fun p => p.2 = t)).map Prod.fst

/-- The actor ids actually in use (owners of spawned tasks), de-duplicated. -/
private def usedActors (s : RuntimeState) : List ActorId :=
  ((List.range s.nextId).filterMap (fun t => s.taskOwner t)).eraseDups

/-- The actor whose ordinary waiter list contains `t`, if any. -/
private def waitingActor (s : RuntimeState) (t : TaskId) : Option ActorId :=
  (usedActors s).find? (fun a => t ∈ s.mailboxWaiters a)

/-- The actor whose timed-waiter list contains `t`, if any. -/
private def timedWaitingActor (s : RuntimeState) (t : TaskId) : Option ActorId :=
  (usedActors s).find? (fun a => t ∈ s.timedMailboxWaiters a)

/-- A one-line description of where task `t` currently lives. -/
def taskLocation (s : RuntimeState) (t : TaskId) : String :=
  match s.taskState t with
  | none    => s!"task {t}: (unspawned)"
  | some st =>
    let owner := match s.taskOwner t with
      | some a => s!"owner actor {a}"
      | none   => "no owner"
    let place :=
      if s.running = some t then "running"
      else match readyIndex s t with
        | some i => s!"readyQ[{i}]"
        | none =>
          match waitingActor s t with
          | some a => s!"waiting on actor {a}"
          | none =>
            match timedWaitingActor s t with
            | some a =>
              match s.waitDeadline t with
              | some d => s!"waitingTimed on actor {a} until {d}"
              | none   => s!"waitingTimed on actor {a}"
            | none =>
              match st with
              | .sleeping =>
                match (s.timers.find? (fun e => e.task = t)) with
                | some e => s!"sleeping until {e.deadline}"
                | none   => "sleeping"
              | .completed => "completed"
              | .cancelled => "cancelled"
              | .failed    => "failed"
              | _          => "off-queue"
    s!"task {t}: {stateWord st}, {place}, {owner}"

/-- The per-task location map for all spawned tasks. -/
def locationMap (s : RuntimeState) : String :=
  let tasks := (List.range s.nextId).filter (fun t => s.taskState t ≠ none)
  if tasks.isEmpty then "  (no tasks spawned)"
  else String.intercalate "\n" (tasks.map (fun t => "  " ++ taskLocation s t))

/-- Render one actor's mailbox: queued occurrence ids and waiter lists. -/
private def mailboxLine (s : RuntimeState) (a : ActorId) : Option String :=
  match s.mailboxes a with
  | none    => none
  | some mb =>
    let occs := mb.messages.map (fun e => toString e.occurrence)
    let msgs := if occs.isEmpty then "(empty)" else String.intercalate ", " occs
    let waiters := s.mailboxWaiters a
    let timed   := s.timedMailboxWaiters a
    let wstr := if waiters.isEmpty then "" else s!"  waiters={waiters}"
    let tstr := if timed.isEmpty then "" else s!"  timedWaiters={timed}"
    some s!"  actor {a}: msgs=[{msgs}]{wstr}{tstr}"

/-- The actor/mailbox view of the state. -/
def mailboxView (s : RuntimeState) : String :=
  let lines := (usedActors s).filterMap (mailboxLine s)
  if lines.isEmpty then "  (no actors)" else String.intercalate "\n" lines

/-- A full one-screen summary of the runtime state. -/
def stateRender (s : RuntimeState) : String :=
  let hdr := s!"RuntimeState  now={s.now}  nextId={s.nextId}  nextMsgId={s.nextMsgId}"
  let run := match s.running with | some t => s!"running={t}" | none => "running=none"
  let rq  := s!"readyQ={s.readyQ}"
  String.intercalate "\n"
    [ hdr, s!"  {run}  {rq}",
      "Tasks:", locationMap s,
      "Mailboxes:", mailboxView s ]

end Render

/-- `RuntimeState.render` — the full state summary (RFC 050). -/
def RuntimeState.render (s : RuntimeState) : String := Render.stateRender s

end Henret
