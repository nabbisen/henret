import Henret.Core.Id

namespace Henret

/-- A message value. The payload is a natural for model purposes; the
semantics never inspects it, so generalising the payload type is a
mechanical change. -/
structure Message where
  id      : Nat
  payload : Nat
deriving Repr, DecidableEq, Inhabited

/-- Unique occurrence identity for one delivered message.
Allocated from `RuntimeState.nextMsgId` at send/inject time.
Monotone; proves global uniqueness across all mailboxes (RFC 033). -/
abbrev MessageId := Nat

/-- A delivered envelope: a `Message` together with its unique
occurrence id and the actor that sent it (or `none` for external
injection). Placed in mailboxes at send/inject; dequeued at receive.
The envelope is immutable in transit — no operation rewrites a queued
envelope (RFC 033). -/
structure Envelope where
  /-- Globally unique id allocated at delivery time. -/
  occurrence : MessageId
  /-- `some a` = sent by a task owned by actor `a` (via `send`).
      `none`   = delivered by the environment (via `inject`). -/
  source     : Option ActorId
  /-- The message body. -/
  body       : Message
deriving Repr, DecidableEq, Inhabited

/-- FIFO mailbox holding envelopes. -/
structure Mailbox where
  messages : List Envelope
deriving Repr, DecidableEq, Inhabited

namespace Mailbox

/-- The empty mailbox. -/
def empty : Mailbox := ⟨[]⟩

/-- Enqueue one envelope at the tail (FIFO). -/
def enqueue (mb : Mailbox) (e : Envelope) : Mailbox :=
  ⟨mb.messages ++ [e]⟩

/-- Dequeue the head envelope, if any. -/
def dequeue (mb : Mailbox) : Option (Envelope × Mailbox) :=
  match mb.messages with
  | []      => none
  | e :: es => some (e, ⟨es⟩)

@[simp] theorem enqueue_messages (mb : Mailbox) (e : Envelope) :
    (mb.enqueue e).messages = mb.messages ++ [e] := rfl

/-- A successful dequeue removes exactly one envelope — the head —
and leaves the rest untouched, in order. -/
theorem dequeue_spec (mb : Mailbox) :
    match mb.dequeue with
    | none => mb.messages = []
    | some (e, mb') => mb.messages = e :: mb'.messages := by
  cases h : mb.messages with
  | nil => simp [dequeue, h]
  | cons e es => simp [dequeue, h]

end Mailbox

/-- Per-actor mailbox map. `none` means the actor does not exist. -/
abbrev ActorMap := ActorId → Option Mailbox

/-- Actor state: identity plus mailbox. The runtime keeps mailboxes in
an `ActorMap`; this record is the per-actor view used by examples. -/
structure ActorState where
  id      : ActorId
  mailbox : Mailbox
deriving Repr, Inhabited

end Henret

/-!
# Henret.Actor.Mailbox

Messages, envelopes, and mailboxes (RFC 004, RFC 006, RFC 033).

A mailbox is a FIFO list of **envelopes** (RFC 033). Each envelope
wraps a `Message` body with:
- `occurrence : MessageId` — globally unique id allocated at delivery;
  proves `reachable_occurrence_unique`.
- `source : Option ActorId` — the owning actor of the sending task
  (`some a` from `send`), or `none` for external injection.

`send` appends at the tail; `receive` removes exactly the head.
The model proves per-operation envelope effects and global occurrence
uniqueness (`Henret.Proofs.Occurrence`).
-/
