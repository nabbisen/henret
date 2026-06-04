import Henret.Core.Id

namespace Henret

/-- A message. The payload is a natural for model purposes; the
semantics never inspects it, so generalising the payload type is a
mechanical change. -/
structure Message where
  id      : Nat
  payload : Nat
deriving Repr, DecidableEq, Inhabited

/-- FIFO mailbox. -/
structure Mailbox where
  messages : List Message
deriving Repr, DecidableEq, Inhabited

namespace Mailbox

/-- The empty mailbox. -/
def empty : Mailbox := ⟨[]⟩

/-- Enqueue at the tail (FIFO). -/
def enqueue (mb : Mailbox) (m : Message) : Mailbox :=
  ⟨mb.messages ++ [m]⟩

/-- Dequeue the head, if any. -/
def dequeue (mb : Mailbox) : Option (Message × Mailbox) :=
  match mb.messages with
  | []      => none
  | m :: ms => some (m, ⟨ms⟩)

@[simp] theorem enqueue_messages (mb : Mailbox) (m : Message) :
    (mb.enqueue m).messages = mb.messages ++ [m] := rfl

/-- A successful dequeue removes exactly one message — the head —
and leaves the rest untouched, in order. -/
theorem dequeue_spec (mb : Mailbox) :
    match mb.dequeue with
    | none => mb.messages = []
    | some (m, mb') => mb.messages = m :: mb'.messages := by
  cases h : mb.messages with
  | nil => simp [dequeue, h]
  | cons m ms => simp [dequeue, h]

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

Messages and mailboxes (RFC 004, RFC 006).

A mailbox is a FIFO list of messages. `send` appends at the tail;
`receive` removes exactly the head. Ownership is positional: a message
lives in exactly one mailbox list, and the only operations that touch
it are the enqueue/dequeue defined here. The ownership and exact-one
properties are proved in `Henret.Proofs.Messaging`.
-/
