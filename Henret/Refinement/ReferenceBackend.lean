import Henret.Refinement.Contract

namespace Henret

/-- Reference backend: carrier `List Message`, identity observation.
All laws hold definitionally. -/
def listBackend : MailboxBackend (List Message) where
  empty := []
  enqueue s m := s ++ [m]
  dequeue s :=
    match s with
    | []      => none
    | m :: ms => some (m, ms)
  toList s := s
  toList_empty := rfl
  toList_enqueue _ _ := rfl
  toList_dequeue s := by
    cases s <;> simp

/-- The model's own `Mailbox` satisfies the contract. -/
def mailboxBackend : MailboxBackend Mailbox where
  empty := Mailbox.empty
  enqueue := Mailbox.enqueue
  dequeue := Mailbox.dequeue
  toList mb := mb.messages
  toList_empty := rfl
  toList_enqueue _ _ := rfl
  toList_dequeue mb := by
    cases h : mb.messages with
    | nil => simp [Mailbox.dequeue, h]
    | cons m ms => simp [Mailbox.dequeue, h]

end Henret

/-!
# Henret.Refinement.ReferenceBackend

Pure reference backends and their contract proofs (RFC 008).

Two backends discharge `MailboxBackend` entirely in the kernel:

* `listBackend` — the carrier is `List Message` itself, the
  observation is the identity. The simplest possible conforming
  backend; the laws are definitional.
* `mailboxBackend` — the model's own `Mailbox` type conforms, which
  ties the runtime model to the contract: anything proved against the
  contract holds of the model's mailboxes.

A native backend (RFC 010) would provide the same four operations over
an opaque carrier and *assume* the three laws as named axioms mapped
to conformance tests. The shape of the obligation is identical — that
is the point of the pattern.
-/
