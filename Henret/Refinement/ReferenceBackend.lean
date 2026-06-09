import Henret.Refinement.Contract

namespace Henret

/-- Reference backend: carrier `List Envelope`, identity observation.
All laws hold definitionally. -/
def listBackend : MailboxBackend (List Envelope) where
  empty := []
  enqueue s e := s ++ [e]
  dequeue s :=
    match s with
    | []      => none
    | e :: es => some (e, es)
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
    | cons e es => simp [Mailbox.dequeue, h]

end Henret

/-!
# Henret.Refinement.ReferenceBackend

Pure reference backends and their contract proofs (RFC 008, RFC 033).

Two backends discharge `MailboxBackend` entirely in the kernel:

* `listBackend` — the carrier is `List Envelope`, the observation is
  the identity. After RFC 033 the atomic unit is `Envelope` (carrying
  occurrence id, source actor, and body). Laws are definitional.
* `mailboxBackend` — the model's own `Mailbox` type conforms, tying
  the runtime model to the contract.

A native backend (RFC 010) would provide the same operations over an
opaque carrier and *assume* the three laws as named axioms mapped to
conformance tests. The shape of the obligation is identical.
-/
