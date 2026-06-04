import Henret.Actor.Mailbox

namespace Henret

/-- Contract for any mailbox backend with carrier `σ`.

The three laws pin the backend to FIFO list semantics through the
observation `toList`:

* `toList_empty` — the empty backend observes as `[]`;
* `toList_enqueue` — enqueue observes as a tail append (message
  identity preserved);
* `toList_dequeue` — dequeue observes as removing exactly the head,
  and only fails on the empty observation.
-/
structure MailboxBackend (σ : Type) where
  empty   : σ
  enqueue : σ → Message → σ
  dequeue : σ → Option (Message × σ)
  toList  : σ → List Message
  toList_empty : toList empty = []
  toList_enqueue : ∀ (s : σ) (m : Message),
    toList (enqueue s m) = toList s ++ [m]
  toList_dequeue : ∀ s : σ,
    match dequeue s with
    | none => toList s = []
    | some (m, s') => toList s = m :: toList s'

namespace MailboxBackend

/-- Any backend satisfying the contract consumes exactly one message
per successful dequeue — a law derived from the contract alone, valid
for every conforming backend. -/
theorem dequeue_length {σ : Type} (B : MailboxBackend σ) (s : σ)
    {m : Message} {s' : σ} (h : B.dequeue s = some (m, s')) :
    (B.toList s).length = (B.toList s').length + 1 := by
  have hs := B.toList_dequeue s
  rw [h] at hs
  simp [hs]

end MailboxBackend

end Henret

/-!
# Henret.Refinement.Contract

The backend-contract pattern (RFC 008).

A *backend contract* packages: the operations a backend must provide,
an observation function `toList` into a pure reference domain, and the
laws tying the operations to the observation. A backend either
*proves* the laws (a pure reference backend — see
`Henret.Refinement.ReferenceBackend`) or *assumes* them as named,
documented, test-mapped trust (a native backend — out of scope for the
Lean-only core, see RFC 010).

The pattern is copyable: replace `Message`/mailbox laws with the
operations and observation of any other component (queue, timer queue,
scheduler driver) to obtain its contract.
-/
