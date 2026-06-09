import Henret.Actor.Mailbox

namespace Henret

/-- Contract for any mailbox backend with carrier `σ`.

After RFC 033, envelopes (not bare messages) are the unit of storage.
The three laws pin the backend to FIFO envelope semantics through the
observation `toList`:

* `toList_empty` — the empty backend observes as `[]`;
* `toList_enqueue` — enqueue observes as a tail append (envelope
  identity preserved);
* `toList_dequeue` — dequeue observes as removing exactly the head,
  and only fails on the empty observation.
-/
structure MailboxBackend (σ : Type) where
  empty   : σ
  enqueue : σ → Envelope → σ
  dequeue : σ → Option (Envelope × σ)
  toList  : σ → List Envelope
  toList_empty : toList empty = []
  toList_enqueue : ∀ (s : σ) (e : Envelope),
    toList (enqueue s e) = toList s ++ [e]
  toList_dequeue : ∀ s : σ,
    match dequeue s with
    | none => toList s = []
    | some (e, s') => toList s = e :: toList s'

namespace MailboxBackend

/-- Any backend satisfying the contract consumes exactly one envelope
per successful dequeue — a law derived from the contract alone, valid
for every conforming backend. -/
theorem dequeue_length {σ : Type} (B : MailboxBackend σ) (s : σ)
    {e : Envelope} {s' : σ} (h : B.dequeue s = some (e, s')) :
    (B.toList s).length = (B.toList s').length + 1 := by
  have hs := B.toList_dequeue s
  rw [h] at hs
  simp [hs]

end MailboxBackend

end Henret

/-!
# Henret.Refinement.Contract

The backend-contract pattern (RFC 008, updated for RFC 033).

A *backend contract* packages: the operations a backend must provide,
an observation function `toList` into a pure reference domain, and the
laws tying the operations to the observation.

After RFC 033, the unit of storage is `Envelope` (carrying
`occurrence`, `source`, and `body`), not bare `Message`. The contract
reflects this: `enqueue` takes an `Envelope`, `dequeue` returns one,
and `toList` produces `List Envelope`.

A backend either *proves* the laws (a pure reference backend — see
`Henret.Refinement.ReferenceBackend`) or *assumes* them as named,
documented, test-mapped trust (a native backend — out of scope for the
Lean-only core, see RFC 010).
-/
