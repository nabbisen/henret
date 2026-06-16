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

/-! ## Selective dequeue (RFC 041)

Built-in selectors over envelope fields. Each removes the **first**
envelope matching a finite, decidable predicate and preserves the
relative order of every other envelope. No arbitrary Lean predicates
enter the operation grammar — selectors are first-order. -/

/-- Remove the first list element satisfying a decidable predicate,
returning it together with the remaining list (order preserved).
Structural recursion keeps the proofs index-free. -/
def listDequeueFirst (p : Envelope → Bool) :
    List Envelope → Option (Envelope × List Envelope)
  | []      => none
  | e :: es =>
    if p e then some (e, es)
    else match listDequeueFirst p es with
         | none          => none
         | some (e', es') => some (e', e :: es')

/-- A generic selective dequeue: remove the first matching envelope. -/
def dequeueFirst (p : Envelope → Bool) (mb : Mailbox) :
    Option (Envelope × Mailbox) :=
  match listDequeueFirst p mb.messages with
  | none          => none
  | some (e, es)  => some (e, ⟨es⟩)

/-- Remove the first envelope with the given occurrence id. -/
def dequeueFirstByOccurrence (occ : MessageId) (mb : Mailbox) :
    Option (Envelope × Mailbox) :=
  mb.dequeueFirst (·.occurrence = occ)

/-- Remove the first envelope sent by the given source actor. -/
def dequeueFirstFrom (src : ActorId) (mb : Mailbox) :
    Option (Envelope × Mailbox) :=
  mb.dequeueFirst (·.source = some src)

/-- A successful selective dequeue returns a matching envelope. -/
theorem listDequeueFirst_matches (p : Envelope → Bool) :
    ∀ {l : List Envelope} {e : Envelope} {l' : List Envelope},
      listDequeueFirst p l = some (e, l') → p e = true := by
  intro l
  induction l with
  | nil => intro e l' h; simp [listDequeueFirst] at h
  | cons x xs ih =>
    intro e l' h
    simp only [listDequeueFirst] at h
    by_cases hp : p x
    · rw [if_pos hp] at h
      obtain ⟨rfl, _⟩ := Option.some.inj h; exact hp
    · rw [if_neg (by simpa using hp)] at h
      cases hr : listDequeueFirst p xs with
      | none => rw [hr] at h; simp at h
      | some pair =>
        obtain ⟨e', es'⟩ := pair
        rw [hr] at h
        obtain ⟨rfl, _⟩ := Option.some.inj h
        exact ih hr

/-- A successful selective dequeue's result is a member of the original list. -/
theorem listDequeueFirst_mem (p : Envelope → Bool) :
    ∀ {l : List Envelope} {e : Envelope} {l' : List Envelope},
      listDequeueFirst p l = some (e, l') → e ∈ l := by
  intro l
  induction l with
  | nil => intro e l' h; simp [listDequeueFirst] at h
  | cons x xs ih =>
    intro e l' h
    simp only [listDequeueFirst] at h
    by_cases hp : p x
    · rw [if_pos hp] at h
      obtain ⟨rfl, _⟩ := Option.some.inj h; exact List.mem_cons_self x xs
    · rw [if_neg (by simpa using hp)] at h
      cases hr : listDequeueFirst p xs with
      | none => rw [hr] at h; simp at h
      | some pair =>
        obtain ⟨e', es'⟩ := pair
        rw [hr] at h
        obtain ⟨rfl, _⟩ := Option.some.inj h
        exact List.mem_cons_of_mem x (ih hr)

/-- The remaining list after a selective dequeue is a sublist of the
original — selective dequeue removes only, never reorders or adds. -/
theorem listDequeueFirst_sublist (p : Envelope → Bool) :
    ∀ {l : List Envelope} {e : Envelope} {l' : List Envelope},
      listDequeueFirst p l = some (e, l') → l'.Sublist l := by
  intro l
  induction l with
  | nil => intro e l' h; simp [listDequeueFirst] at h
  | cons x xs ih =>
    intro e l' h
    simp only [listDequeueFirst] at h
    by_cases hp : p x
    · rw [if_pos hp] at h
      obtain ⟨_, rfl⟩ := Option.some.inj h
      exact List.sublist_cons_self x xs
    · rw [if_neg (by simpa using hp)] at h
      cases hr : listDequeueFirst p xs with
      | none => rw [hr] at h; simp at h
      | some pair =>
        obtain ⟨e', es'⟩ := pair
        rw [hr] at h
        obtain ⟨_, rfl⟩ := Option.some.inj h
        exact (ih hr).cons₂ x

/-- A failed selective dequeue means no element matches. -/
theorem listDequeueFirst_none (p : Envelope → Bool) :
    ∀ {l : List Envelope}, listDequeueFirst p l = none → ∀ e ∈ l, p e = false := by
  intro l
  induction l with
  | nil => intro _ e he; simp at he
  | cons x xs ih =>
    intro h e he
    simp only [listDequeueFirst] at h
    by_cases hp : p x
    · rw [if_pos hp] at h; simp at h
    · rw [if_neg (by simpa using hp)] at h
      cases hr : listDequeueFirst p xs with
      | none =>
        rcases List.mem_cons.mp he with rfl | hmem
        · simpa using hp
        · exact ih hr e hmem
      | some pair => obtain ⟨e', es'⟩ := pair; rw [hr] at h; simp at h

/-- `dequeueFirst` returns a matching envelope. -/
theorem dequeueFirst_matches (p : Envelope → Bool) (mb : Mailbox)
    {e : Envelope} {mb' : Mailbox}
    (h : mb.dequeueFirst p = some (e, mb')) : p e = true := by
  unfold dequeueFirst at h
  cases hr : listDequeueFirst p mb.messages with
  | none => rw [hr] at h; simp at h
  | some pair =>
    obtain ⟨e', es'⟩ := pair; rw [hr] at h
    obtain ⟨rfl, _⟩ := Option.some.inj h
    exact listDequeueFirst_matches p hr

/-- `dequeueFirst` leaves a sublist of the original mailbox. -/
theorem dequeueFirst_sublist (p : Envelope → Bool) (mb : Mailbox)
    {e : Envelope} {mb' : Mailbox}
    (h : mb.dequeueFirst p = some (e, mb')) : mb'.messages.Sublist mb.messages := by
  unfold dequeueFirst at h
  cases hr : listDequeueFirst p mb.messages with
  | none => rw [hr] at h; simp at h
  | some pair =>
    obtain ⟨e', es'⟩ := pair; rw [hr] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hmb⟩ := h
    rw [← hmb]; exact listDequeueFirst_sublist p hr

/-- A failed `dequeueFirst` means the mailbox is unchanged and no
envelope matches. -/
theorem dequeueFirst_none (p : Envelope → Bool) (mb : Mailbox)
    (h : mb.dequeueFirst p = none) : ∀ e ∈ mb.messages, p e = false := by
  unfold dequeueFirst at h
  cases hr : listDequeueFirst p mb.messages with
  | none => exact listDequeueFirst_none p hr
  | some pair => obtain ⟨e', es'⟩ := pair; rw [hr] at h; simp at h

/-! ## Length lemmas for bounded mailboxes (RFC 056)

These live with `Mailbox` rather than inside the preservation proofs so the
capacity invariant's per-operation bullets stay one-liners. -/

/-- Enqueue increases mailbox length by exactly one. -/
@[simp] theorem enqueue_length (mb : Mailbox) (e : Envelope) :
    (mb.enqueue e).messages.length = mb.messages.length + 1 := by
  simp [enqueue]

/-- If a mailbox has room (`length < n`), one enqueue keeps it within `n`. -/
theorem enqueue_length_le_capacity_of_lt {mb : Mailbox} {e : Envelope} {n : Nat}
    (h : mb.messages.length < n) : (mb.enqueue e).messages.length ≤ n := by
  rw [enqueue_length]; omega

/-- A head dequeue never increases mailbox length. -/
theorem dequeue_length_le {mb : Mailbox} {e : Envelope} {mb' : Mailbox}
    (h : mb.dequeue = some (e, mb')) : mb'.messages.length ≤ mb.messages.length := by
  cases hm : mb.messages with
  | nil => simp [dequeue, hm] at h
  | cons x xs =>
    simp only [dequeue, hm] at h
    obtain ⟨_, rfl⟩ := h
    simp

/-- A selective dequeue never increases mailbox length (RFC 041 + 056). -/
theorem dequeueFirst_length_le {p : Envelope → Bool} {mb mb' : Mailbox} {e : Envelope}
    (h : mb.dequeueFirst p = some (e, mb')) : mb'.messages.length ≤ mb.messages.length :=
  (dequeueFirst_sublist p mb h).length_le

end Mailbox

/-- Per-actor mailbox policy (RFC 056). A single-field record now — a
**stability seam**: the overflow policy (reject / drop / park) is a plausible
second knob, and `RuntimeState` is public and documentation-generated, so a
record avoids future churn. `capacity = none` means unbounded.

Option A models the **reject** overflow behavior only: a valid delivery to a
full mailbox returns `.backpressured` and leaves the state unchanged. No
unimplemented overflow constructors are exposed, since public constructors are
a promise consumers may pattern-match on. -/
structure MailboxPolicy where
  /-- `some n` bounds the mailbox to `n` envelopes; `none` is unbounded. -/
  capacity : Option Nat
deriving Repr, DecidableEq, Inhabited

namespace MailboxPolicy

/-- The default policy: unbounded capacity (preserves pre-RFC-056 behavior). -/
def unbounded : MailboxPolicy := { capacity := none }

@[simp] theorem unbounded_capacity : unbounded.capacity = none := rfl

end MailboxPolicy

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
