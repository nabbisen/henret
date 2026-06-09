---
title: Message Envelope and Occurrence Identity
rfc: RFC-HENRET-033
status: Implemented (v0.7.0)
project: Henret
package: henret
namespace: Henret
depends: RFC 022 (deferred design), RFC 024 (send owner guard); orthogonal to RFC 031/032
---

# RFC-HENRET-033: Message Envelope and Occurrence Identity

## Motivation

Two known, documented gaps close together here:

1. **Occurrence identity (RFC 022).** `Message` is a value type; the
   model can prove per-operation effects but not "each message
   occurrence lives in at most one mailbox" — two sends of equal values
   are indistinguishable. The matrix and `Mailbox.lean` carry explicit
   disclaimers to this effect.
2. **Source provenance (RFC 024/026 PROVENANCE NOTE).** `send`'s guards
   prove a running, actor-owned task performed the send, but the
   delivered value records nothing — the model cannot connect a
   received message to its sending actor.

Both are representation problems with the same fix: deliver envelopes,
not bare values.

## Design

### The envelope

```lean
structure Envelope where
  occurrence : MessageId        -- fresh per delivery, model-allocated
  source     : Option ActorId   -- some a = sent by a task of actor a
                                -- none   = environment injection
  body       : Message
deriving Repr, DecidableEq
```

`MessageId := Nat`. `RuntimeState` gains `nextMsgId : Nat` (init 0),
the exact analogue of `nextId` for tasks — and the proof strategy
deliberately reuses the `fresh_none` discipline that made task-id
reasoning cheap.

`source : Option ActorId` makes the environment path honest: `inject`
stamps `none`, not a fake actor. The asymmetry is the point — the
type records exactly what the operation knows.

### Operational changes

- `send t b m` (guards unchanged): the owner lookup that RFC 024 only
  *guarded on* is now **used** — enqueue
  `⟨s.nextMsgId, s.taskOwner t, m⟩`, bump `nextMsgId`.
- `inject a m`: enqueue `⟨s.nextMsgId, none, m⟩`, bump `nextMsgId`.
- `receive t`: dequeues an `Envelope`; `StepResult.received` now
  carries the envelope — the receiver *sees* the source, which is what
  makes provenance usable rather than merely stored.
- `Mailbox.messages : List Envelope`. The `MailboxBackend` contract
  laws and the reference backend restate over `Envelope`; the law
  *shapes* are element-type-generic, so this is mechanical (decide at
  implementation whether to parameterize the backend by element type or
  fix it to `Envelope`; parameterization is cleaner if the refinement
  proofs stay unchanged, otherwise fix the type).

### Occurrence uniqueness: formulating over an infinite domain

`mailboxes : ActorId → Option Mailbox` ranges over all of `Nat`, so
"the multiset of all occurrence ids is nodup" cannot be stated by
enumeration. Two finite-content fields capture it:

```lean
  occ_fresh :     -- allocated ids only (the fresh_none analogue)
    ∀ a mb e, s.mailboxes a = some mb → e ∈ mb.messages →
      e.occurrence < s.nextMsgId
  occ_nodup :     -- within one mailbox
    ∀ a mb, s.mailboxes a = some mb →
      (mb.messages.map Envelope.occurrence).Nodup
  occ_disjoint :  -- across mailboxes
    ∀ a b mba mbb, a ≠ b →
      s.mailboxes a = some mba → s.mailboxes b = some mbb →
      ∀ ea ∈ mba.messages, ∀ eb ∈ mbb.messages,
        ea.occurrence ≠ eb.occurrence
```

Note the pairwise-values formulation alone would miss a duplicate of
the *same* envelope value twice in one list; `occ_nodup` (over the
mapped id list) catches exactly that, which is why both within- and
across-mailbox fields are needed.

Preservation is the `fresh_none` playbook: send/inject append an id
equal to `nextMsgId`, which `occ_fresh` says exceeds every existing id
in *every* mailbox — so nodup and disjointness extend; receive removes
the head — sublists preserve all three; every other operation leaves
mailboxes untouched (`StepProjections`).

## What "provenance" will and will not claim

Provable, and claimed:

- `send_stamps_source` — the envelope created by `send t b m` carries
  `source = s.taskOwner t` (the genuine owner, by the guard).
- `inject_stamps_none` — environment deliveries are marked as such.
- **`reachable_occurrence_unique`** (headline) — in every reachable
  state, an occurrence id identifies at most one envelope in at most
  one mailbox.
- Envelope immutability in transit: no operation rewrites an enqueued
  envelope (operations only append or remove-head; provable from the
  step definition).

**Not claimed (and documented as such):** the trace-history statement
"every envelope in a mailbox with `source = some a` *was placed by* a
send from a task owned by `a`". That is a statement about runs, not
states; making it a theorem needs either a trace-indexed predicate or
a history-carrying ghost state. The compositional argument
(stamping + uniqueness + immutability) is what this RFC delivers; the
single trace theorem is recorded as a possible strengthening if a
consumer needs it in one piece. This keeps the claim discipline honest
— the same standard RFC 022 applied to the old overclaim.

## Compatibility and churn

Breaking for: `Mailbox`, `MailboxBackend` + reference backend,
`StepResult.received`, every messaging theorem statement (mechanical:
`Message` → `Envelope` at the dequeue site), examples 02/04, demo
scenarios 2/7, the native deque differential tests if they exercise
message values. No new operations, no new task states — churn is wide
but shallow, concentrated in `Messaging.lean` and the three new
`WellFormed` fields (→ +3). Orthogonal to RFC 031/032; if RFC 031 lands
first, its `deliver_wakes_head` restates over envelopes with no design
interaction.

## Out of scope

Message TTLs/priorities; selective receive by source or id;
deduplication semantics (uniqueness is an invariant, not an API);
multi-hop forwarding provenance (an envelope re-sent gets a *new*
occurrence and source — forwarding history is future work).

## Acceptance criteria

- [ ] `reachable_occurrence_unique` kernel-checked, audit-allowlisted.
- [ ] `send_stamps_source` / `inject_stamps_none` proved; example 04
      shows a received envelope's source for both paths.
- [ ] `Mailbox.lean` and matrix disclaimers about unmodeled occurrence
      identity replaced by the new positive claims.
- [ ] Refinement backend re-verified over `Envelope`.
