---
rfc: 22
title: Message Occurrence Semantics
status: Implemented
implemented_in: v0.2.1
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC-HENRET-022: Message Occurrence Semantics

## Motivation

`Message` is a value (`id`, `payload`); two distinct `send` operations can
deliver equal values to one or more mailboxes. Documentation saying "a
message is never duplicated by the model" overclaimed: the proven theorems
are per-operation (one send = one append; one receive = one head removal),
not a global occurrence-uniqueness property.

## Decision

Messages remain **values** for now. The documentation is scoped accordingly
(`Henret/Proofs/Messaging.lean` docstring): per-operation non-duplication is
PROVEN; value-level global uniqueness is not claimed.

The occurrence model — fresh `MessageId` allocation in `RuntimeState`, a
`WellFormed` field asserting each occurrence lives in exactly one mailbox,
and send/receive proofs over it — is recorded here as the design sketch for
a future RFC if actor semantics require it.

## Acceptance criteria

- [x] The matrix and module docs no longer overclaim message
      non-duplication.
- [x] The future occurrence design is written down.
