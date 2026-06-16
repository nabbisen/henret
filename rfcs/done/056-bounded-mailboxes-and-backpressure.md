---
rfc: 56
title: Bounded Mailboxes and Backpressure
status: Implemented
implemented_in: v0.18.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC 056 — Bounded Mailboxes and Backpressure

## Status

Proposed.

## Summary

Add optional bounded-mailbox semantics and distinguish full-mailbox backpressure from invalid protocol errors.

## Motivation

Current mailboxes are unbounded. Real actor runtimes often need bounded queues to control memory growth and apply backpressure. Henret should be able to model a legal send that cannot proceed because the mailbox is full, without conflating it with invalid sender state.

## Non-goals

- Do not implement blocked sends and receive timeouts in the same RFC unless the design is already stable.
- Do not require all profiles to use bounded mailboxes.
- Do not claim fairness: a blocked sender may remain blocked forever without a policy.

## Design

Introduce mailbox capacity as an optional semantic layer:

```lean
structure MailboxPolicy where
  capacity : ActorId → Option Nat
```

Add `StepResult.backpressured` or `StepResult.sendBlocked`.

Two possible designs:

A. Result-only first:
- full mailbox send returns `.backpressured`, state unchanged.

B. Full parking semantics:
- full mailbox send parks the sender in `TaskState.sending` or `TaskState.blockedSend`.
- add `mailboxSenders : ActorId → List PendingSend`.

Recommended: implement A first, then B in a follow-up if needed.

## Formal model changes

If implementing full parking, add:

```lean
structure PendingSend where
  task : TaskId
  target : ActorId
  env : Envelope

mailboxSenders : ActorId → List PendingSend
```

For the first RFC, avoid this state unless necessary.

## Proof obligations

- `send_full_backpressured`
- `backpressured_unchanged` if result-only design is chosen.
- `bounded_mailbox_never_exceeds_capacity` for reachable states under bounded profile.
- `receive_may_unblock_sender` only if parked-send semantics are implemented.

## Tests and examples

- Demo: bounded actor with capacity 1, first send succeeds, second returns backpressured.
- Demo: receive frees capacity.
- Golden trace for bounded vs unbounded profile.

## Documentation updates

- Add “full is legal, not invalid” section.
- Update profile matrix: bounded mailboxes are not part of default core unless explicitly selected.

## Acceptance criteria

- Capacity invariant is proved.
- Full mailbox behavior is explicit.
- Existing unbounded semantics remain available.
- The docs do not imply backpressured tasks eventually proceed.

## Risks and review questions

- Should capacity be per-actor, global, or profile-level constant?
- Should environment `inject` obey capacity or bypass it?
- Should capacity count waiters or only messages?
