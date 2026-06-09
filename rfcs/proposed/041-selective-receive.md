# RFC 041 — Selective Receive

**Status.** Proposed  
**Target version.** v0.11.x or later  
**Priority.** Medium-low  
**Track.** Advanced actor semantics  
**Depends on.** RFC 033 occurrence identity; RFC 040 recommended  
**Touches.** mailbox model, receive operations, messaging proofs, examples, docs

## Summary

Add selective receive operations that consume a matching envelope while preserving the order of nonmatching envelopes.

This RFC should be implemented only after ordinary receive, parking, occurrence identity, and timeout semantics are stable.

## Motivation

Actor systems often need to receive only messages matching a kind, source, id, or correlation key. Henret's current receive consumes only the mailbox head. That is simpler and proof-friendly, but less expressive.

Selective receive will make Henret more actor-like while testing whether the proof architecture can support richer mailbox operations.

## Design constraint

Do not put arbitrary Lean predicates directly into `RuntimeOp` unless there is a clear executable/equality story. Runtime operations should remain first-order and easy to inspect.

## Proposed operations

Start with built-in selectors over envelope fields:

```lean
| receiveByOccurrence (t : TaskId) (occ : MessageId)
| receiveFrom         (t : TaskId) (source : ActorId)
```

Optional later:

```lean
| receiveByBodyTag    (t : TaskId) (tag : Nat)
```

if `Message` gains a structured body.

## Semantics

For `receiveByOccurrence t occ`:

- same guards as `receive t`;
- search the owning actor's mailbox for the first envelope with `occurrence = occ`;
- if found, remove that envelope and return `.received env`;
- preserve relative order of all other envelopes;
- if not found, park or return blocked according to policy.

### Blocking policy

Two options:

**Option A — immediate blocked without selector-specific waiter state.**  
Task parks in ordinary `mailboxWaiters`. Any future message wakes it, and the task re-runs selective receive. This is Mesa-style and simple, but may cause spurious wakeups.

**Option B — selector-aware waiters.**  
Waiter entries carry a selector so only matching deliveries wake them.

```lean
structure WaiterEntry where
  task : TaskId
  selector : Selector
```

Option B is more precise but significantly expands invariants.

## Recommendation

Use **Option A** for the first selective receive RFC. Henret already uses Mesa semantics. Spurious wakeups are acceptable and realistic. Selector-aware waiters can be a future optimization RFC.

## Mailbox helper functions

Add pure helpers:

```lean
def Mailbox.dequeueFirstByOccurrence : MessageId → Mailbox → Option (Envelope × Mailbox)
def Mailbox.dequeueFirstFrom : ActorId → Mailbox → Option (Envelope × Mailbox)
```

Required properties:

```lean
dequeueFirst_preserves_nonmatching_order
dequeueFirst_removes_exactly_one_matching
dequeueFirst_none_preserves_mailbox
dequeueFirst_occurrence_unique_result
```

## Theorems

```lean
receiveByOccurrence_only_own : ...
receiveByOccurrence_removes_matching : ...
receiveByOccurrence_preserves_nonmatching_order : ...
receiveFrom_only_own : ...
receiveFrom_source_matches : ...
selective_receive_empty_or_missing_parks : ...
```

If using Option A, document that blocking is mailbox-level, not selector-level.

## Invariant implications

No new `WellFormed` fields are required for Option A. Existing mailbox occurrence uniqueness should be preserved because selective receive only removes envelopes.

If Option B is selected, add selector-waiter invariants; this RFC recommends deferring that.

## Examples

Add scenarios:

1. mailbox contains A, B, C; receive occurrence B; remaining order A, C.
2. receiveFrom source actor; only matching source is consumed.
3. selector missing; task parks; later nonmatching message wakes under Option A; task rechecks and may park again.

## Acceptance criteria

- Selective receive operations exist.
- Nonmatching envelope order is preserved.
- Exactly one matching envelope is removed.
- Actor-local receive discipline still holds.
- Occurrence uniqueness is preserved.
- Blocking policy is explicitly documented.
- Demo shows both successful selection and missing-selection blocking.

## Risks

Selective receive can become proof-expensive quickly. Keep selectors built-in and finite. Do not introduce arbitrary predicates in this RFC.

## Non-goals

- Erlang-style full pattern matching.
- Selector-aware waiter queues.
- Fairness among selective waiters.
- User-defined predicates inside `RuntimeOp`.
