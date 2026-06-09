# RFC 037 — v0.8.1 Public Claim Repair

**Status.** Implemented (v0.9.0)  
**Target version.** v0.8.1  
**Priority.** Highest  
**Track.** Release hygiene, public claim integrity  
**Depends on.** v0.8.0 archive and RFC 035 current implementation  
**Touches.** README, guided tour, proof index, proof/trust/test matrix, `RuntimeOp` docstrings, RFC 035 status wording, scripts/check gates

## Summary

Repair all stale or over-strong public claims left after v0.8.0. This RFC is intentionally editorial but release-blocking. Henret's value depends on exact alignment between model semantics, theorem names, proof/trust/test classification, and public documentation.

The core model does not need semantic changes in this RFC. The goal is to make v0.8.1 an honest base for RFC 036 bridge completion.

## Motivation

The v0.8.0 review found that the semantic kernel is strong, but some public claims still describe older versions:

- the demo scenario count is stale;
- the `RuntimeOp.send` provenance note predates `Envelope.source`;
- README text says send/receive do not touch task state, which is false after parked receive and wake-one semantics;
- guided-tour parenthood text uses old field counts;
- RFC 035 is marked fully implemented although the bridge is currently a skeleton.

These are not cosmetic. In a formal-verification project, stale claims are product defects because they damage the trust boundary.

## Scope

### In scope

1. Fix stale user-facing documentation.
2. Correct source docstrings that overstate or understate current semantics.
3. Downgrade RFC 035 wording to “single-worker bridge skeleton” if the full bridge is deferred to RFC 036.
4. Expand phrase and symbol gates to catch the specific stale phrases discovered in the review.
5. Update examples/test index if scenario naming or counts changed.

### Out of scope

- Any change to `RuntimeState`, `RuntimeOp`, `step`, or proofs.
- Bridge theorem completion.
- New actor features.
- New preservation automation.

## Required edits

### 1. Avoid hard-coded demo scenario counts

Replace text such as:

```text
The demo exercises six scenarios ...
```

with:

```text
The demo exercises a sequence of regression scenarios covering lifecycle,
mailboxes, parking, timers, cancellation, parenthood, occurrence identity,
and bridge-facing behavior.
```

If a count is kept, ensure `scripts/check.sh` or a generated doc process validates it.

### 2. Fix `RuntimeOp.send` provenance note

Replace the old note that says a delivered `Message` carries no source actor.

Recommended docstring:

```lean
/-- The running task `t` sends body `m` to actor `b`'s mailbox.

    The delivered value is wrapped in an `Envelope` stamped with:
    - `occurrence = s.nextMsgId`
    - `source = taskOwner t`

    Guards: `t` is the running task in `.running` state, `t` has an
    owning actor, and `b`'s mailbox exists.
-/
```

If the actual parameter is still named `Message`, clarify that `Message` is the body and `Envelope` is the mailbox payload.

### 3. Split mailbox effects from scheduling side effects

Replace the false README claim:

```text
send appends exactly one message to exactly one mailbox; receive consumes exactly the head; neither touches task state
```

with:

```text
Mailbox payload effects: `send`/`inject` append one envelope to the target mailbox;
successful `receive` removes exactly the head envelope.

Scheduling side effects: under Mesa semantics, delivery may wake one waiting task;
an empty own-mailbox `receive` parks the running task.
```

### 4. Fix parenthood field-count references

Replace:

```text
field 15 of 16
all 16 fields
```

with:

```text
`WellFormed.parent_lt` and `WellFormed.parent_spawned` are the parenthood
fields of the current 19-field invariant.
```

### 5. Downgrade RFC 035 status

Change the RFC title/status or preamble from full implementation to skeleton implementation.

Recommended status block:

```markdown
**Status.** Implemented as bridge skeleton in v0.8.0; full single-worker
bridge preservation deferred to RFC 036.
```

Recommended title:

```markdown
# RFC 035 — Single-Worker Lean-Runtime Bridge Skeleton
```

### 6. Add stale phrase gates

Add live-doc phrase checks for at least:

```text
six scenarios
field 15 of 16
all 16 fields
message carries no source actor
requires an envelope or occurrence identity
neither touches task state
RFC 035 — Lean-Runtime Bridge: Connecting
```

Historical directories may be excluded only if the exclusion is explicit and documented.

## Acceptance criteria

- `lake build Henret` passes.
- `lake exe henret-demo` passes.
- `doc_symbol_check.py` still resolves all live-doc symbols.
- `check.sh` fails if the stale phrases above are reintroduced into live docs.
- README, guided tour, proof index, test index, and matrix all agree on current semantics.
- No Lean theorem statement changes are required.

## Risks

The main risk is overfitting phrase gates to the current review. The correct mitigation is to add both phrase checks and symbol checks, while preferring generated or count-free prose where possible.

## Non-goals

This RFC must not attempt to complete bridge proofs. Doing so would mix release hygiene with semantic work and make review harder.
