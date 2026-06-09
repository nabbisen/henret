# RFC 078 — Security and Robustness Interpretation

## Status

Proposed strategic RFC.

## Summary

Translate Henret's formal invariants into security and robustness claims understandable by architects, runtime implementers, and reviewers. This RFC does not add new core semantics; it improves the assurance narrative.

## Motivation

Henret proves many structural properties, but external audiences may not immediately see their security or robustness meaning. For example:

- actor-local receive means a task cannot hijack another actor's mailbox;
- occurrence uniqueness means delivery identity is not duplicated;
- parent acyclicity prevents supervision loops;
- invalid no-op prevents malformed operations from corrupting state.

These are practical claims. They should be stated carefully and traceably.

## Goals

- Create a security/robustness interpretation document.
- Map each claim to theorem support.
- Avoid overclaiming confidentiality, integrity, availability, or concurrency guarantees.
- Prepare material for public release and external review.

## Non-goals

- Do not claim cryptographic security.
- Do not claim C runtime memory safety or race freedom from Lean proofs.
- Do not claim fairness or availability unless a liveness layer is implemented.
- Do not turn Henret into a security product.

## Claim categories

### Integrity claims

- Invalid operations do not mutate model state.
- A task can only receive from its own actor's mailbox.
- Occurrence ids are globally unique across reachable mailboxes.
- Parent chains are acyclic.

### Isolation claims

- Actor-local receive prevents cross-actor mailbox consumption.
- Owner and parent fields are stable under defined operations.

### Robustness claims

- Runnable tasks are not lost from ready queue.
- Waiting tasks are represented consistently in waiter queues.
- Timer entries correspond to sleeping tasks under reachable-state invariants.

### Non-claims

- No proof of OS-level thread safety.
- No proof of C data-race freedom.
- No fairness/liveness unless profile-specific theorem exists.
- No protection against malicious runtime adapter unless conformance checks pass.

## Deliverable document

`docs/security-and-robustness-interpretation.md` should include:

```markdown
| Practical claim | Formal support | Caveats |
|---|---|---|
| A task cannot receive from another actor's mailbox | receive_only_own | Only in Henret model; adapter must conform |
| Duplicate message occurrence ids cannot appear in reachable state | reachable_occurrence_unique | Applies to Envelope occurrence ids, not message body equality |
| Invalid operation cannot corrupt state | step_invalid_unchanged | Invalidity is model-defined |
```

## Design note

This document should be conservative. The main purpose is to prevent marketing overclaim while helping users understand why the proofs matter.

## Concerns

- Security language can be misread as real-world security certification.
- Some claims depend on semantic profile.
- Runtime adapter caveats must be visible.

## Implementation tasks

1. Add security/robustness interpretation doc.
2. Map at least 12 claims to theorem support.
3. Add caveat column for every claim.
4. Add non-claims section.
5. Cross-link from README and assurance case.
6. Ensure theorem references pass doc-symbol checker.

## Acceptance criteria

- The project can explain its value to security-minded reviewers without overclaiming.
- Every practical claim has formal support or is explicitly labeled tested/trusted/out-of-scope.
- Non-claims are visible.
