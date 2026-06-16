# RFC 052 — Semantic Extension Governance

## Status

Implemented (v0.15.3).

## Summary

Define governance rules for changing Henret's semantic core. Henret's value is
precision. As `RuntimeOp`, `RuntimeState`, `StepResult`, and `WellFormed` evolve,
the project needs a disciplined extension process that prevents silent theorem,
documentation, and bridge drift.

## Motivation

Henret has repeatedly encountered drift:

- operation grammar changed but docs lagged;
- theorem names changed but proof index lagged;
- result semantics changed from blocked-no-op to parking;
- bridge claims were stronger than implemented cases.

The solution is not merely more review. The project needs governance rules that
make semantic extension predictable.

## Non-goals

This RFC does not:

- freeze the model permanently;
- require bureaucratic process for private experiments;
- prevent breaking changes before a stable public release;
- replace technical review.

## Proposed design

### Semantic-core files

Classify these as semantic-core files:

```text
Henret/Scheduler/Op.lean
Henret/Scheduler/Model.lean
Henret/Core/Result.lean
Henret/Actor/Task.lean
Henret/Actor/Mailbox.lean
Henret/Proofs/Invariants.lean
Henret/Proofs/InvariantsPreservation.lean
Henret/Bridge/*
```

Changes to these require a semantic-impact checklist.

### Required checklist for semantic changes

Every semantic-core RFC must answer:

1. What public type changes?
2. What `step` branches change?
3. What `WellFormed` fields are added, removed, or strengthened?
4. What preservation cases change?
5. What examples must change?
6. What bridge translation changes?
7. What trace events change?
8. What proof/trust/test matrix entries change?
9. What migration note is needed?
10. What old phrase should be banned by stale-phrase gate?

### Theorem stability levels

Classify public theorem names:

- **Stable**: promised to remain or deprecate with alias.
- **Experimental**: may change between minor versions.
- **Internal**: no public stability.

Add theorem annotations in docs, not necessarily in Lean attributes.

### Deprecation rule

If a theorem is renamed, keep a compatibility alias for one release when
reasonable:

```lean
theorem old_name := new_name
```

Do not keep aliases that obscure semantic changes.

### Bridge claim rule

No bridge RFC may use "complete" unless every operation with readyQ effect is
covered or explicitly excluded in the headline.

## Implementation tasks

1. Create `docs/semantic-extension-governance.md`.
2. Create RFC template section: Semantic Impact Checklist.
3. Classify current public theorem names.
4. Add stable/experimental/internal table to proof index.
5. Add stale-phrase registration process.
6. Add bridge claim rule to acceptance policy.
7. Update RFC README.

## Acceptance criteria

- New RFC template includes semantic impact checklist.
- Proof index classifies theorem stability.
- Bridge completion claims are constrained by policy.
- The process is light enough for continued development.

## Risks

Too much process can slow research. Keep governance focused on public claims and
semantic-core changes only.
