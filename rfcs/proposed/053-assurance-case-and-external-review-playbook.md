# RFC 053 — Assurance Case and External Review Playbook

## Status

Proposed.

## Summary

Create an explicit assurance case for Henret: a structured argument connecting
claims, evidence, assumptions, tests, and known exclusions. This makes Henret
reviewable by external architects, formal-methods engineers, and runtime
implementers.

## Motivation

Henret already has proof/trust/test discipline, axiom audits, and an honesty
ledger. These are strong raw materials. An assurance case turns them into a
reviewable argument:

- what exactly is claimed;
- why the claim follows;
- where the proof lives;
- what is trusted;
- what is merely tested;
- what is out of scope;
- how regressions are prevented.

This is especially valuable because Henret sits at the boundary of formal
verification and execution management.

## Non-goals

This RFC does not:

- certify Henret under any external standard;
- prove C race freedom;
- replace README or proof index;
- turn every internal lemma into a public claim.

## Proposed design

### Assurance document

Add:

```text
docs/assurance-case.md
```

Suggested structure:

```text
1. System scope
2. Claim hierarchy
3. Kernel-proven claims
4. Trusted assumptions
5. Tested claims
6. Out-of-scope claims
7. Evidence map
8. Review checklist
9. Known residual risks
10. Release sign-off template
```

### Claim hierarchy

Top-level claim:

```text
Henret is a kernel-checked semantic reference for actor/task scheduler states.
```

Subclaims:

```text
C1: Reachable states satisfy WellFormed.
C2: Message occurrence ids are globally unique in reachable states.
C3: Parent chains are acyclic in reachable states.
C4: Actor-local receive touches only the owning actor's mailbox.
C5: Bridge relation holds for covered single-worker operations.
C6: Native assumptions are explicit and budgeted.
```

Each claim must link to:

- theorem name;
- file path;
- assumptions;
- tests, if any;
- caveats.

### External review checklist

Add:

```text
docs/review-playbook.md
```

Checklist examples:

- Does any public claim exceed theorem statements?
- Does any theorem depend on project-specific axioms unexpectedly?
- Are bridge exclusions described in the same document as bridge claims?
- Does every grammar change have a migration note?
- Are examples excluded from public API imports?
- Do docs distinguish no-op blocked result from waiting-state semantics where relevant?

### Residual-risk register

Add:

```text
docs/risk-register.md
```

Initial risks:

- proof maintenance cost as WellFormed grows;
- bridge incompleteness;
- native C concurrency outside Lean logic;
- future liveness claims needing policy assumptions;
- possible over-strict trace equality for multi-worker runtimes.

## Implementation tasks

1. Create assurance case document.
2. Create review playbook.
3. Create risk register.
4. Link each top-level claim to theorem and file.
5. Add axiom budget summary.
6. Add tested-claim summary.
7. Add release sign-off checklist.
8. Include assurance case in README.

## Acceptance criteria

- A reviewer can identify every top-level claim and its evidence.
- Trusted and tested claims are not mixed with kernel-proven claims.
- Known gaps are visible near the related claims.
- The assurance case is updated by release checklist.

## Risks

The assurance case may duplicate docs. Avoid duplication by linking to proof
index and matrix, not copying every theorem table.
