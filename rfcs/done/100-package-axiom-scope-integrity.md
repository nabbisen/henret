---
rfc: 100
title: Package Axiom Scope Integrity
status: Implemented
implemented_in: v0.34.6
supersedes: []
superseded_by: []
depends_on: [20, 69, 84]
blocks: [102]
category: proofs
---

# RFC 100 — Package Axiom Scope Integrity

## Status

Implemented in v0.34.6. The three `native_decide` proofs are removed from
`Henret.Examples.Basic` and the package-wide `native_decide` gate is enforced
via `scripts/native_decide_check.py`; closed through the review chain in
`.git-exclude/reviewed/004`–`005`.

## Summary

Remove the three `native_decide` proofs from `Henret.Examples.Basic`, gate the
package against undeclared `native_decide` use, and make every axiom-budget
statement identify its exact import and theorem scope.

## Motivation

The default `import Henret` theorem surface remains within its declared
STD/STD_C budget, but three opt-in example theorems currently depend on
`Lean.ofReduceBool`. Package-wide prose says `native_decide` is forbidden while
the selected-theorem audit does not inspect those theorems. The proof boundary
is therefore narrower than the public wording.

## Non-goals

- Do not classify `Lean.ofReduceBool` as a kernel proof dependency.
- Do not broaden the optional six-axiom native deque trust boundary.
- Do not require every private/internal lemma to become a stable public theorem.

## Proposed design

1. Replace the three example proofs with kernel `decide` proofs or ordinary
   proofs whose axiom sets satisfy the package policy.
2. Add a source-aware gate that rejects executable `native_decide` use in all
   tracked Lean sources. Comments and documentation examples are parsed or
   scoped explicitly rather than matched accidentally.
3. Separate three claims in generated and narrative documentation:
   - default import (`import Henret`) axiom boundary;
   - selected, gate-audited public theorem set;
   - optional `Henret.Native.*` trusted axioms.
4. Add representative opt-in example theorems to an audit tier or add a
   package-wide theorem inventory check that detects new undeclared axiom
   classes without pretending every theorem is stable API.

## Implementation tasks

1. Rewrite `spawnChild_parent_check`, `spawnChild_parent_was_running`, and
   `spawnChild_child_state` without `native_decide`.
2. Add the prohibition check and self-tests.
3. Update the axiom budget generator, proof index, assumption index, handoff
   wording, and release checklist.
4. Hash the new policy script in release evidence.

## Acceptance criteria

- No tracked Lean source contains an executable `native_decide` invocation.
- `#print axioms` for the three example theorems contains no
  `Lean.ofReduceBool`.
- The gate fails on a fixture that introduces `native_decide` outside an
  explicitly documented exception policy.
- Every public axiom-budget statement names its import/theorem scope.
- The optional native deque remains the only declared project-specific trust
  surface.

## Risks

A simple text grep can create blind spots or false positives. The gate must have
self-tests and a deliberately narrow exception mechanism, with no broad path
exclusion for examples.
