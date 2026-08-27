---
rfc: 103
title: Evidence Ledger to Gate Binding
status: Implemented
implemented_in: v0.34.6
supersedes: []
superseded_by: []
depends_on: [81, 102]
blocks: []
category: release-process
---

# RFC 103 — Evidence Ledger to Gate Binding

## Status

Implemented in v0.34.6. `verified_by_ci: true` is bound to a checked
gate/workflow record, and bounded explorer execution (gate 11) is a required
`release-core` gate. Closed through the review chain in
`.git-exclude/reviewed/008`–`010`.

## Summary

Make `verified_by_ci: true` a checked reference to an executable gate/workflow
record, and add bounded explorer execution to release-core so its TESTED claim
has current CI evidence.

## Motivation

The evidence ledger currently marks the bounded explorer as CI-verified even
though CI only builds some explorer modules and never runs the executable. A
boolean assertion is too weak for a provenance-centered ledger.

## Non-goals

- Do not turn bounded exploration into proof.
- Do not claim out-of-tree runtime evidence is verified by this repository.
- Do not require network access for evidence validation.

## Proposed design

1. Add a stable evidence/gate identifier to each in-tree `verified_by_ci: true`
   record.
2. Validate that the identifier exists in the active gate registry or named
   workflow and that its command is executed in the claimed profile.
3. Add a bounded, deterministic `henret-explore` execution gate to release-core,
   with world/depth parameters recorded in output and manifest evidence.
4. Preserve the distinction between build evidence, execution evidence, proof,
   and out-of-tree/null evidence.
5. Fail generation when a gate is renamed/removed without updating its ledger
   claims.
6. Introduce `release-core-v3` / `rfc103-release-core-v3` rather than changing
   the retained RFC 102 v2 registry in place. Numeric IDs remain ordering and
   compatibility fields; ledger claims bind to stable semantic IDs.
7. Assign each semantic gate an evidence capability. Require PROVEN model
   proofs to bind to kernel-build evidence, TRUSTED proof-boundary claims to
   axiom-audit evidence, and in-tree TESTED claims to executable-test evidence.
8. Derive explorer manifest parameters/results from one executed
   machine-readable record. Require all bounded confirmations and the genuine
   deterministic minimal counterexample `[spawn 0]` before exit success.
9. Treat the JSON record as a strict retained schema: reject duplicate object
   keys at every depth, require exact object fields, and distinguish JSON
   booleans from integers without language-level equality coercion.

## Implementation tasks

1. Extend the ledger schema and validator.
2. Add explorer build/execution as a named required gate.
3. Add positive/negative validator fixtures.
4. Update the evidence ledger rendering, manifest schema, and release checklist.

## Acceptance criteria

- Every `verified_by_ci: true` record names a resolvable gate/workflow id.
- Deleting or skipping the named gate makes ledger validation fail.
- Release-core runs the bounded explorer and records its parameters, result,
  duration, and output hash.
- The current verifier rejects missing/mismatched semantic IDs and malformed
  explorer evidence, including duplicate keys and boolean/integer type
  substitution, while retaining valid v1/v2 compatibility.
- The explorer remains classified TESTED, never PROVEN.
- Out-of-tree runtime claims remain `verified_by_this_tarball: false` and
  `verified_by_ci: false` unless immutable external coordinates are added.

## Risks

Gate identifiers become retained evidence and need compatibility rules. Prefer
stable semantic ids over array positions or incidental display names.
