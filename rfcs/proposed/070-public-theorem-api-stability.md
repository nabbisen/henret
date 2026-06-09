# RFC 070 — Public Theorem API Stability

## Status

Proposed strategic RFC.

## Summary

Define which Henret theorem names, structures, and semantic claims are part of the stable public API. This protects users while preserving room for proof-internal refactoring.

## Motivation

Henret's theorem corpus is growing. Some theorem names are conceptual products: `reachable_wf`, `reachable_queue_exact`, `receive_only_own`, `reachable_occurrence_unique`. Others are helper lemmas created to make preservation proofs manageable.

Without an API policy, users may import internal lemmas and get broken by normal refactoring, or maintainers may accidentally rename a headline theorem without noticing the public impact.

## Goals

- Define theorem API stability classes.
- Mark public-stable theorems.
- Establish compatibility rules for releases.
- Update documentation symbol checker to distinguish stable and internal symbols.

## Non-goals

- Do not freeze every theorem.
- Do not prevent refactoring of proof internals.
- Do not promise semantic backward compatibility for experimental RFCs.

## Proposed stability classes

### Stable public API

Examples:

```lean
reachable_wf
reachable_queue_exact
reachable_waiters_exact
receive_only_own
reachable_parent_lt
parent_chain_terminates
reachable_occurrence_unique
```

Rules:

- Rename requires deprecation alias or major/minor release note.
- Statement strengthening is allowed if existing use remains valid.
- Statement weakening requires explicit breaking-change RFC.

### Public experimental API

Useful but not yet stable.

Examples:

- bridge theorems during RFC 035/036;
- semantic-profile experimental claims;
- trace equivalence claims.

### Internal proof API

Examples:

- field projection lemmas;
- operation-specific preservation helpers;
- simp-normalization lemmas.

Rules:

- May change without deprecation.
- Should not be highlighted in README.

### Generated/scaffold API

Examples:

- generated theorem lists;
- mechanical decomposition lemmas.

Rules:

- Not for user imports.

## Design note

Public API status should be documented in one place and then referenced by proof index and release notes. Do not scatter status labels only in comments.

## Concerns

- Some helper lemmas may become popular with users. Provide a process to promote them.
- Deprecation aliases may add maintenance cost.
- Stable theorem statements should be chosen carefully.

## Implementation tasks

1. Create `docs/public-theorem-api.md`.
2. Add stability column to proof index.
3. Mark each public theorem group.
4. Add release checklist: public theorem additions/removals/renames must be listed.
5. Add optional deprecated aliases for any recently renamed public theorem.
6. Add examples that import only stable public API.

## Acceptance criteria

- Public-stable theorem set is explicitly listed.
- Internal helper theorem use in docs is minimized or marked internal.
- Release notes include theorem API changes.
