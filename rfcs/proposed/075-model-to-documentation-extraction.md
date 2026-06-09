# RFC 075 — Model-to-Documentation Extraction

## Status

Proposed strategic RFC.

## Summary

Generate key documentation tables from Lean declarations or from a single checked metadata source. The purpose is to prevent repeated documentation drift in operation lists, result constructors, `WellFormed` fields, theorem names, axiom budgets, and bridge certificates.

## Motivation

Henret has repeatedly found stale documentation during review: wrong scenario counts, old operation grammar, stale theorem names, and old invariant field counts. Existing doc-symbol checks help, but they cannot ensure that conceptual tables remain complete.

Generated or checked documentation should become part of Henret's product quality.

## Goals

- Reduce manual drift in live docs.
- Generate or validate tables for core semantic artifacts.
- Keep generated output readable and reviewable.
- Preserve hand-written explanatory docs around generated tables.

## Non-goals

- Do not generate all documentation.
- Do not require complex Lean metaprogramming at first.
- Do not block normal RFC writing on extraction machinery.

## Candidate generated artifacts

- `RuntimeOp` constructor table.
- `StepResult` constructor table.
- `TaskState` constructor table.
- `WellFormed` field table.
- public theorem API table.
- axiom budget table.
- bridge completeness certificate entries.
- scenario count and names.
- semantic profile capability table.

## Implementation options

### Option A — checked metadata files

Create Lean declarations such as:

```lean
def runtimeOpDocs : List ConstructorDoc := [...]
def wellFormedFieldDocs : List FieldDoc := [...]
```

A script extracts/prints them into Markdown.

Pros: simple and robust.  
Cons: still duplicates some info manually.

### Option B — Lean environment reflection

Use Lean metaprogramming to inspect constructors and structure fields.

Pros: less duplication.  
Cons: more complex; generated docs may be less curated.

### Option C — external parser

Parse Lean source files to generate docs.

Pros: language-independent.  
Cons: fragile; not recommended.

Recommended: Option A first, with selective Option B later.

## Design note

Generated tables should be committed to the repository for readability, but CI should verify that regeneration produces no diff.

## Concerns

- Over-generation can make docs feel mechanical.
- Metadata declarations can drift unless checked against actual constructors.
- Metaprogramming may add maintenance complexity.

## Implementation tasks

1. Add `Henret/Docs/Metadata.lean`.
2. Define metadata for `RuntimeOp`, `StepResult`, `TaskState`, `WellFormed` fields, and headline theorems.
3. Add `scripts/generate_docs.py` or a Lake executable.
4. Generate Markdown fragments under `docs/generated/`.
5. Include generated fragments from live docs or reference them directly.
6. Add CI check that generated docs are up to date.
7. Extend doc-symbol checker to cover generated theorem references.

## Acceptance criteria

- At least four previously drift-prone tables are generated or checked.
- README/guided tour use generated or checked operation/result lists.
- CI fails when generated docs are stale.
