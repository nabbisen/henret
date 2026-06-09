# RFC 069 — Proof Dependency Budget

## Status

Proposed strategic RFC.

## Summary

Introduce a proof dependency budget that classifies public theorems by import cost, axiom footprint, use of classical reasoning, and stability level. This complements the existing axiom audit by making proof complexity visible.

## Motivation

Axiom cleanliness is necessary but not sufficient for a professional Lean library. Users also care about:

- whether importing a theorem elaborates the full preservation corpus;
- whether a theorem depends on `Classical.choice`;
- whether a lemma is public API or internal proof scaffolding;
- whether a theorem is expected to remain stable across versions.

Henret should make this visible.

## Goals

- Define proof budget categories.
- Annotate public theorem groups.
- Extend documentation and release checks.
- Help users choose lightweight imports.

## Non-goals

- Do not forbid classical reasoning entirely.
- Do not require proof-term introspection for all dependencies in v1.
- Do not destabilize current module layout.

## Proposed categories

### Axiom footprint

- `kernel-standard`: only Lean kernel/standard axioms such as `propext`, `Quot.sound`, optionally `Classical.choice`.
- `project-assumption`: depends on explicit Henret or native axioms.
- `trusted-extern`: depends on FFI/backend assumptions.

### Import weight

- `light`: available from `Henret.Model` or small proof modules.
- `standard`: available from `Henret.Proofs`.
- `heavy`: imports preservation machinery or bridge proofs.
- `native`: imports optional native assumptions.

### Public stability

- `public-stable`: documented theorem API.
- `public-experimental`: useful but may change.
- `internal`: helper theorem, not stable.
- `generated`: generated or mechanically derived.

### Constructiveness

- `constructive`: no `Classical.choice`.
- `classical`: depends on classical reasoning.
- `opaque/trusted`: depends on declared assumptions.

## Proposed documentation table

```markdown
| Theorem | Module | Import weight | Axiom footprint | Stability | Notes |
|---|---|---|---|---|---|
| reachable_wf | Henret.Proofs | heavy | kernel-standard | public-stable | master invariant |
| reachable_queue_exact | Henret.Proofs | heavy | kernel-standard | public-stable | queue exactness |
| nativeDequeModel_qRun_tracks | Henret.Native | native | project-assumption | experimental | optional FFI layer |
```

## Design note

This RFC should not become bureaucracy. The table should focus on public theorem API, not every helper lemma.

## Concerns

- Manual tables can drift; pair this with RFC 075 eventually.
- If too many theorems are marked public-stable too early, refactoring becomes painful.
- If too few are public, Henret looks less usable.

## Implementation tasks

1. Create `docs/proof-dependency-budget.md`.
2. Classify headline theorems and major public lemmas.
3. Add stability labels to proof index.
4. Update README to mention theorem API levels.
5. Optionally extend `axiom_audit.py` output with category annotations.
6. Define release policy: public-stable theorem renames require changelog entry.

## Acceptance criteria

- Users can tell which theorem imports are lightweight or heavy.
- Public-stable theorem list is explicit.
- Native/trusted theorems are never mixed silently with kernel-proven core theorems.
