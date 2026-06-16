---
rfc: 69
title: Proof Dependency Budget
status: Implemented
implemented_in: v0.33.0
supersedes: []
superseded_by: []
depends_on: [62]
blocks: []
category: proofs
---

# RFC 069 — Proof Dependency Budget

## Status

**Implemented in v0.33.0.** Shipped as a generated, diff-gated per-theorem budget
(see _Implementation_ below); the manual-table risk the draft flagged is avoided
by generating from the audit allowlist + public-theorem snapshot.

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

## Implementation (v0.33.0)

Shipped as an additive proof-observability slice — no model change, no new op,
axioms unchanged, all nine fast gates green.

- `scripts/proof_dependency_budget.py` generates
  `docs/generated/proof-dependency-budget.md` from the audit allowlist
  (`scripts/axiom_audit.py`, tier per theorem) joined with the public-theorem
  snapshot (`docs/generated/public-theorems.md`, stability). It classifies the
  156 audited theorems by **constructiveness** (constructive / classical /
  trusted), **import weight** (core / bridge / standard / conformance / native,
  a coarse namespace proxy — full import-graph precision is a v1 non-goal), and
  **stability** (public-stable / internal), and lists every `Classical.choice`
  user explicitly.
- A `--check` mode is wired into `check.sh` gate 7: the budget cannot silently
  drift, so a `constructive → classical` move (or a new audited theorem) fails the
  gate until the table is regenerated and committed — making the classical budget
  a conscious decision.
- `docs/proof-dependency-budget.md` is the human-facing policy page (categories +
  the four policy rules + a map to the related artifacts).

Mapping to the draft tasks: task 1 (human doc) and task 2 (classify the headline
theorems, via the generated table) are done; task 5 (category annotations over the
audit output) is done by the generator. Task 3 (stability labels) is satisfied by
the `stability` column joined from the public-theorem snapshot rather than by
hand-labelling the proof index. Task 4 (README) is recorded in the docs index.
Task 6 (rename policy) is already enforced for public-stable theorems by the
RFC 062 §9.2 name-diff gate, now complemented by this tier/weight/stability gate.

Deliberately out of scope (per the draft non-goals and the design note "should not
become bureaucracy"): proof-term import-graph introspection (the namespace proxy
is honest and stable); per-helper-lemma classification (`wf_*_pass` /
`*_under_enqueue` helpers stay governed by `proof-style.md`); RFC 075 automation
of the table beyond the present generator.

## Acceptance criteria

- Users can tell which theorem imports are lightweight or heavy.
- Public-stable theorem list is explicit.
- Native/trusted theorems are never mixed silently with kernel-proven core theorems.
