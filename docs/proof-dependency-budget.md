# Proof dependency budget

*RFC 069.* Axiom cleanliness (every theorem ⊆ a tiny allowlist) is necessary but
not sufficient for a library others build on. Readers also want to know, per
theorem: does it pull in `Classical.choice`, how heavy is the import that yields
it, and is it part of the stable public API or internal scaffolding. The
**proof dependency budget** makes those three things visible and keeps them from
silently growing.

This page defines the categories and the policy. The data lives in a generated,
diff-gated table — [`generated/proof-dependency-budget.md`](generated/proof-dependency-budget.md)
— produced by `scripts/proof_dependency_budget.py` and checked by `check.sh`
gate 7. The complementary axiom-footprint *summary counts* are in
[`generated/axiom-budget.md`](generated/axiom-budget.md) (RFC 084).

## What the budget covers

The budget is computed over the **audited theorem surface** — the 156 theorems
whose axiom footprint is pinned in `scripts/axiom_audit.py` and printed by
`check.sh` gate 6. These are the project's named claims; everything users are
asked to trust is here. Each is classified along three axes.

### Constructiveness (does it use classical reasoning?)

- **constructive** — only `propext` and `Quot.sound` (the STD tier). No choice.
- **classical** — also `Classical.choice` (STD_C). In Henret this is confined to
  reachability theorems, where `by_cases` / `obtain` over decidable structure
  pulls choice in; it is never used for an essentially non-constructive result.
- **trusted** — also depends on declared native/FFI axioms (the optional
  `Henret.Native` Chase-Lev layer, RFC 010).

The generated **classical-reasoning budget** lists every `classical` theorem by
name, so a constructive→classical move is a visible diff, not a silent slide.

### Import weight (how much must elaborate)

A coarse, stable proxy derived from the theorem's namespace (full import-graph
precision is a deliberate v1 non-goal):

- **core** — plain `Henret.*`: the model and preservation corpus.
- **bridge** — `Henret.Bridge.*`: lean-runtime bridge / refinement machinery.
- **standard** — `Henret.Trace.*`, `Henret.Diagnostics.*`: light projections.
- **conformance** — `Henret.Conformance.*`: the golden conformance suite.
- **native** — `Henret.Native.*`: the optional FFI layer; pulls in trusted axioms.

### Stability (public API vs internal)

- **public-stable** — the name is on the prefix-defined public theorem surface
  (`generated/public-theorems.md`, RFC 062 §9.2), so it is covered by the
  name-diff gate and the API-stability tiers in
  [`proof-api-stability.md`](proof-api-stability.md).
- **internal** — an audited headline lemma that is not part of the public API;
  it may be refactored without a public-surface migration entry.

## Policy

1. **Classical budget is conscious.** Moving a theorem from `constructive` to
   `classical` (or to `trusted`) changes the generated table; the diff gate makes
   it fail until regenerated and committed. Treat that regeneration as the place
   to ask "did this theorem really need choice?".
2. **Native/trusted is never mixed silently.** `trusted` theorems (the native
   layer) are always visibly separated from kernel-proven core theorems — both
   here and in `axiom-budget.md`.
3. **The table is generated, never hand-edited.** The source of truth is the
   audit allowlist joined with the public-theorem snapshot. Do not edit the
   generated file; run `python3 scripts/proof_dependency_budget.py`.
4. **No bureaucracy creep.** The budget classifies audited theorems only, not
   every helper lemma (internal `wf_*_pass` / `*_under_enqueue` helpers are proof
   scaffolding, governed by `proof-style.md`, and are intentionally out of scope).

## Relationship to other artifacts

| Artifact | Question it answers |
|---|---|
| `generated/axiom-budget.md` (RFC 084) | how many theorems per axiom tier |
| `generated/public-theorems.md` (RFC 062 §9.2) | what is the public theorem surface, by name |
| `proof-api-stability.md` (RFC 062) | what stability promise each public tier carries |
| `proof-ergonomics-metrics.md` (RFC 062) | what a new `RuntimeOp` costs in files touched |
| **this budget** (RFC 069) | per theorem: classical?, how heavy?, public? |
