---
rfc: 84
title: Model-to-Documentation Extraction Implementation
status: Implemented
implemented_in: v0.17.7
supersedes: []
superseded_by: []
depends_on: [75, 85]
blocks: [80]
category: documentation
---

# RFC 084 — Model-to-Documentation Extraction Implementation

## Status

Implemented in **v0.17.7** (full generator); the `doc_count_check.py` stopgap
shipped earlier (folded into v0.17.2). Created in the v0.17.0 audit review
follow-up (item A6, decision **A+B**) as the concrete implementation plan for
the strategic **RFC 075 (Model-to-Documentation Extraction)**. Priority **P1**;
final-pass amendments 084-1..5 applied.

The checked descriptor source is `Henret/Meta/Docs.lean` (the `HenretMeta`
lib — import-cheap, 084-5). Three generators emit `docs/generated/`:
`extract_model_docs.py` (operation/state/result/WellFormed tables, validated
against the real declarations — 084-1), `extract_theorem_docs.py` (public
theorem index + axiom budget from the gate-validated audit allowlist, 084-4),
and `extract_rfc_index.py` (RFC index from RFC 085 front matter). The gate
suite (gate 7) regenerates and diffs the committed files; divergence fails.
`doc_count_check.py` excludes `docs/generated/` (084-3).

## Summary

Implement RFC 075 by extracting the project's recurrently-drifting
documentation tables — operation lists, `StepResult` constructors,
`WellFormed` fields, the public theorem index, the axiom budget, and the
RFC index — from a single checked source, and failing CI when committed
docs diverge from the generated output. Ship a small count-check stopgap
first so drift is caught before the full generator lands.

## Motivation

The v0.17.0 audit (and the session before it) repeatedly found stale
counts and names: "twelve / 18 / 21 operations", "19-field", a
non-existent `run_preserves_owner` in the audit gate, and a stale-phrase
gate that missed the prose form "12 operations". The reactive grep
blocklist can only ban phrases someone thought to add. Source-of-truth
extraction removes the entire drift class.

## Goals

- Generate the core semantic tables from a checked source, not by hand.
- Fail CI when committed generated docs differ from a fresh generation.
- Provide an immediate stopgap before the full generator is ready.

## Non-goals

- Generating all documentation (hand-written prose stays hand-written).
- Heavy Lean metaprogramming / parser reflection in the first pass.
- Replacing RFC 075's strategic framing (this RFC implements it).

## Immediate stopgap (ship first)

```text
scripts/doc_count_check.py
```

Computes or reads the current counts from source —
`RuntimeOp` / `TaskState` / `StepResult` constructor counts and the
`WellFormed` field count — and rejects live docs whose count claims
contradict them, e.g. "N operations", "N-operation grammar",
"N WellFormed fields", "N proof-matrix entries". Excludes historical
RFCs/reviews/CHANGELOG (which legitimately cite past counts). Runs in the
RFC 080 gate suite (stage 9).

## Implementation path

1. Start with a **Lean metadata module**, not parser reflection: keep a
   checked list of constructor/field descriptors next to each definition.
2. Have Lean print markdown/JSON from those descriptors.
3. Commit the generated files; CI regenerates and diffs.
4. Hand-written docs include the generated tables by reference or in a
   fenced block delimited by generation markers.

Example source pattern:

```lean
def RuntimeOp.metadata : List ConstructorDoc :=
  [ { name := "spawn", since := "RFC 004", category := "lifecycle" }, ... ]
```

## Deliverables

```text
scripts/doc_count_check.py            stopgap (ships first)
scripts/extract_model_docs.py         model tables from Lean output
scripts/extract_rfc_index.py          RFC index from front matter (RFC 085)
docs/generated/runtime-op-table.md
docs/generated/task-state-table.md
docs/generated/step-result-table.md
docs/generated/wellformed-field-table.md
docs/generated/public-theorem-index.md
docs/generated/axiom-budget.md
docs/generated/rfc-index.md
```

## Final-pass amendments (RFCs 080-086 v2 review)

**084-1 — Metadata validated against definitions.** A hand-kept metadata
list can drift like Markdown, so the generator checks: every metadata
constructor/field name resolves to an actual Lean declaration; names are
duplicate-free; the metadata count equals the real constructor/field count;
tables are produced *only* from metadata that passes these checks.

**084-2 — Generated-block markers.** Hand-written docs that embed generated
tables delimit them exactly:

```markdown
<!-- BEGIN GENERATED: runtime-op-table -->
...
<!-- END GENERATED: runtime-op-table -->
```

CI regenerates and diffs only the marked blocks (or the `docs/generated/`
files).

**084-3 — Stopgap excludes generated docs.** `doc_count_check.py` excludes
historical RFCs/reviews/CHANGELOG **and** `docs/generated/` (generated docs
necessarily contain counts and must not trip the stale-count scan).

**084-4 — Public-theorem-index source of truth.** Public theorems are marked
explicitly — `/-- HENRET_PUBLIC_THEOREM: ... -/` or a
`def PublicTheorem.metadata : List TheoremDoc` — so the index is not another
hand-maintained list.

**084-5 — Split generators by import cost.** Operation/constructor/field
tables extract from a `Henret.Model` import; the theorem index requires
`Henret.Proofs`. Keep the generators separate so cheap tables don't force a
full proof build.

## Acceptance criteria

```text
- doc_count_check.py runs in RFC 080 gate stage 9; excludes historical files
  AND docs/generated/.
- Metadata is validated against real declarations (names resolve,
  duplicate-free, counts match) before any table is generated.
- Generated docs are committed and regenerated+diffed in CI (marked blocks
  or docs/generated/ files); divergence fails.
- Public theorems are marked via an explicit source of truth (084-4).
- Generators are split by import cost (Model vs Proofs).
- The RFC index generator consumes RFC 085 front-matter metadata.
```

## Priority and sequencing

P1, but split across the wave per the v2 review: the **`doc_count_check.py`
stopgap lands second** (right after RFC 085, supporting RFC 080 stage 9),
while the **full generator lands last** (step 8), once metadata (085) and
the gates (080) are stable. Consumes RFC 085 front-matter for the RFC index.

## References

- Implements RFC 075 (model-to-documentation extraction, strategic).
- Consumes RFC 085 (RFC metadata normalization).
- Runs inside the RFC 080 (release gate integrity) gate suite.
- v0.17.0 audit review, item A6 and additional recommendation 1.
