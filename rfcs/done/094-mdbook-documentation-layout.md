---
rfc: 94
title: mdbook Documentation Layout (docs/src/)
status: Implemented
implemented_in: v0.34.0
supersedes: []
superseded_by: []
depends_on: [75, 84]
blocks: []
category: documentation
---

# RFC 094 — mdbook Documentation Layout (`docs/src/`)

## Status

Implemented in v0.34.0. Approved with amendments (architect review); see the
acceptance-criteria amendments at the end of this RFC for what shipped and the
two recorded deviations.

## Summary

The project guidelines call for documentation under `docs/src/`, "structured to
be compatible with mdbook." That layout was never implemented: docs live flat in
`docs/*.md`, there is no `book.toml` and no `SUMMARY.md`, and `mdbook build` has
nothing to build. Meanwhile the generated-doc set (RFC 075/084/062/069) is
hard-wired to `docs/generated/`.

This RFC adopts the intended layout: a `book.toml` at `docs/`, a persona-organized
`docs/src/SUMMARY.md`, the user/contributor-facing docs moved under `docs/src/`,
and the generators repointed to `docs/src/generated/`. It is a **move-and-relink**
change, not a content rewrite, and it must update the documentation gates
(`doc_symbol`, `doc_count`, the generated-doc drift `--check`) so they keep
passing at the new paths.

## Motivation

- **Stated convention vs reality.** The guidelines say `docs/src/` + mdbook; the
  repo has flat `docs/` and no book. The divergence is silent — nothing fails,
  but the documented build does not exist.
- **Browsable docs.** Consumers (e.g. iotakt) and contributors benefit from a
  navigable, cross-linked site rather than a flat directory of `.md` files.
- **Generated docs belong in the book.** The model tables, theorem index, axiom
  budget, proof-dependency budget, and RFC index (`docs/generated/`) should
  render inside the book, which means the generators must target the book tree.
- **Persona structure already exists on paper.** The guidelines define three
  reader paths (New Users / Intermediate / Maintainers); the book's `SUMMARY.md`
  is the natural place to realize them.

## Goals

- `mdbook build` (run from `docs/`) produces a browsable site.
- A hand-maintained `docs/src/SUMMARY.md` organized by the three personas.
- All doc generators write into `docs/src/generated/`; gate 7's generated-doc
  `--check` stays green at the new paths.
- The documentation gates (`doc_symbol_check`, `doc_count_check`) updated to the
  new paths and green.
- No prose rewritten — only files moved and cross-references relinked.

## Non-goals

- **No content rewrite.** Bodies are unchanged; this is layout + links.
- **No site hosting/deploy.** Publishing the built site (GitHub Pages, etc.) is a
  separate concern, deferred to the publication plan (RFC 079).
- **No new fast gate.** `mdbook` is a Rust tool, not part of the Lean/Lake proof
  toolchain. To keep the proof CI minimal, `mdbook build` is **not** added to
  `check.sh` fast gates; it is at most an optional docs-CI step.
- **No change to generator content.** Only their output (`OUT`) and snapshot-read
  paths move.

## Proposed layout

Adopt the explicit `src/` layout (rather than pointing mdbook at flat `docs/`
with `src = "."`, which would drag repo-internal process files into the book):

```
docs/
  book.toml                 # mdbook config: [book] src = "src"
  src/
    SUMMARY.md              # the book spine (hand-maintained, persona-ordered)
    introduction.md         # short landing page (intro, not a README copy)
    <user/contributor chapters>.md
    generated/              # generators' new OUT (moved from docs/generated/)
      runtime-op-table.md, wellformed-field-table.md, step-result-table.md,
      task-state-table.md, public-theorems.md, public-theorem-index.md,
      axiom-budget.md, proof-dependency-budget.md, rfc-index.md
  migration/                # upgrade guides — included in book (see below)
  reviews/                  # repo-internal: NOT in book
  patterns/                 # decide at review (likely in book)
  evidence-ledger.yaml      # data artifact: NOT in book
  handoff-*.md              # repo-internal handoffs: NOT in book
```

### Book content vs repo-internal (the main review decision)

The reviewable judgement is *which* docs are reader-facing chapters (→ `src/`)
versus repo-internal process/data artifacts (→ stay in `docs/` root, excluded
from the book). Proposed classification:

| In the book (`docs/src/`) | Repo-internal (stays in `docs/`) |
|---|---|
| project-positioning, guided-tour, naming-and-scope, profile-index, model-explorer | reviews/ (architect review records) |
| integration-contract, observability, deadline-priority, resource-lifetime, resource-drain | handoff-*.md (session handoffs) |
| native-backend-boundary, package-boundary, bridge-architecture, conformance-suite | evidence-ledger.yaml (machine data) |
| proof-index, proof-style, proof-engineering, proof-api-stability | progress-policy, risk-register (process) |
| proof-dependency-budget, proof-ergonomics-metrics, assurance-case, fault-taxonomy | release-checklist (operator runbook — could go either way) |
| assumption-index, prior-art-runtime-workspace, migration/, generated/ | release-policy (could go either way) |

The split is deliberately conservative: anything a *reader* of the model would
consult goes in the book; anything that is review/handoff/process/data stays out.
The boundary cases (release-checklist, release-policy, patterns/) are flagged for
the architect to rule on.

### SUMMARY organization (by persona)

`docs/src/SUMMARY.md` is hand-maintained (mdbook convention) and ordered by the
guideline personas:

```markdown
# Summary

- [Introduction](introduction.md)

# New users
- [What Henret is](project-positioning.md)
- [Guided tour](guided-tour.md)
- [Profiles](profile-index.md)
- [Model explorer](model-explorer.md)

# Intermediate users
- [Integration contract](integration-contract.md)
- [Proof index (theorem API)](proof-index.md)
- [Conformance suite](conformance-suite.md)
- [Observability](observability.md)
- [Migration guides](migration/README.md)
- [Generated reference](generated/runtime-op-table.md)
  - ... (model tables, theorem index, axiom & dependency budgets, RFC index)

# Maintainers & contributors
- [Proof style](proof-style.md)
- [Proof engineering](proof-engineering.md)
- [API stability](proof-api-stability.md)
- [Proof dependency budget](proof-dependency-budget.md)
- [Proof ergonomics metrics](proof-ergonomics-metrics.md)
- [Assurance case](assurance-case.md)
- [Fault taxonomy](fault-taxonomy.md)
- [Package boundary](package-boundary.md)
```

## Tooling and gate impact (explicit)

This is the part that makes the change "more than a folder rename." Each item
must move in lockstep, in one commit:

1. **Generator `OUT` paths** → `docs/src/generated/`:
   `extract_model_docs.py`, `extract_theorem_docs.py`, `extract_rfc_index.py`,
   `public_theorem_index.py`, `proof_dependency_budget.py`. The last two also
   **read** `public-theorems.md`; that read path moves too.
2. **`check.sh` gate 7** invokes those scripts with `--check`; since the paths
   live inside the scripts, repointing the scripts suffices, but the gate must be
   re-run to confirm.
3. **`doc_count_check.py`** `EXCLUDE_DIR` currently lists `docs/generated`,
   `docs/reviews`, `docs/migration` → update to the new locations.
4. **`doc_symbol_check.py`** scans a fixed set of docs (proof-index, matrix,
   README, guided-tour, …) → update those paths to `docs/src/`.
5. **Relative cross-references.** Moving `docs/foo.md` → `docs/src/foo.md` changes
   link depths (e.g. `generated/...` references). A grep sweep + `mdbook build`'s
   broken-link detection covers this.
6. **README "More Detail" links** and the guideline references point into `docs/`
   → update to `docs/src/`.
7. **`GENERATED by ...` headers** in generated files that cite paths → regenerate.

## Migration plan (single atomic change, per RFC 000)

1. Add `docs/book.toml` and `docs/src/`.
2. `git mv` the in-book docs into `docs/src/` and `docs/generated/` →
   `docs/src/generated/`.
3. Repoint generator `OUT`/read paths and the gate scan/exclude paths.
4. Fix relative cross-references; run `mdbook build` to surface broken links.
5. Regenerate every generated doc into the new location; run `check.sh --fast`.
6. Write `docs/src/SUMMARY.md` and `docs/src/introduction.md`.
7. Update README links and the guideline references.

Combine all of the above in one dedicated change; do not spread it across
unrelated commits (RFC 000 anti-pattern guidance).

## Concerns / open questions

- **New non-Lean dependency.** mdbook (Rust) is needed to *build* the site, but
  not to verify proofs. Keeping it out of the fast gates avoids adding a Rust
  toolchain to the proof CI. Open question: do we want a separate, optional
  docs-CI job that runs `mdbook build` (link-check), and should it block release?
  Proposed: optional, non-blocking, link-check only.
- **Book-vs-internal boundary.** The classification table above is the main thing
  to ratify; the boundary cases (release-checklist/policy, patterns/) need a call.
- **SUMMARY drift.** A hand-maintained SUMMARY can fall behind new docs. Proposed:
  start hand-maintained; add a lightweight "every `src/*.md` is reachable from
  SUMMARY" orphan-check later only if drift appears (do not over-tool up front).
- **Link churn.** The relative-path rewrite is mechanical but broad; `mdbook
  build` + a grep sweep are the safety net.

## Acceptance criteria

- `mdbook build` from `docs/` succeeds and yields a browsable, cross-linked site.
- All generators write to `docs/src/generated/`; gate 7's generated-doc `--check`
  is green at the new paths.
- `doc_symbol_check` and `doc_count_check` are green at the new paths.
- `SUMMARY.md` is organized by the three personas and reaches every in-book doc.
- No doc body was rewritten; the diff is moves + relinks + path updates.
- README and the guideline references point at `docs/src/`.

## Review note

This RFC is the deliberate decision the flat-vs-`src/` question requires. It is
not started until the architect reviews and approves the scope — in particular
the book-vs-internal classification and the "no mdbook fast gate" stance. A
review request will be raised when the time comes.

## Acceptance criteria (as amended by architect review)

Shipped in v0.34.0:

- All book-included docs live under `docs/src/`; migration guides under
  `docs/src/migration/` (linked from `SUMMARY.md`).
- `scripts/check_docs.sh` runs `mdbook build docs` and structure checks **outside**
  `check.sh --fast`. Blocking for documentation/layout PRs and release candidates.
- `scripts/doc_summary_check.py`: every non-excluded `docs/src/**.md` is reachable
  from `SUMMARY.md`; every SUMMARY target exists; every local Markdown link
  resolves (the orphan + link checks the architect required in §7 and §10).
- Book/internal boundary recorded (§5): `release-policy`, `release-checklist`,
  `progress-policy`, `review-playbook` in the book's maintainer section;
  `evidence-ledger.yaml`, `reviews/`, `handoff-*.md`, `risk-register.md` kept
  internal at `docs/` root; `patterns/refinement-contract.md` (stable) in the book.
- `doc_count_check.py` excludes `docs/src/migration/`; the migration template now
  requires historical counts to be marked as historical (§9).
- CHANGELOG (v0.34.0) records the documentation path move and the path-break for
  external links to `docs/generated/...`.

## Recorded deviations from the suggested structure

1. **Flat `docs/src/` + SUMMARY-section organization** instead of literal
   `docs/src/release/` and `docs/src/maintainers/` subdirectories. The amendment
   required every chapter under `docs/src/` and the persona organization; mdBook
   takes its section structure from `SUMMARY.md` headings rather than the folder
   tree, so keeping the 38 top-level pages flat (preserving only the pre-existing
   `generated/`, `migration/`, `patterns/` subdirs) realizes the three reader
   paths via `SUMMARY.md` while avoiding the relative-link churn that nesting two
   pages into new subdirs would have caused. The suggested subdirs remain an easy
   follow-up if preferred.
2. **`extract_rfc_index.py` link prefix fix.** The RFC-index generator emitted
   RFC links as `done/NNN.md`, which never resolved from the generated-doc
   location (a latent pre-existing break). They now emit `../../../rfcs/NNN.md`
   so the links resolve from `docs/src/generated/` and the docs gate's local-link
   check passes book-wide. This is a correctness fix adjacent to the move, not a
   semantic content change.
