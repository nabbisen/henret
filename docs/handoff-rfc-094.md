# Checkpoint handoff — RFC 094 (mdBook Documentation Layout) implemented as v0.34.0

**For:** architect review
**Release:** `henret-v0.34.0.tar.gz`
**Scope:** documentation-architecture only — no model, no proof, no theorem change.
Axioms unchanged; public theorem surface unchanged (101 names). All nine
`check.sh --fast` gates green; the new `check_docs.sh` gate green.

## What shipped

The documentation surface is now an mdBook.

- `docs/book.toml` (`src = "src"`, git URL `nabbisen/henret`).
- `docs/src/SUMMARY.md` — hand-maintained, organized into three reader paths
  (New users / Intermediate users & integrators / Maintainers & contributors).
  54 chapter links covering all 38 top-level pages plus the `migration/`,
  `generated/`, and `patterns/` entries.
- `docs/src/introduction.md` — new reader-oriented intro (identity, three reader
  paths, generated-reference entry point). Not a README copy (§11).
- All in-book docs moved `docs/*.md` → `docs/src/*.md`; `generated/`,
  `migration/`, `patterns/` moved under `docs/src/` preserving structure.

### Book / internal boundary (ratified per §5)

- **In book** (`docs/src/`): the 24 docs the review listed, plus the additional
  reader/integrator/maintainer pages (roadmap, scheduling/shutdown/supervision
  semantics, trace-ledger, test-index, theorem-naming, evidence-ledger.md,
  proof-trust-test-matrix, semantic-extension-governance). Maintainer section
  holds `release-policy`, `release-checklist`, `progress-policy`,
  `review-playbook`. Stable pattern `patterns/refinement-contract.md` is in book.
- **Internal** (stay at `docs/` root): `reviews/`, `handoff-*.md`,
  `risk-register.md`, and `evidence-ledger.yaml` (machine data; its reader-facing
  rendering `evidence-ledger.md` is in the book). `docs/README.md` repurposed as
  a short root pointer to the book.

### Docs gate (separate from the Lean fast gate, §6/§7/§10)

- `scripts/doc_summary_check.py` — orphan check (every `docs/src/**.md` reachable
  from `SUMMARY.md`, `ORPHAN_EXCLUDE = {SUMMARY.md}`), every SUMMARY target
  exists, every local Markdown link resolves.
- `scripts/check_docs.sh` — runs the structure check then `mdbook build docs`.
  **Not** in `check.sh --fast`. Blocking for documentation/layout PRs and release
  candidates (recorded in `docs/src/release-checklist.md`). Exits 2 if `mdbook`
  is absent so CI can distinguish "tool missing" from "checks failed".
- Verified in-sandbox with mdBook v0.5.3: `56 pages, all reachable from SUMMARY;
  187 local links resolve` + `mdbook: build succeeded`.

### Generator / gate repointing (§8, one commit)

`extract_model_docs`, `extract_theorem_docs`, `extract_rfc_index`,
`public_theorem_index`, `proof_dependency_budget` now write/read
`docs/src/generated/` (OUT + snapshot paths + prose/headers). `doc_symbol_check`
scan list, `doc_count_check` `EXCLUDE_DIR`, `forbidden_claim_check` ledger path
(+ message), and `fault_taxonomy_check` DOC path all updated. All five generator
`--check` modes pass against the relocated committed copies.

### doc_count convention (§9)

`docs/src/migration/` stays excluded from the stale-current-count gate; the
migration template now requires historical counts to be marked as historical,
and the script comment records why.

### CHANGELOG / version

`lakefile.lean` → `v0.34.0` (and its `release-policy` comment path fixed).
CHANGELOG v0.34.0 entry records the move, the boundary, the gate, and the
**path-break compatibility note** (external links to `docs/generated/...` /
`docs/*.md` now live under `docs/src/...`; pre-contract-freeze, no symlink shim).
Historical CHANGELOG entries left as-is — they accurately describe paths as they
were at the time (not a semantic rewrite).

### Evidence

RFC moved to `rfcs/done/094-...md` (status Implemented, `implemented_in:
v0.34.0`); `rfcs/README.md` row updated; `rfc-index` regenerated. Matrix claim
**237** (DOCUMENTED) and a `proof-index` RFC 094 section added. Root `README.md`
in-book links repointed (risk-register / evidence-ledger.yaml left at root) and a
book pointer added to the learning path.

## Recorded deviations from the suggested structure

1. **Flat `docs/src/` + SUMMARY-section organization** instead of literal
   `docs/src/release/` and `docs/src/maintainers/` subdirectories. The amendment
   required every chapter under `docs/src/` and persona organization; mdBook takes
   its sectioning from `SUMMARY.md` headings, not the folder tree, so the 38
   top-level pages stay flat (only the pre-existing `generated/`/`migration/`/
   `patterns/` subdirs kept) — realizing the three reader paths while avoiding the
   relative-link churn that nesting two pages into new subdirs would cause. The
   suggested subdirs are an easy follow-up if you prefer them.
2. **`extract_rfc_index.py` link prefix fix.** The generator emitted RFC links as
   `done/NNN.md`, which never resolved from the generated-doc location (a latent
   pre-existing break). They now emit `../../../rfcs/<folder>/NNN.md`, which
   resolves on disk and when browsing the repo on GitHub, so the docs gate's
   local-link check passes book-wide. A correctness fix adjacent to the move.

## Residuals / notes for review

- The `migration/` SUMMARY parent link points at `migration/template.md` (which
  carries the format + historical-count convention) since there is no
  `migration/README.md`; acceptable as the section landing, trivially swappable
  for a dedicated index page if preferred.
- Some moved pages still contain in-prose backtick path *labels* like
  ``docs/generated/...`` whose **links** already resolve (gate is green). These
  cosmetic labels were not swept to avoid an over-broad prose edit and to respect
  "no semantic rewrite"; a separate label-normalization pass is a clean follow-up
  if wanted.
- mdBook is provided in-sandbox as a prebuilt v0.5.3 binary (no cargo); CI needs
  `mdbook` on PATH for `check_docs.sh` to run its build step.

## State for next cycle

`check.sh --fast` and `check_docs.sh` both green; v0.34.0 packaged. On the
horizon (unchanged): Phase 2B-2 one-projection Shape-A pilot (deferred,
review-gated) and RFC 068 (Invariant Dependency Graph) as the next proposed
candidate.
