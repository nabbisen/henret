# Checkpoint handoff — RFC 094 follow-ups into v0.34.0

**For:** architect review
**Release:** `henret-v0.34.0.tar.gz` (consolidated; v0.34.0 was not yet published)
**Scope:** documentation-gate follow-ups from the RFC 094 implementation review.
No model, proof, or theorem change. Axioms unchanged; public theorem surface
unchanged (101 names). `check.sh --fast` and `check_docs.sh` both green.

## What shipped

Two of the four review follow-ups — the two with actionable scope. Issues 3 and 4
deferred exactly as the review directed.

### Issue 2 (prioritized) — mdBook version pin + CI determinism

- The book targets the mdBook 0.5 line (last verified with 0.5.3). No separate
  pin file is kept — that was judged heavier than a low-stakes docs gate needs.
- `scripts/check_docs.sh` reports the detected mdBook version, then builds.
- New `.github/workflows/docs.yml` — a **separate** workflow from the Lean
  release gate (`ci.yml`) — installs the latest mdBook release from its prebuilt
  binary and runs `scripts/check_docs.sh` on PRs, pushes to `main`, and tags.
- Pinned version recorded in `docs/src/release-checklist.md`.

### Issue 1 — migration landing page

- New `docs/src/migration/README.md`: explains the guides, links the template and
  every version-to-version guide, and states the historical-count convention.
- `docs/src/SUMMARY.md` migration parent moved from `migration/template.md` to
  `migration/README.md`; the template is now a child page. Orphan check passes
  (57 pages reachable; 196 local links resolve).

### Deferred (as directed)

- **Issue 3** — reader-facing path-label normalization: kept a separate
  low-priority pass, not mixed into the layout work; historical CHANGELOG entries
  left untouched.
- **Issue 4** — flat `docs/src/` scale: no action; revisit subdirectories only if
  the top-level page list becomes hard to navigate.

## Evidence

`lakefile.lean` stays at `v0.34.0`; the v0.34.0 CHANGELOG entry now records both follow-ups and
the two deferrals. No RFC status change (these are refinements within the already
`done` RFC 094, framed by the review as follow-up issues, not new RFCs); matrix
claim 237 and the proof-index RFC 094 section already cover the docs gate, so no
new claim was added. Package excludes `docs/book/` (mdBook output, git-ignored).

## State for next cycle

Both gates green; v0.34.0 (consolidated) packaged. Ready to proceed to the next planned item:
Phase 2B-2 one-projection Shape-A pilot (deferred, review-gated) or RFC 068
(Invariant Dependency Graph) as the next proposed candidate.
