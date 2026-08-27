---
rfc: 101
title: Documentation and RFC Index Integrity
status: Implemented
implemented_in: v0.34.6
supersedes: []
superseded_by: []
depends_on: [52, 75, 84, 85, 94]
blocks: [70, 74, 79, 102]
category: documentation
---

# RFC 101 — Documentation and RFC Index Integrity

## Status

Implemented in v0.34.6. The root and generated-book RFC indexes are produced
from RFC front matter by `scripts/extract_rfc_index.py` (gated, `--check`),
with `scripts/markdown_link_check.py` and `scripts/doc_count_check.py`
covering repository-wide link and count drift; closed through the review
chain in `.git-exclude/reviewed/004`–`005`. This same patch is the first to
exercise the mechanism it delivers.

**Deferred (RFC 000 "Granularity of transitions").** Two acceptance criteria
ship unenforced: no gate derives the release-version string or the RFC-lifecycle
counts used in current-claim prose, so "all current documents agree on vX.Y.Z"
and "the roadmap contains no implemented RFC in an open queue" remain
review-enforced rather than machine-enforced. The v0.34.6 review found exactly
that drift in `docs/src/roadmap.md` behind a green gate run. Risk R6 therefore
stays open (downgraded to not-release-blocking) until a version/lifecycle
consistency check exists; closing it is follow-up work for M2.

## Summary

Repair current-claim drift and make the repository RFC index, model counts,
roadmap facts, test inventory, and Markdown links mechanically consistent with
their authoritative sources.

## Motivation

Live documents describe 29 rather than 33 `WellFormed` fields, the roadmap
describes v0.27.0/28 operations and queues completed work, the root RFC index
places implemented RFCs under Proposed, and the test index understates demo
coverage. Existing gates accept these contradictions because structured values
and the root RFC index are outside their effective coverage.

## Non-goals

- Do not redesign model semantics.
- Do not treat historical handoffs/reviews as live current-state documents.
- Do not maintain a second hand-written RFC lifecycle table.

## Proposed design

1. Define current-claim documents and historical-document exclusions
   explicitly.
2. Repair assurance, guided-tour, profile, integration, roadmap, test-index,
   release, contributing, risk-register, and package metadata statements.
3. Generate both `docs/src/generated/rfc-index.md` and `rfcs/README.md` from RFC
   front matter, with folder location as lifecycle authority.
4. Strengthen count checking using structured extraction so Markdown emphasis,
   backticks, and prose variants cannot evade it.
5. Extend the link checker to all current repository Markdown, including the
   root RFC index; exclude historical records only through a documented list.
6. Reopen risk R6 until the new checks demonstrate that representative stale
   fixtures fail.
7. Treat `depends_on` as the authoritative schedule relation. Permit `blocks`
   as an optional forward hint only when the target declares the inverse
   dependency, and fail metadata validation on a one-sided `blocks` edge.

## Implementation tasks

1. Correct every live 29/28/stale-version claim and the ten-scenario test count.
2. Generalize the RFC index generator and replace the hand-maintained root
   index.
3. Add structured current-fact metadata or reuse `Henret.Meta.Docs` for version,
   grammar, invariant, scenario, and RFC counts.
4. Extend link/count self-tests with regressions from the architect review.
5. Replace `<REPO-URL-PLACEHOLDER>` in `lakefile.lean`.
6. Update RFC 000 and contributor guidance for generated-index operation.
7. Add dependency-edge consistency fixtures to the RFC metadata checker.

## Acceptance criteria

- All current documents agree on v0.34.6, 29 operations, 10 task states, 10
  results, 33 `WellFormed` fields, and ten demo scenarios where counts are used.
- `rfcs/README.md` is generated or checked from front matter and has exactly one
  section for each lifecycle state.
- Every current repository Markdown link resolves.
- Fixtures using bold/backticked stale counts fail the count gate.
- The roadmap contains no implemented RFC in an open queue.
- Every declared `blocks` edge has a matching inverse `depends_on` edge, and a
  one-sided fixture fails the metadata gate.
- Risk R6 remains open until these regression checks pass in CI.

## Risks

Generated current facts must not rewrite historical records. The generator and
link checker need an explicit current-versus-historical document policy.
