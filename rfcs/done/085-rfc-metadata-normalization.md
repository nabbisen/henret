---
rfc: 85
title: RFC Metadata Normalization
status: Implemented
implemented_in: v0.17.1
supersedes: []
superseded_by: []
depends_on: []
blocks: [80, 84]
category: governance
---

# RFC 085 — RFC Metadata Normalization

## Status

Implemented in **v0.17.1**. Originally a strategic RFC approved in the
v0.17.0 audit review (item A4, decision **B — normalize to YAML front
matter**, priority **P2**); amendments 085-A..E and the final-pass
amendments 085-1..5 applied from the RFCs 080-086 reviews. Delivered as a
single mechanical migration: all 87 RFCs (including this policy's RFC 000)
carry canonical front matter, `scripts/rfc_metadata_check.py` enforces the
schema as `check.sh` gate 10, and RFC 000 mandates the format.

## Summary

Normalize every RFC's status metadata to a single machine-readable YAML
front-matter block, migrate the RFCs that use other shapes, add a
dependency-light status linter, and update RFC 000 to mandate the format.
The status value set is the **RFC 000 lifecycle**, not an expanded set.
This pairs with RFC 075/084: the front matter is the source for the
generated RFC index.

## Motivation

The audit found three coexisting status styles across the 55 done RFCs:
YAML-ish `status:` (34), the `**Status.**` shape RFC 000 *illustrates* (10),
and `## Status` headers (11). All carry a valid status, but three formats
force any status tooling to parse three shapes and make a generated index
harder.

## Goals

- One canonical, machine-readable status format across all RFCs.
- A linter that validates every RFC's front matter (dependency-light).
- RFC 000 updated to mandate the chosen format.

## Non-goals

- Renumbering any RFC (RFC 000: numbers are permanent).
- Mixing semantic edits into the migration (mechanical commit only).
- Expanding the lifecycle state set (see 085-A).

## Format

```yaml
---
rfc: 055
title: Structured Cancellation and Shutdown
status: Implemented
implemented_in: v0.17.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: execution-management
---
```

## 085-A — Allowed status values = the RFC 000 lifecycle

The closed set is exactly the RFC 000 state machine — **no new states**:

```text
Draft | Proposed | Implemented | Withdrawn | Superseded
```

Note: the RFCs 080-086 review suggested also allowing `Accepted`,
`Rejected`, and `Deferred`. These are **not** part of Henret's lifecycle:
RFC 000 treats `Accepted` as an optional 5-folder-variant state this
project did not adopt, has no `Rejected` ("rejection" = `Withdrawn`), and
has no `Deferred`. Introducing them would change the lifecycle policy and
must be done as an explicit amendment to RFC 000, not via this schema.

## 085-B — Null / empty values

```yaml
# proposed:    implemented_in: null
# implemented: implemented_in: v0.x.y
# superseded:  status: Superseded   superseded_by: [082]
# empty lists: supersedes: []   superseded_by: []   depends_on: []   blocks: []
```

## 085-C — Dependency metadata

```yaml
depends_on: [80, 81]    # bare integers (085-2); rendered "RFC 080", "RFC 081"
blocks: []
```

Supports roadmap generation and prevents accidental sequencing errors.

## 085-D — Linter validations

```text
- no duplicate rfc number
- filename number matches front-matter rfc number
- filename slug matches title under slug normalization
- supersedes / superseded_by / depends_on / blocks point to existing RFCs
- implemented_in matches the version pattern when status = Implemented
- status is one of the 085-A closed set
- status value is consistent with the folder (RFC 000: folder is source of
  truth — proposed/ => Proposed/Draft; done/ => Implemented; archive/ =>
  Withdrawn/Superseded)
```

## 085-E — Migration scope

```text
APPLIES TO:  rfcs/done/   rfcs/proposed/   rfcs/archive/   rfcs/README.md
DOES NOT:    handoffs, reviews, docs/
```

(There is no `rfcs/rejected/`; withdrawn/superseded RFCs live in
`rfcs/archive/` per RFC 000.)

## Final-pass amendments (RFCs 080-086 v2 review)

**085-1 — Accepted YAML subset (so a stdlib parser is safe).**

```text
- scalar strings; integer rfc numbers
- lists of integers in a single chosen form (see 085-2)
- no nested objects; no multiline scalars
```

**085-2 — Canonical RFC-number format in lists.** Use bare integers and
render with zero-padding in generated docs:

```yaml
depends_on: [80, 81]      # rendered as "RFC 080", "RFC 081"
```

(Leading-zero integers are parser-fragile; bare ints are canonical here.)

**085-3 — Exact version pattern.**

```text
implemented_in: vMAJOR.MINOR.PATCH         e.g. v0.17.0
optional pre-release suffix allowed:        e.g. v0.17.0-alpha.1
```

**085-4 — Folder/status consistency (RFC 000 source-of-truth).**

```text
rfcs/proposed/ may contain Draft or Proposed
rfcs/done/     must contain Implemented
rfcs/archive/  may contain Withdrawn or Superseded
```

**085-5 — Slug normalization.** `lowercase, ASCII hyphenation, remove
punctuation, collapse hyphens`; an explicit override is allowed when the
title contains symbols (e.g. `C++`, `IO.RealWorld`).

## Acceptance criteria

```text
- All done/proposed/archive RFCs carry valid front matter in the 085-A set
  and the 085-1 YAML subset.
- Dependency lists use bare-integer RFC numbers (085-2); versions match the
  085-3 pattern.
- The status linter (085-D) enforces folder/status consistency (085-4),
  slug normalization (085-5), unique ids, and cross-reference existence; it
  runs in check.sh (RFC 080).
- RFC 000 updated to mandate the front-matter block.
- The generated RFC index (RFC 084) consumes this metadata.
- One mechanical migration commit, no semantic edits.
```

## Concern

Keep the linter small and dependency-light: Python standard library plus a
minimal front-matter parser is enough for this simple schema. Do not pull a
large YAML dependency into the project for this.

## Priority and sequencing

P2 by release-impact, but **first in the implementation order** per the v2
review: the front matter is the source for RFC-index extraction (RFC 084)
and provides structured metadata the rest of the wave builds on. May be
batched with RFC 080's CI work.

## References

- v0.17.0 audit review item A4; RFCs 080-086 review amendments 085-A..E.
- RFC 000 (RFC lifecycle policy) — to be amended (mandate the format).
- RFC 075 / RFC 084 (doc extraction) — consume this metadata.
