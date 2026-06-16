---
rfc: 0
title: RFC Lifecycle Policy
status: Implemented
implemented_in: v0.1.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: governance
---

# RFC 000 — RFC Lifecycle Policy

This file mirrors the project-level policy `000-rfc-lifecycle-policy.md`.

1. The folders `rfcs/proposed/`, `rfcs/done/`, and `rfcs/archive/` are the
   source of truth for RFC state.
2. RFC files are named `NNN-slug.md`. Numbering starts at `001` (this policy
   itself is `000`); numbers are never reused.
3. Each RFC carries a YAML front-matter block as its single machine-readable
   metadata (RFC 085). Mandatory fields: `rfc` (integer), `title`, `status`
   (one of `Draft | Proposed | Implemented | Withdrawn | Superseded`),
   `implemented_in` (`vMAJOR.MINOR.PATCH` when `status: Implemented`, else
   `null`), `supersedes`, `superseded_by`, `depends_on`, `blocks`
   (bare-integer RFC-number lists, e.g. `[80, 84]`), and `category`. The
   `status` value must mirror the containing folder: `proposed/` →
   `Draft`/`Proposed`; `done/` → `Implemented`; `archive/` →
   `Withdrawn`/`Superseded`.
4. Moving an RFC between folders and updating `rfcs/README.md` happen in the
   same commit.
5. Completed RFCs are never deleted; superseded ones move to `archive/` with a
   `superseded_by` entry and `status: Superseded`.
6. `scripts/rfc_metadata_check.py` enforces this schema as a release gate
   (RFC 085).
