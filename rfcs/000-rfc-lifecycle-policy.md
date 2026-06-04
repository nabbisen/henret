---
title: RFC Lifecycle Policy
rfc: RFC-HENRET-000
status: Active
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-000: RFC Lifecycle Policy

This file mirrors the project-level policy `000-rfc-lifecycle-policy.md`.

1. The folders `rfcs/proposed/`, `rfcs/done/`, and `rfcs/archive/` are the
   source of truth for RFC state.
2. RFC files are named `NNN-slug.md`. Numbering starts at `001`; numbers are
   never reused.
3. The `status` front-matter field must mirror the containing folder
   (`Proposed`, `Implemented (vX.Y.Z)` in `done/`, `Archived`).
4. Moving an RFC between folders and updating `rfcs/README.md` happen in the
   same commit.
5. Completed RFCs are never deleted; superseded ones move to `archive/` with a
   superseded-by note.
