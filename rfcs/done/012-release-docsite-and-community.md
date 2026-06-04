---
title: Release, Docsite, and Community
rfc: RFC-HENRET-012
status: Implemented (v0.1.0)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-012: Release, Docsite, and Community


## Motivation

Henret should be usable by the Lean 4 community, not just the original implementer.

## Release target

First public target:

```text
Henret v0.1.0
```

Scope:

- Lean-only actor/task model,
- executable scheduler semantics,
- basic lifecycle proofs,
- proof/trust/test matrix,
- guided examples,
- optional native backend notes only.

## Tasks

1. Add `CONTRIBUTING.md`.
2. Add `CHANGELOG.md`.
3. Add release checklist.
4. Add issue templates.
5. Add docsite outline.
6. Prepare package metadata.
7. Tag release.

## Acceptance criteria

- Public release is easy to understand.
- Contribution path is clear.
- Release does not overclaim.

## Implementation note (v0.1.0)

CHANGELOG.md, CONTRIBUTING.md, LICENSE (Apache-2.0), NOTICE shipped.
Package metadata in lakefile.lean and lean-toolchain. `lake exe henret-demo`
runs as the acceptance gate. Remaining: Reservoir metadata, issue templates,
mdbook docsite — open for post-v0.1.0.
