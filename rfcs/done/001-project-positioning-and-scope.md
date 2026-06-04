---
title: Project Positioning and Scope
rfc: RFC-HENRET-001
status: Implemented (v0.1.0)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-001: Project Positioning and Scope


## Motivation

Henret needs a clear ecosystem identity before implementation continues. The previous work was reviewed as a runtime foundation, but the confirmed purpose is broader and more Lean-first: executable actor/task runtime models and refinement patterns for Lean 4.

## Scope

This RFC defines what Henret is and what it is not.

## Decision

Henret is:

```text
A Lean 4 package for executable actor/task runtime models,
scheduler semantics, refinement patterns, and auditable backend boundaries.
```

Henret is not:

```text
A production async runtime.
A Tokio clone.
A process manager.
A native thread library.
A fully verified lock-free scheduler.
```

## Design requirements

1. README must open with the Henret purpose.
2. Non-goals must be visible.
3. Actor/task semantics must be named as the first modeling domain.
4. Native backend work must be optional.
5. The proof/trust/test distinction must be central.

## Documentation tasks

- Create `docs/project-positioning.md`.
- Add public one-sentence summary.
- Add scope and non-goal table.
- Add migration note from previous runtime workspace.

## Acceptance criteria

- A new reader does not confuse Henret with a process manager or native thread library.
- Public docs consistently use the actor/task runtime model framing.

## Implementation note (v0.1.0)

Implemented via README.md opening, docs/project-positioning.md (one-sentence summary, scope/non-goal table, migration note), and docs/prior-art-runtime-workspace.md.
