---
rfc: 3
title: Lean-Only Core Package
status: Implemented
implemented_in: v0.1.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: foundation
---

# RFC-HENRET-003: Lean-Only Core Package


## Motivation

Henret's ecosystem value depends on easy adoption. A user should not need native C tooling to learn the core model.

## Scope

This RFC defines the Lean-only package boundary.

## Design

Default import path:

```lean
import Henret
```

should include only Lean modules.

Recommended module tree:

```text
Henret/
  Core/
  Actor/
  Scheduler/
  Refinement/
  Examples/
```

Optional native material should live under:

```text
Henret/Native/
```

or in a separate package.

## Tasks

1. Create root `Henret.lean`.
2. Create Lean-only module tree.
3. Move/adapt pure model code.
4. Remove native dependencies from default build.
5. Add Lean-only tests.
6. Add `lake exe henret-demo` if feasible.

## Acceptance criteria

- `lake build` succeeds for core without native backend.
- `import Henret` does not require native C symbols.
- Examples are Lean-only unless explicitly marked native/optional.

## Implementation note (v0.1.0)

Root Henret.lean imports the Lean-only tree (Core/Actor/Scheduler/Proofs/Refinement/Examples). Default `lake build` and `lake exe henret-demo` need no C toolchain.
