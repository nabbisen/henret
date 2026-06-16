---
rfc: 2
title: Package Identity and Naming
status: Implemented
implemented_in: v0.1.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: foundation
---

# RFC-HENRET-002: Package Identity and Naming


## Motivation

A Lean ecosystem package needs a stable name across repository, Lake package, and namespace.

## Decision

Use:

```text
Project name:       Henret
Repository name:    henret
Lake package name:  henret
Lean namespace:     Henret
Subtitle:           Executable actor and task runtime models for Lean 4
```

## Naming policy

Henret should be treated as a coined project/package name in public documentation. Public docs should not rely on etymology. The subtitle and examples should explain the project.

## Module naming

Use:

```lean
namespace Henret
```

Recommended import roots:

```lean
import Henret.Core
import Henret.Actor
import Henret.Scheduler
import Henret.Refinement
import Henret.Examples
```

## Tasks

1. Rename package to `henret`.
2. Rename namespace to `Henret`.
3. Rename docs and examples.
4. Remove stale generic names from the roadmap.
5. Add `docs/naming-and-scope.md`.

## Acceptance criteria

- No public-facing file calls the package `lean-runtime-foundation`, `kinema`, `actra`, or generic ecosystem starter.
- Lake package and Lean namespace agree with this RFC.

## Implementation note (v0.1.0)

Lake package `henret`, namespace `Henret`, repo `henret`; docs/naming-and-scope.md added; no stale generic names remain.
