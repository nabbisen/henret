---
rfc: 10
title: Optional FFI Backend Boundary
status: Implemented
implemented_in: v0.1.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: ffi
---

# RFC-HENRET-010: Optional FFI Backend Boundary


## Motivation

The existing FFI/deque work is valuable, but it should be optional and educational, not the center of Henret's first release.

## Scope

This RFC covers optional native backend material.

## Design

Native backend material should be isolated under:

```text
Henret.Native
```

or separate packages such as:

```text
henret-native
henret-cdeque
```

## Trust-boundary rule

Typed assumptions are allowed only if they are:

- named,
- documented,
- indexed,
- mapped to tests,
- excluded from Lean-only proof claims.

## Tasks

1. Isolate native modules.
2. Preserve typed assumption files.
3. Add conformance map.
4. Add optional native build instructions.
5. Add warning that C race-freedom is not proven by Lean.

## Acceptance criteria

- Default Henret usage is Lean-only.
- Advanced users can study native backend boundary discipline.
- Documentation does not imply full verification of C concurrency.

## Implementation note (v0.1.0)

`Henret/Native/DequeModel.lean` — `DequeModel` contract (6-law, `toList`-based,
analogous to `MailboxBackend`), `listDeque` reference implementation (all laws by
`rfl`), `qRun_tracks` (any backend satisfying the contract tracks the reference —
PROVEN, only `propext`), `drivePopB_complete` (LIFO owner-pop driver liveness —
PROVEN).

`Henret/Native/Assumptions.lean` — 6 typed axioms for `NativeDeque` (the entire
trust surface for a C Chase-Lev deque), `nativeDequeModel : DequeModel` (closes the
contract definitionally), `nativeDequeModel_qRun_tracks` (PROVEN, depends only on
the 6 named axioms).

Separation is at the import level: `import Henret` never pulls in native axioms.
Build: `lake build HenretNative`. Axiom audit: see `docs/assumption-index.md`.
Actual `@[extern]` C linkage and conformance differential tests are post-v0.1.0.

## Amendment (v0.2.1, RFC 023)

`drivePopB` renamed to `driveStackB` with an explicit orientation note: the
driver works on the owner's-eye (list-front) view, the reverse of
`DequeModel.toList`'s top → bottom orientation. The stale `execDemo` framing
was removed.
