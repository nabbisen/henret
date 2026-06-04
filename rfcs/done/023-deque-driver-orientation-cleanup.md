---
title: Deque Driver Orientation Cleanup
rfc: RFC-HENRET-023
status: Implemented (v0.2.1)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-023: Deque Driver Orientation Cleanup

## Motivation

`Henret/Native/DequeModel.lean` used two queue orientations without an
explicit bridge: `DequeModel.toList` reads top → bottom (owner's end at the
list back, removed by `popLast`), while `drivePopB` treated the list front
as the owner's end. The file also referenced `execDemo`, an executable
Henret no longer ships.

## Changes

- `drivePopB` → `driveStackB`: the name now says what it is — an owner-end
  *stack* driver over the owner's-eye view.
- Docstring carries an explicit ORIENTATION NOTE: the driver's view is the
  reverse (`List.reverse`) of `toList`'s orientation; it is a standalone
  fairness model, not an operation of `DequeModel`.
- `execDemo` framing removed; the liveness claim stands on its own.
- All references updated (`Assumptions.lean`, audit script, docs,
  example 09); CHANGELOG notes the rename.

## Acceptance criteria

- [x] No file mixes "top → bottom" and "front is bottom" without an
      explicit translation note.
- [x] `driveStackB_complete` audit-clean (`propext`, `Quot.sound`).
