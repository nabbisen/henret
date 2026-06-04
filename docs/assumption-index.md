# Assumption Index

## Lean-only core (`import Henret`)

Zero project-specific assumptions.

`#print axioms` on every exported theorem reports only Lean's standard kernel
axioms `propext` and `Quot.sound` (and `Classical.choice` for theorems about
opaque types).

Audit script:
```lean
#print axioms step_preserves_terminal    -- propext
#print axioms drivePopB_complete         -- propext, Quot.sound
#print axioms wake_twice_invalid         -- propext, Quot.sound
```

## Optional native layer (`import Henret.Native.Assumptions`)

Six typed axioms for the `NativeDeque` backend (RFC 010, implemented v0.1.0):

| Axiom | What it trusts |
|---|---|
| `NativeDeque.toList_empty` | Empty deque observes as `[]` |
| `NativeDeque.toList_push` | Push appends to the bottom |
| `NativeDeque.steal_val` | Steal returns the correct head value |
| `NativeDeque.steal_rest` | Steal leaves the correct tail |
| `NativeDeque.pop_val` | Pop (owner) returns the correct last value |
| `NativeDeque.pop_rest` | Pop leaves the correct remainder |

These are the *entire* trust surface for the native deque.  They appear
explicitly in `#print axioms nativeDequeModel_qRun_tracks`.

### What is NOT claimed

- C memory race-freedom (concurrent steal + push)
- OS scheduling fairness
- Wall-clock timer accuracy

### Conformance testing (planned follow-up work)

Each axiom should be mapped to a differential test comparing `NativeDeque`
against `listDeque` on representative programs.  See
`docs/native-backend-boundary.md`.
