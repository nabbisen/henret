# Native Backend Boundary (RFC 010)

Henret's trust discipline for optional native backends.

## The principle

> Trust exactly as little as necessary.  Name it.  Test it.  Keep it separate.

The Lean-only core (`import Henret`) makes **zero** project-specific
assumptions.  When a native C backend is connected, its trust surface is
bounded to a small, named set of typed axioms — not "the C code is correct,"
but "these 6 specific behavioral laws hold."

## The pattern (implemented in `Henret/Native/`)

```text
Step 1: opaque operations
  NativeDeque.empty, push, steal, pop, toList (noncomputable)

Step 2: 6 typed axioms — the entire trust surface
  NativeDeque.toList_empty      (ASSUMED)
  NativeDeque.toList_push       (ASSUMED)
  NativeDeque.steal_val         (ASSUMED)
  NativeDeque.steal_rest        (ASSUMED)
  NativeDeque.pop_val           (ASSUMED)
  NativeDeque.pop_rest          (ASSUMED)

Step 3: DequeModel instance
  nativeDequeModel : DequeModel
  (definitional, no further trust needed)

Step 4: downstream theorems are PROVEN
  nativeDequeModel_qRun_tracks  (PROVEN given the 6 axioms)
  nativeDequeModel_driveComplete (PROVEN, no native axioms at all)
```

## Axiom audit

```
#print axioms nativeDequeModel_qRun_tracks
→ [propext, Classical.choice,
   NativeDeque.toList_empty, NativeDeque.toList_push,
   NativeDeque.steal_val,    NativeDeque.steal_rest,
   NativeDeque.pop_val,      NativeDeque.pop_rest]

#print axioms step_preserves_terminal
→ [propext]     ← core is unaffected by the native layer
```

The separation is enforced at the **import level**.  The native modules live
in `Henret/Native/` but are NOT imported by `Henret.lean`.  Users opt in:

```lean
import Henret.Native.DequeModel   -- pure, kernel-checked
import Henret.Native.Assumptions  -- declares the 6 axioms
```

Build the native layer: `lake build HenretNative`

## What is NOT claimed (OUTSCOPE)

* C memory race-freedom: concurrent `steal` + `push` has no representation in
  Lean's type theory.  Requires Iris-style concurrent separation logic.
* OS scheduling fairness, wall-clock timer accuracy.
* Correctness of the C code itself: the axioms express *what* is trusted;
  conformance differential tests exercise *whether* it holds at runtime.

## Prior art connection

The prototype workspace (`lean-runtime-workspace`) used four IO-level axioms
(`spec_push`, `spec_steal`, `spec_pop`, `spec_snapshot`) over a `Deque` opaque
type bound to `lean_cl_*.c` via `@[extern]`.  Henret v0.1.0 generalizes this
to pure-state `DequeModel` laws (6 laws, no IO monad required for the spec),
and defers the actual `@[extern]` C linkage to the planned follow-up work.

## Conformance testing (planned follow-up work)

Each axiom should be paired with a conformance test that exercises the C deque
against `listDeque` using differential testing (`progDiff`/`injectDiff` in the
prototype).  Those tests don't prove the axiom — they are evidence that
justifies trusting it.  They should be indexed in `docs/test-index.md`.
