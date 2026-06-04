# Prior Art: the Runtime Workspace (Stage 0)

Henret's patterns were extracted from a reviewed prototype,
`lean-runtime-workspace`, which is preserved as prior art alongside this
repository. It contained: a `TaskOp` operation grammar with a dual (model /
machine) interpreter, ~45 kernel-checked theorems, four typed FFI axioms, a C
Chase-Lev work-stealing deque with an epoll-based FFI package, and a stress
harness.

## Reused in Henret

- the operation-grammar → pure-interpreter design,
- the executable reference-driver idea,
- model-level lifecycle invariants as the primary proof targets,
- parametric refinement via backend contracts,
- the discipline of *typed, named* assumptions,
- the proof/trust/test classification.

## Explicitly not inherited

- the "runtime foundation" framing and any production-runtime claim,
- Tokio-likeness,
- any correctness claim about the C deque (race-freedom of the C code was
  never proven and is OUTSCOPE for Henret),
- the requirement of a C toolchain: Henret's default build is Lean-only.

The C/FFI material may return as an optional, clearly-bounded backend example
under RFC 010 (implemented): `Henret/Native/` carries the `DequeModel` contract
and the six typed `NativeDeque` axioms, indexed in `docs/assumption-index.md`.
Actual C linkage and conformance tests are planned follow-up work.
