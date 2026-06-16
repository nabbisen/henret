# Package Boundary

Henret is deliberately **two separately versioned packages**. This document
says what is in each, where each kind of evidence lives, and how the two are
linked. It is the prose companion to the machine-readable
[`evidence-ledger.yaml`](evidence-ledger.yaml) (RFC 081).

## The two packages

### `henret` — the model package (this tarball)

A pure Lean 4 actor/task scheduler semantics: the `RuntimeState`, the `step`
function and its `RuntimeOp` grammar, the `WellFormed` invariant, every
preservation and reachability proof, the single- and multi-worker bridge
relation, the conformance suite, and the bounded explorer. It is
**kernel-checked, `sorry`-free, and has zero project-specific axioms** beyond
the six trusted `NativeDeque` sequential-spec axioms, which are declared and
audited in-tree.

Everything this package claims is `in_tree_model_proof` or
`in_tree_model_test`: it is present in this checkout and verified by this
tarball's gates (`scripts/check.sh --release`).

### `lean-runtime-workspace/lean-runtime` — the runtime package (sibling)

The concrete work-stealing runtime: the C Chase-Lev deque, the epoll FFI, the
Lean-Runtime bridge code, and the empirical harnesses — differential,
Wing-Gong linearizability, and the partition-invariant stress test. It is a
**separately versioned sibling package**; it is **not** part of the model
checkout or this release tarball.

Its evidence is `sibling_runtime_package` in the ledger and carries
`verified_by_this_tarball: false`. The model-package gates do **not** build or
run it.

## What this means for the honesty ledger

- The model's proofs are unconditional and self-contained: they hold for the
  abstract semantics in every reachable state, independent of any runtime.
- The `NativeDeque` axioms are a **trusted** boundary (tier `TRUSTED`): the
  axiom statements are in-tree and audited as exactly six, but they *trust*
  the out-of-tree C implementation on the sequential-specification axis. The
  concurrent-safety axis (C11 data-race freedom) is `OUTSCOPE` — it needs
  Iris-style separation logic and is not claimed.
- The concurrent harnesses are **tested out-of-tree** (tier `TESTED`,
  location `sibling_runtime_package`). `TRUSTED` and `TESTED` are never
  collapsed: the first is a design assumption, the second is empirical
  evidence in a different package.

This tarball therefore must not state, or imply, that it verifies the runtime
`runtimeTests` tier. The accurate posture is: *runtime evidence exists in a
separately versioned package and is not verified by this tarball's gates.*
`scripts/forbidden_claim_check.py` enforces that posture.

## The toolchain link

Both packages pin the **same Lean toolchain** (`lean-toolchain`, Lean
v4.15.0) so the bridge relation in the model package and the queue model in
the runtime package typecheck against the same compiler. That shared
toolchain is the only hard coupling between the two; there is no build-time
dependency in either direction.

## See also

- [`evidence-ledger.yaml`](evidence-ledger.yaml) / [`.md`](evidence-ledger.md)
  — the machine-readable per-claim ledger.
- [`proof-trust-test-matrix.md`](proof-trust-test-matrix.md) — the exhaustive
  in-tree claim matrix, with an evidence-location column.
- [`assumption-index.md`](assumption-index.md) — the complete axiom budget.
