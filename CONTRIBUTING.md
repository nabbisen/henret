# Contributing to Henret

## Ground rules

1. **Lean-only default.** `lake build` and the demo must never require a C
   compiler, native deque, epoll, or OS-specific reactors. Native material is
   optional and isolated (RFC 010).
2. **No overclaiming.** Changes that imply production-runtime readiness,
   native-thread correctness, or blur model vs. implementation are rejected.
3. **Matrix discipline.** Any PR adding/changing a correctness claim must
   update `docs/proof-trust-test-matrix.md` and the relevant index
   (`proof-index.md`, `assumption-index.md`, `test-index.md`).
4. **Trust hygiene.** No `sorry`. New axioms only behind the RFC 010 boundary,
   named, indexed, and conformance-tested.
5. **Small examples.** Each example teaches one concept and stays short.

## Workflow

- Substantive changes start as an RFC in `rfcs/proposed/` following
  `rfcs/000-rfc-lifecycle-policy.md` (NNN-slug.md, numbers never reused,
  Status mirrors the folder, README index updated in the same commit).
- Build gate: `lake build && lake exe henret-demo` must pass (demo exits
  non-zero on regression).
- Preferred additions: mailbox semantics, supervision, cancellation,
  backpressure, bounded queues, request/reply, select/receive, logical timers.
- Deferred: OS process lifecycle, native threads, real epoll/io_uring,
  lock-free C proofs, scheduler performance work.

## Dev environment

Toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.15.0`); install
via elan. If your network blocks `release.lean-lang.org`, download the
toolchain tarball from the Lean GitHub releases and unpack it under
`~/.elan/toolchains/leanprover--lean4---v4.15.0/`.
