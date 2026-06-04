---
title: Release Gate and CI
rfc: RFC-HENRET-017
status: Implemented (v0.2.0)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-017: Release Gate and CI

## Motivation

The v0.1.0 release was verified by an ad-hoc command sequence. A release
gate makes "what must be green before an archive is cut" explicit,
reproducible, and CI-enforceable.

## Design

A single script, `scripts/check.sh`, that fails fast on any of:

1. `lake build` — Lean-only core + demo executable.
2. `lake build HenretNative` — optional native layer.
3. `lake exe henret-demo` — self-checking regression scenarios.
4. Every `examples/NN_*.lean` compiles via `lake env lean`.
5. Axiom audit — the flagship theorems depend on exactly the standard
   kernel axioms (and the native theorem on exactly the six declared
   `NativeDeque` axioms); the audit greps `#print axioms` output.

`.github/workflows/ci.yml` runs the same script on push/PR, installing the
pinned toolchain from `lean-toolchain`. The script is the source of truth;
CI is just a runner for it.

## Acceptance criteria

- [x] `scripts/check.sh` runs all five gates and exits non-zero on failure.
- [x] CI workflow file invoking the script.
- [x] Release procedure documented: gate green → archive `henret-vX.Y.Z.tar.gz`.

## Implementation note (v0.2.0)

`scripts/check.sh`, `.github/workflows/ci.yml`. The axiom audit writes a
temporary Lean file, compiles it, and compares against expected axiom sets.
