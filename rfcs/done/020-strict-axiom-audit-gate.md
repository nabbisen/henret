---
title: Strict Axiom Audit Gate
rfc: RFC-HENRET-020
status: Implemented (v0.2.1)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-020: Strict Axiom Audit Gate

## Motivation

The v0.2.0 audit grepped for `NativeDeque|sorryAx`, which would miss a new
project axiom with any other name (e.g. `axiom UnsafeRuntimeMagic`).
Henret's public value rests on trust-boundary honesty, so the audit must be
exact.

## Design

`scripts/axiom_audit.py` parses `#print axioms` output (handling wrapped
lines) and checks each theorem's axiom set against an explicit allowlist:

- Core and pure-native theorems: subset of `{propext, Quot.sound}`.
- `nativeDequeModel_qRun_tracks`: must *contain* all six `NativeDeque`
  axioms and be a subset of those six plus `propext`, `Quot.sound`,
  `Classical.choice`.
- Theorems printed but not allowlisted fail; allowlisted theorems not
  printed fail. Auditing is intentional in both directions.

`scripts/check.sh` is the canonical test command (gate 5 runs the audit;
gate 6 greps for stale documentation phrases per RFC 021).

## Acceptance criteria

- [x] A deliberate extra project axiom fails the audit (validated with a
      fabricated `UnsafeRuntimeMagic` dependency).
- [x] A missing expected native axiom fails the audit.
- [x] Expected axiom sets documented per theorem (in the allowlist itself
      and `docs/assumption-index.md`).

## Implementation note (v0.2.1)

`scripts/axiom_audit.py`, `scripts/check.sh` gates 5–6. CI unchanged: it
runs `scripts/check.sh`.
