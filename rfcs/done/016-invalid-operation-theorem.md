---
rfc: 16
title: Invalid Operation Theorem
status: Implemented
implemented_in: v0.2.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: proofs
---

# RFC-HENRET-016: Invalid Operation Theorem

## Motivation

The docs referenced `step_invalid_unchanged` ("an invalid operation never
mutates state") but the theorem did not exist (v0.1.0 review must-fix 6).
The property held by construction in every branch of `step`; this RFC makes
it a checked theorem so it cannot silently regress as operations evolve.

## Design

```lean
theorem step_invalid_unchanged {s : RuntimeState} {op : RuntimeOp}
    (h : (step s op).2 = .invalid) : (step s op).1 = s
```

Proof by full case analysis: every valid branch returns a non-`.invalid`
result (contradiction with `h`); every invalid branch returns `s` literally.
The new monotonic-tick guard (RFC 015) added one more invalid branch, which
the theorem covers.

## Acceptance criteria

- [x] Theorem stated exactly as documented and kernel-checked.
- [x] Covers all ten operations including the new tick guard.
- [x] Indexed in the proof index and matrix.

## Implementation note (v0.2.0)

`Henret/Proofs/Lifecycle.lean`, next to the terminal-preservation theorems
whose docstring referenced it.
