---
title: Documentation Consistency Sweep
rfc: RFC-HENRET-018
status: Implemented (v0.2.0)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-018: Documentation Consistency Sweep

## Motivation

The v0.1.0 review found two classes of documentation drift (must-fixes 1
and 7): lifecycle diagrams that did not match the model (`new` and `yielded`
are directly schedulable, but docs showed a linear `new -> ready -> running`
chain), and native-layer docs still describing RFC 010 as proposed/future
after it shipped.

## Design

One sweep, one consistent wording. Lifecycle docs now show the actual
transition table (spawn/schedule/yield/sleep/wake/tick/complete/cancel) and
state explicitly that `new`, `ready`, `yielded` are all runnable. Native
wording is standardized everywhere to:

> The Lean-only core has zero project-specific assumptions. The optional
> native-boundary module declares six project-specific axioms. Actual C
> linkage and conformance tests are planned follow-up work.

## Touched

`Henret/Actor/Task.lean` docstring, `docs/guided-tour.md`,
`examples/01_task_lifecycle.lean`, `README.md`,
`docs/prior-art-runtime-workspace.md`, `docs/assumption-index.md`,
`docs/native-backend-boundary.md`, `docs/proof-trust-test-matrix.md`,
`examples/README.md`.

## Acceptance criteria

- [x] No remaining `rfcs/proposed/010` links or "RFC 010 (proposed)" text.
- [x] Lifecycle docs match `step`'s actual transitions.
- [x] Standard native wording everywhere the boundary is described.

## Implementation note (v0.2.0)

Performed as part of the v0.2.0 review-resolution change, together with
`docs/reviews/v0.1.0-review-resolution.md` which maps each review must-fix
to its fix.
