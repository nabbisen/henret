# Release Policy

This policy governs versioning, changelog discipline, and what may change
between releases. It is conservative by design and holds until RFC 052
(semantic-extension governance) formalises a stronger API-stability
contract.

## Versioning (pre-1.0, conservative)

Henret is pre-1.0; the leading `0.` signals that the public surface may
still move. Within that, version bumps are classified:

| Change | Bump | Examples |
|---|---|---|
| **Patch** (`0.x.Y+1`) | docs, tests, tooling, non-public helper lemmas, renderers | proof-engineering notes; a new private lemma; a new example |
| **Minor** (`0.X+1.0`) | a new public theorem, a new example, an additive module, a new operation or state | RFC 049 (added `fail`/`restartOne`); RFC 045 (trace layer) |
| **Breaking** | a change to `RuntimeOp`, `RuntimeState`, `StepResult`, or `TaskState` that alters existing behavior, or a theorem rename | a removed operation; a changed `step` result |

Note that *additive* grammar changes (a new `RuntimeOp` constructor that
does not alter the behavior of existing operations) are treated as minor,
because exhaustive `match` in downstream code is the only thing that
breaks, and that break is mechanical and compiler-caught. A grammar
change of any kind requires migration notes (see below).

## Changelog policy

`CHANGELOG.md` is kept in **descending version order** (newest first).
Each release entry:

1. names the RFC and the version;
2. separates **semantics** (model/proof changes) from **docs/tooling**;
3. states the axiom-budget impact explicitly (the expectation is
   "unchanged — only `propext`, `Classical.choice`, `Quot.sound`");
4. links the example(s) and doc(s) that demonstrate the change.

A change that does not alter the model or the proof corpus says so
plainly, so a reader can tell semantics from polish at a glance.

## Migration notes

Any change to the operation grammar (`RuntimeOp`), the state shape
(`RuntimeState`), the result type (`StepResult`), or the task-state enum
(`TaskState`) ships with a migration note under `docs/migration/`, even
when the change is additive. The note tells a downstream consumer exactly
which `match` arms or field accesses need updating. Use
`docs/migration/template.md` as the starting point.

## Claim classification

Every user-facing correctness claim is classified in
`docs/proof-trust-test-matrix.md` as PROVEN (kernel-checked), ASSUMED
(a named axiom), TESTED (a harness, not a proof), or OUTSCOPE. Release
notes must not present a TESTED or ASSUMED claim as PROVEN.

## What a release does not promise

Until RFC 052 is accepted, no release promises API stability: theorem
names, module boundaries, and the operation grammar may change between
minor versions. The proof/trust/test matrix and the axiom budget are the
stable contract — what is proven stays proven, and the axiom set does not
grow silently.
