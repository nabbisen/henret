---
rfc: 48
title: Bounded Model Explorer and Shrinker
status: Implemented
implemented_in: v0.14.1
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: conformance
---

# RFC 048 — Bounded Model Explorer and Shrinker

## Status

Implemented (v0.14.1).

## Summary

Add a bounded explorer that enumerates small Henret operation sequences, checks
semantic properties, and reports minimal counterexamples. This is not a
substitute for proofs. It is a development tool that finds missing assumptions,
misdocumented semantics, and regressions before they become proof obligations.

## Motivation

Henret's semantics are growing: waiting, timers, parenthood, envelopes, bridge
translation, and future multi-wait behavior. Proofs cover known claims, but model
design often benefits from exhaustive search over small executions.

A bounded explorer can answer questions like:

- is there any sequence where a waiting task is not in a waiter queue?
- can a message occurrence id appear twice?
- can a child parent chain cycle?
- can a bridge translation mismatch arise in fewer than five operations?
- does a new operation violate an expected no-effect property?

## Non-goals

This RFC does not:

- replace theorem proofs;
- claim unbounded correctness;
- search arbitrary Lean terms;
- use external SMT solvers in the first version.

## Proposed design

### Operation generator

Define finite domains:

```lean
structure SmallWorld where
  maxTask  : Nat
  maxActor : Nat
  maxMsg   : Nat
  maxTime  : Nat
```

Generate candidate operations:

```lean
def genOps : SmallWorld → List RuntimeOp
```

Generate operation sequences up to depth `d`:

```lean
def genPrograms : SmallWorld → Nat → List (List RuntimeOp)
```

### Property checker

Define executable boolean checkers corresponding to key invariants:

```lean
def checkWellFormedBool : RuntimeState → Bool

def checkBridgeBool : RuntimeState → Bool
```

These should be connected to propositions where practical:

```lean
theorem checkWellFormedBool_sound :
  checkWellFormedBool s = true → WellFormed s
```

If full soundness is too expensive, document checkers as testing-only.

### Shrinker

For a failing sequence, minimize it:

```lean
def shrinkProgram : (List RuntimeOp → Bool) → List RuntimeOp → List RuntimeOp
```

Simple deletion-based shrinking is enough:

1. try removing each operation;
2. keep the removal if failure still occurs;
3. repeat to fixed point.

### Explorer executable

Add:

```text
MainExplorer.lean or lake exe henret-explore
```

Modes:

```text
--depth 4
--tasks 3
--actors 2
--property wellformed
--property bridge
--property occurrence
```

## Implementation tasks

1. Create `Henret/Explore/Gen.lean`.
2. Create `Henret/Explore/Check.lean`.
3. Create `Henret/Explore/Shrink.lean`.
4. Add bounded search executable.
5. Add at least three properties: well-formedness, occurrence uniqueness, bridge skeleton consistency.
6. Add one deliberately failing sample property to demonstrate shrinking.
7. Add docs with examples of explorer output.
8. Keep the explorer outside the default `import Henret` path.

## Acceptance criteria

- Explorer can enumerate programs up to a small depth.
- Explorer finds and shrinks a deliberately false property.
- Explorer confirms key true properties over the bounded sample set.
- It is documented as empirical/model-search support, not proof.

## Risks

Search may explode. Keep defaults tiny and CI mode bounded. Larger exploration
can be a local/nightly tool.
