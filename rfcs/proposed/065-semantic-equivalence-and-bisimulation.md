---
rfc: 65
title: Semantic Equivalence and Bisimulation
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [72]
blocks: []
category: theory
---

# RFC 065 — Semantic Equivalence and Bisimulation

## Status

Proposed strategic RFC.

## Summary

Define levels of equivalence between Henret states and traces. The goal is to support bridge proofs, adapter conformance, replay comparison, and semantic-profile variants without requiring exact internal state equality for every use case.

## Motivation

As Henret grows, exact equality is often too strong. Two executions may differ in internal queue order, proof-only fields, or diagnostic event ordering while being observationally equivalent for a user or adapter. Conversely, some differences, such as a duplicated occurrence id or wrong mailbox receive, must never be ignored.

Henret needs named equivalence relations to prevent informal reasoning.

## Goals

- Define a hierarchy of equivalence relations.
- Identify which relations are intended for model proofs, adapter conformance, and documentation examples.
- Provide first Lean definitions and simple reflexivity/symmetry/transitivity theorems where appropriate.
- Prepare for bisimulation between Henret and external runtime traces.

## Non-goals

- Do not replace `WellFormed`.
- Do not prove full runtime bisimulation against the C scheduler in this RFC.
- Do not weaken safety claims by hiding semantically important differences.

## Proposed equivalence levels

### Level 0 — exact state equality

```lean
s₁ = s₂
```

Use for unit proofs and simple deterministic examples.

### Level 1 — observable result equality

Two execution steps are equivalent if their public `StepResult`s match, ignoring internal state differences.

Candidate:

```lean
def ResultEq (r₁ r₂ : StepResult) : Prop := r₁ = r₂
```

This is intentionally trivial at first, but it gives a named hook for future result masking.

### Level 2 — observable state equivalence

Ignore internal proof helper fields and focus on public semantic fields:

- task states;
- owners and parents;
- mailbox envelopes;
- timers;
- ready/running/waiting membership;
- logical time.

Candidate:

```lean
structure ObservableEq (s₁ s₂ : RuntimeState) : Prop where
  taskState_eq : s₁.taskState = s₂.taskState
  mailboxes_eq : s₁.mailboxes = s₂.mailboxes
  readyQ_eq : s₁.readyQ = s₂.readyQ
  running_eq : s₁.running = s₂.running
  timers_eq : s₁.timers = s₂.timers
  now_eq : s₁.now = s₂.now
```

### Level 3 — queue-permutation equivalence

Useful when scheduler fairness or bridge projection allows different ready queue order but the same set of runnable tasks.

Candidate:

```lean
def SameReadySet (s₁ s₂ : RuntimeState) : Prop :=
  ∀ t, t ∈ s₁.readyQ ↔ t ∈ s₂.readyQ
```

This must not be used where order matters.

### Level 4 — trace equivalence

Two traces are equivalent if they produce the same observable events under a chosen observability policy.

Candidate:

```lean
def TraceEq (obs : ObservabilityProfile) (tr₁ tr₂ : Trace) : Prop := ...
```

### Level 5 — bisimulation relation

A relation `R` between two systems such that each step in one can be matched by zero or more steps in the other while preserving observables.

Candidate:

```lean
structure Bisimulation (A B : Type) where
  R : A → B → Prop
  step_left : ...
  step_right : ...
```

## Design note

Do not try to prove everything at once. The first useful deliverable is a small equivalence hierarchy and a documentation rule: every bridge or adapter theorem must state which equivalence level it uses.

## Concerns

- Too many equivalence relations can confuse users.
- Queue-permutation equivalence can accidentally hide scheduler bugs.
- Bisimulation abstractions may become heavy unless they are introduced after trace semantics stabilize.

## Implementation tasks

1. Add `Henret/Semantics/Equivalence.lean`.
2. Define `ObservableEq`, `SameReadySet`, and `TraceEq` skeleton if trace type exists.
3. Prove reflexivity for all initial relations.
4. Prove symmetry/transitivity where mathematically appropriate.
5. Add documentation explaining when each relation is allowed.
6. Update bridge RFCs to name their equivalence level.
7. Add examples comparing exact equality vs observable equivalence.

## Acceptance criteria

- Henret has a documented equivalence hierarchy.
- Bridge/conformance documents stop saying vaguely "matches" without naming a relation.
- At least `ObservableEq` has basic equivalence theorems.
- No safety claim is weakened silently.
