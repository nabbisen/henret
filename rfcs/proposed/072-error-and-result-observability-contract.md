---
rfc: 72
title: Error and Result Observability Contract
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [74]
blocks: []
category: observability
---

# RFC 072 — Error and Result Observability Contract

## Status

Proposed strategic RFC.

## Summary

Define which `StepResult` values and state transitions are public observable behavior. This contract is required for replay, trace equivalence, conformance tests, and adapter certification.

## Motivation

Henret has several result categories: success, invalidity, blocked waiting, received envelope, wake lists, etc. Some are core public semantics. Others may be diagnostic or implementation-shaped. External runtimes need to know what they must reproduce.

Without an observability contract, conformance tests can overfit internal details or under-check important behavior.

## Goals

- Define public observability of each `StepResult` constructor.
- Define which state changes are observable in trace/replay formats.
- Support multiple observability profiles if needed.
- Prevent accidental overclaiming in docs.

## Non-goals

- Do not hide safety-critical violations.
- Do not make internal state entirely opaque.
- Do not define full trace semantics if RFC 045 is not implemented yet; provide compatible groundwork.

## Proposed classification

### Public-semantic results

These must be preserved by conforming implementations:

- `invalid`
- `blocked`
- `spawned t`
- `received envelope`
- `woke tasks` if exposed by the model operation
- terminal/cancel success if represented distinctly

### Low-information success

`ok` is observable but intentionally does not expose all internal changes.

### Diagnostic results

If some result constructors exist only to help demo/testing, mark them diagnostic. A runtime adapter may not need to expose them exactly if it proves equivalent public behavior.

## State observability

Observable state components for replay/conformance:

- task lifecycle state;
- ready/running/waiting/sleeping membership;
- mailbox envelopes;
- logical clock;
- timer deadlines when testing timer semantics;
- parent relation;
- occurrence ids.

Non-observable or internal by default:

- proof helper decomposition;
- internal bridge witness objects;
- generated theorem scaffolding.

## Lean representation

```lean
inductive ObservabilityLevel where
  | public
  | diagnostic
  | internal

structure ResultObservability where
  resultKind : String
  level : ObservabilityLevel
  conformanceRequired : Bool
```

## Design note

The contract should be stricter for safety-relevant behaviors than for scheduling order. For example, duplicate occurrence ids are always observable as an error; exact ready queue order may be profile-dependent.

## Concerns

- If too much is public, adapters become hard to write.
- If too little is public, Henret loses value as a semantic reference.
- Result observability interacts with semantic equivalence; define them together if possible.

## Implementation tasks

1. Add `docs/result-observability-contract.md`.
2. Classify every `StepResult` constructor.
3. Update replay format to reference this contract.
4. Update adapter contract to list required observable behaviors.
5. Add negative conformance examples for `invalid` vs `blocked`.
6. Add release gate phrase checks for vague result descriptions.

## Acceptance criteria

- Every `StepResult` has an observability classification.
- Replay and conformance docs use the classification.
- Public docs no longer imply that diagnostic details are mandatory runtime API unless they are.
