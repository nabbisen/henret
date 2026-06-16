---
rfc: 61
title: Runtime Adapter Contract
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: integration
---

# RFC 061 — Runtime Adapter Contract

## Status

Proposed.

## Summary

Define the public contract an external runtime must satisfy to claim Henret-conformant behavior.

## Motivation

The project now has a separate concrete runtime package. Henret should publish a formal and practical adapter contract that says exactly what an implementation must expose: operations, state projections, trace emission, and unsupported features.

## Non-goals

- Do not require every runtime to support every Henret profile.
- Do not require native code to be verified.
- Do not claim conformance without trace evidence and profile declaration.

## Design

Define an adapter checklist:

1. Declare supported `SemanticProfile`.
2. Provide operation mapping from implementation API to Henret `RuntimeOp`.
3. Provide state projection mapping from implementation state to Henret-observable fields.
4. Emit traces in RFC 060 format.
5. Provide unsupported-operation behavior.
6. Provide trust/test evidence for native components.

Optionally define a Lean typeclass for pure adapters:

```lean
class HenretAdapter (ImplState : Type) where
  project : ImplState → RuntimeState
  stepImpl : ImplState → ImplOp → ImplState × ImplResult
  toRuntimeOp : ImplState → ImplOp → Option RuntimeOp
```


## Formal model changes

- Add `docs/runtime-adapter-contract.md`.
- If typeclass is added, keep it separate from core model.

## Proof obligations

- `adapter_step_refines` for pure adapters if implemented.
- For native/runtime adapters, classify as tested unless a proof exists.

## Tests and examples

- Example adapter for a tiny pure queue runtime.
- Negative example: adapter missing blocked receive support must declare profile without parking.

## Documentation updates

- Update bridge docs to reference the adapter contract.
- Add conformance badge criteria only after the contract is stable.

## Acceptance criteria

- Contract is explicit.
- A runtime cannot claim full Henret conformance without profile and evidence.
- The lean-runtime package can be evaluated against the contract.

## Risks and review questions

- Should conformance be all-or-nothing or profile-scoped?
- Should adapter evidence be machine-readable?
- Should a future Reservoir package expose certification metadata?
