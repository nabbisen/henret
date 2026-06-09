# RFC 074 — Bridge Completeness Certificate

## Status

Proposed strategic RFC.

## Summary

Define a machine-readable and human-readable certificate describing which Henret `RuntimeOp`s are covered by the bridge to the worker-queue model, under which conditions, and at which equivalence level.

## Motivation

The bridge layer is central to Henret's practical value. However, partial bridge coverage can be easy to misread. A certificate prevents vague claims such as "the bridge is implemented" when some operations or branches remain uncovered.

## Goals

- List every `RuntimeOp` and every semantically important branch.
- State whether it is covered by bridge theorem, tested only, unsupported, or out of scope.
- State the bridge equivalence relation used.
- Make the certificate part of release gates.

## Non-goals

- Do not complete bridge proofs in this RFC unless RFC 036 is included.
- Do not certify multi-worker bridge if only single-worker relation exists.
- Do not make unsupported branches disappear from docs.

## Certificate schema

Example table:

```markdown
| RuntimeOp | Branch | QOps | Bridge theorem | Status | Equivalence |
|---|---|---|---|---|---|
| spawn | valid | Push 0 nextId | bridge_spawn | covered | exact-list |
| schedule | readyQ nonempty | Pop 0 | bridge_schedule | covered | exact-list |
| cancel | queued task | Filter 0 t | bridge_cancel | covered | exact-list |
| send | no waiter | [] | bridge_send_no_waiter | covered | exact-list |
| send | waiter exists | Push 0 w | bridge_send_wakes | covered | exact-list |
| tick | expired timers | Push 0 t* | bridge_tick | covered | exact-list |
```

## Lean representation

Optional:

```lean
inductive BridgeCoverage where
  | covered
  | partial
  | testedOnly
  | unsupported
  | outOfScope

structure BridgeCertificateEntry where
  opName : String
  branchName : String
  coverage : BridgeCoverage
  theoremName : Option String
  equivalence : String
```

## Design note

The certificate should be generated or at least checked against theorem names. This pairs naturally with the doc-symbol checker.

## Concerns

- A branch-level certificate is more work than operation-level, but operation-level is too coarse.
- If theorem names change often, certificate maintenance becomes noisy.
- The certificate should not claim behavior for invalid branches unless the bridge explicitly handles invalid no-ops.

## Implementation tasks

1. Create `docs/bridge-completeness-certificate.md`.
2. List all `RuntimeOp` variants and relevant branches.
3. Add theorem-name references for covered branches.
4. Add status values for uncovered branches.
5. Add doc-symbol check for theorem names used in the certificate.
6. Add release gate: no bridge headline claim unless certificate has no unexpected partial entries.

## Acceptance criteria

- Every operation branch has an explicit bridge coverage status.
- The certificate identifies exact theorem names for covered branches.
- Public README bridge claims reference certificate status.
