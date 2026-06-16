# RFC NNN — <Title>

## Status

Proposed.

## Summary

<One or two paragraphs: what this RFC proposes and why, at a glance.>

## Motivation

<The problem this solves. Concrete pain points, prior drift, or missing
capability.>

## Non-goals

<What this RFC explicitly does not do, to bound scope.>

## Proposed design

<The design. Types, operations, theorems, file layout — whatever the RFC
introduces.>

## Semantic Impact Checklist

> Required only for **semantic-core changes** — edits to
> `Henret/Scheduler/Op.lean`, `Scheduler/Model.lean`, `Core/Result.lean`,
> `Actor/Task.lean`, `Actor/Mailbox.lean`, `Proofs/Invariants.lean`,
> `Proofs/InvariantsPreservation.lean`, or `Bridge/*`. Delete this section
> for non-semantic RFCs (docs, tooling, renderers, new derived theorems).
> See `docs/semantic-extension-governance.md`.

1. **Public types** — <RuntimeOp / RuntimeState / StepResult / TaskState /
   Envelope changes, or "none">
2. **Step branches** — <which `step` cases change>
3. **WellFormed fields** — <added / removed / strengthened, base and
   RestartWellFormed>
4. **Preservation cases** — <which `preserves_wf_*` / dispatch arms change>
5. **Examples** — <which `examples/NN_*.lean` change>
6. **Bridge translation** — <`toQOps` and `bridge_*` changes>
7. **Trace events** — <`TraceEvent` constructors added / changed>
8. **Matrix entries** — <`proof-trust-test-matrix.md` rows + classification>
9. **Migration note** — <required `docs/migration/` note>
10. **Stale phrases** — <old phrases to ban in the stale-phrase gate>

## Implementation tasks

1. <ordered, checkable tasks>

## Acceptance criteria

- <observable, testable outcomes>

## Risks

<What could go wrong; how scope is kept bounded.>
