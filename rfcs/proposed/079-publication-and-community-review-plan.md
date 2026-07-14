---
rfc: 79
title: Publication and Community Review Plan
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [76, 77, 78, 101, 104]
blocks: []
category: pedagogy
---

# RFC 079 — Publication and Community Review Plan

## Status

Proposed strategic RFC.

## Summary

Prepare Henret for external publication and community review as a Lean 4 ecosystem project. This RFC defines release content, reviewer materials, issue templates, and communication boundaries.

## Motivation

Henret has grown from a private proof project into a credible semantic reference model. Public release requires more than passing builds. The project needs clear positioning, examples, theorem maps, non-goals, contribution rules, and review checklists.

## Goals

- Prepare a public-quality repository presentation.
- Make project purpose immediately understandable.
- Invite useful review without attracting misunderstanding as a production runtime.
- Establish contribution and RFC workflow.

## Non-goals

- Do not publish as production runtime.
- Do not claim complete verification of the C runtime.
- Do not promise broad compatibility with all actor models.
- Do not require formal publication paper in this RFC.

## Public positioning

Recommended one-line description:

```text
Henret is a Lean 4 semantic reference model for actor/task execution systems, with kernel-checked invariants, replayable traces, and explicit runtime-conformance boundaries.
```

README must answer:

- What is Henret?
- What is it not?
- What is proven?
- What is trusted?
- What is tested?
- How do I run the model and examples?
- How do I read the proof map?
- How do I propose semantic changes?

## Public artifacts

Required before external release:

- README, concise and accurate.
- Guided tour.
- Proof/trust/test matrix.
- Assumption index.
- Public theorem API document.
- Counterexample catalog.
- Security and robustness interpretation.
- Replay examples.
- Golden trace conformance suite.
- RFC index.
- Contribution guide.

## Review checklist

External reviewers should be invited to check:

1. Does README overclaim?
2. Are trusted assumptions explicit?
3. Are `WellFormed` fields meaningful and not redundant?
4. Are bridge claims complete or properly marked partial?
5. Are examples educational?
6. Are theorem names stable enough?
7. Are non-goals visible?

## Issue templates

Recommended templates:

- semantic bug report;
- documentation drift report;
- theorem API request;
- new RFC proposal;
- runtime adapter conformance issue;
- proof-maintenance issue.

## Design note

A public release should present Henret as a rigorous semantic product, not as a large pile of proofs. Use diagrams, examples, and counterexamples.

## Concerns

- Public users may expect a runtime library; repeat non-goal clearly.
- Formal-methods users may challenge proof boundaries; the honesty ledger must be strong.
- Runtime implementers may want performance claims; keep those out of core Henret.

## Implementation tasks

1. Create `CONTRIBUTING.md`.
2. Create `.github/ISSUE_TEMPLATE/` files.
3. Create external review checklist.
4. Polish README first page.
5. Add `docs/what-henret-is-not.md`.
6. Add release checklist for public publication.
7. Add simple architecture diagram in text form.
8. Add roadmap page distinguishing immediate, strategic, and speculative RFCs.

## Acceptance criteria

- A new Lean user can understand Henret's purpose in 10 minutes.
- A reviewer can find proof/trust/test boundaries quickly.
- A runtime implementer can find adapter/conformance expectations.
- Public non-goals prevent misinterpretation.
