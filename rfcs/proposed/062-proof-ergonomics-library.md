---
rfc: 62
title: Proof Ergonomics Library
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: proofs
---

# RFC 062 — Proof Ergonomics Library

## Status

Proposed.

## Summary

Extract reusable proof helpers, simp sets, and small tactics to control preservation-proof growth.

## Motivation

Henret has many operation × invariant preservation proofs. They are auditable but repetitive. Without a proof ergonomics layer, every semantic feature increases proof size linearly and risks copy-paste bugs.

## Non-goals

- Do not hide essential proof obligations behind opaque automation.
- Do not introduce brittle metaprogramming unless simpler helper lemmas fail.
- Do not make reviews harder by replacing readable proofs with magic tactics.

## Design

Create:

```text
Henret/Proofs/Automation/Simp.lean
Henret/Proofs/Automation/Preservation.lean
Henret/Proofs/Automation/Cases.lean
```

Add named simp sets:

```lean
attribute [simp, henret_step] ...
attribute [simp, henret_proj] ...
```

Add small tactics only for repeated local shapes, for example:

```lean
macro "close_unchanged_field" : tactic
macro "split_task_eq" ident : tactic
```

Prefer helper lemmas over macros where possible.

## Formal model changes

- No semantic model change.
- Refactor existing preservation files gradually.

## Proof obligations

- Existing theorem statements unchanged.
- Axiom audit unchanged.
- Add a no-regression theorem list to prove automation does not weaken claims.

## Tests and examples

- CI should compare theorem names before/after or rely on doc-symbol check.
- Build-time measurement optional.

## Documentation updates

- Add proof style guide.
- Document when automation is allowed and when explicit proof is preferred.

## Acceptance criteria

- Preservation files shrink or become more structured.
- No theorem statement disappears.
- Automation is local, named, and reviewable.

## Risks and review questions

- What is the acceptable tradeoff between auditability and brevity?
- Should generated proof patterns be avoided until v1?
- Can this be done as pure lemma extraction only?
