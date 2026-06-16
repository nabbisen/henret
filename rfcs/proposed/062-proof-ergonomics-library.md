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

Proposed. **Phase 1 implemented in v0.30.0** (see _Architect ruling_ and _Phase 1
implementation_ below). The RFC as a whole stays Proposed because Phases 2–3 are
gated on a separate architect review; `implemented_in` is therefore left `null`.

## Summary

Extract reusable proof helpers, simp sets, and small tactics to control preservation-proof growth.

## Motivation

Henret has many operation × invariant preservation proofs. They are auditable but repetitive. Without a proof ergonomics layer, every semantic feature increases proof size linearly and risks copy-paste bugs.

## Non-goals

- Do not hide essential proof obligations behind opaque automation.
- Do not introduce brittle metaprogramming unless simpler helper lemmas fail.
- Do not make reviews harder by replacing readable proofs with magic tactics.

## Architect ruling (v0.29.0 review)

Approved as a **phased, lemma-first proof-style modernization**, not strong proof
automation. Decisions: auditability over brevity (compress only when the
obligation stays named); **no macros in Phase 1–2**; bulk-first (the 33-field
record build before inert-arm consolidation); **keep explicit per-op
classification — never `| _ =>`**; gradual, phase-gated rollout. The governing
sentence (now in `docs/proof-style.md`):

> Proof ergonomics may remove syntactic repetition, but it must not remove
> semantic accountability. Each preservation obligation must remain named either
> by a theorem, a field-specific lemma, or an explicit operation classification.

This supersedes the original _Design_ below: no macros, no `Automation/Cases.lean`,
and named simp-sets only where they demonstrably help (with governance).

## Phase 1 implementation (v0.30.0)

Shipped:

- `docs/proof-style.md` — the full proof-style guide (preservation principles,
  helper-lemma style, simp-set policy + governance, operation-classification and
  no-catch-all rules, macro policy, public-theorem stability, how-to-add a
  RuntimeOp / WellFormed field, measurement metric).
- **Theorem-name diff gate** — `scripts/public_theorem_index.py` +
  `docs/generated/public-theorems.md` + `docs/proof-api-stability.md`, wired into
  `check.sh` gate 7. Snapshots the 101-name prefix-defined public theorem surface
  and fails on undocumented rename/removal.
- **`Time.lean` pilot** — extracted `wf_mailbox_capacity_pass` (the three time
  blocks now share one field-specific helper for `mailbox_within_capacity`); same
  theorem statements and public names, axioms unchanged, all nine fast gates
  green.

Deliberately **not** done in Phase 1 (per the ruling): macros; `Automation/Cases.lean`;
catch-all classification; public-statement changes; sweeping Messaging/Lifecycle
rewrite. The `henret_upd` named simp-set was prototyped and **withdrawn** — the
point-update lemmas do not compose under a named `simp only` set, and registering
one would pull a `Lean.Meta.*` import into the prelude-only proof tree for no
payoff (governance rule §13.4 applied at design time). Simp-set adoption is
deferred to the Phase-2 dense files.

## Original design (superseded by the ruling above)

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
