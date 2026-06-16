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

Proposed. **Phase 1 in v0.30.0; Phase 2A (Messaging.lean) in v0.31.0; Phase 2B-1
(Lifecycle.lean) in v0.32.0** (see _Architect ruling_ and the
_Phase 1 / 2A / 2B-1 implementation_ sections below). The RFC as a whole stays
Proposed because Phase 2B-2 (Shape-A pilot) and Phase 3 are gated on a separate
architect review; `implemented_in` is therefore left `null`.

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

## Phase 2A implementation (v0.31.0) — Messaging.lean

Architect-approved Messaging-only slice (Phase-1/2 review): lemma-only, per-field
helpers first, no Shape-A migration, no macros, simp-set only if evidence-gated
(none shipped — explicit invocation preferred), measurement recorded.

Shipped:

- Three `private` helpers in `Preservation/Messaging.lean` —
  `wf_occ_fresh_under_enqueue`, `wf_occ_nodup_under_enqueue`,
  `wf_occ_disjoint_under_enqueue` — discharge the occurrence-identity fields
  (`occ_fresh`/`occ_nodup`/`occ_disjoint`) under an enqueue. The proof is
  occurrence-only (it never reads the envelope's `source`), so one trio covers
  `send` and `inject` in both the waiter-present and waiter-absent branches.
  Adopted at all five enqueue sites. `Messaging.lean`: 2078 → 1989 lines; the occ
  proof is defined once instead of five times.
- `mailbox_within_capacity` kept **explicit** at every `send`/`inject` site (an
  enqueue grows a mailbox; the not-full guard bounds the new length via
  `Mailbox.enqueue_length` + `lt_capacity_of_not_full`) — never disguised as a
  pass-through (architect §10).
- `docs/proof-ergonomics-metrics.md` records the dummy-op file-touch measurement;
  honest finding: Phase 2A is a Shape-B (lines/duplication) win, not Shape-A
  (file-count). `docs/proof-style.md` records the method and the simp-set
  permission rule (Phase-1 lesson) + Phase-2 evidence gate.

Same theorem statements/names; all six Messaging theorems remain
`[propext, Quot.sound]`; public surface unchanged (101 names; the helpers are
`private`); all nine fast gates green. Matrix claims 233–234.

Deliberately **not** done in Phase 2A: macros; catch-all/Shape-A classification;
broad `step` simp-set; any change to the explicit capacity reasoning. Phase 2B
(`Lifecycle.lean`) and Phase 2C (`Resource.lean`, only if warranted) remain gated
on a Phase-2A review.

## Phase 2B-1 implementation (v0.32.0) — Lifecycle.lean

Architect-approved (Phase 2A checkpoint review): Shape-B only, per-field first, no
Shape-A migration, no macros, no forced simp-set, measurement recorded.

Shipped:

- Five per-field pass-through helpers in `Henret/Proofs/StepFields.lean` —
  `wf_waiters_owned_pass` (`mailboxWaiters`+`taskOwner` stable),
  `wf_waiters_nodup_pass` (`mailboxWaiters`), `wf_owned_has_mailbox_pass`
  (`taskOwner`+`mailboxes`), `wf_timer_nodup_pass` / `wf_timer_sorted_pass`
  (`timers`). Each takes exactly the stability proof(s) for the projections its
  field reads.
- Adopted at 22 sites across `Preservation/Lifecycle.lean`
  (`spawn`/`schedule`/`yield`/`complete`/`cancel`/`fail`/`spawnChild`); three
  `waiters_owned` bullets dropped a now-unnecessary defensive `by_cases`.
- `taskState`-reading fields (`waiters_waiting`/`timers_sleep`/
  `spawned_has_owner`/`owner_spawned`) left explicit — not pass-through.
- Helper suffix discipline (`*_pass` vs `*_under_enqueue` vs `*_of_*`) recorded in
  `docs/proof-style.md`; measurement in `docs/proof-ergonomics-metrics.md`
  (Observation 2).

`Lifecycle.lean`: 1692 → 1680 lines; exported `wf_*_pass`: 13 → 18 (all used).
Same theorem statements/names; axioms unchanged; public surface unchanged (101
names); all nine fast gates green. Matrix claim 235.

Deliberately **not** done in Phase 2B-1: macros; Shape-A classification (deferred
to a review-gated Phase 2B-2 pilot); simp-set; any `*_pass` helper for a
`taskState`-reading field. Phase 2C (`Resource.lean`) remains out of scope unless
a concrete repeated proof mass appears.

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
