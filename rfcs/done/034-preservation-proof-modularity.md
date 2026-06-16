---
rfc: 34
title: Preservation-Proof Modularity
status: Implemented
implemented_in: v0.5.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: proofs
---

# RFC-HENRET-034: Preservation-Proof Modularity

## Motivation

`Henret/Proofs/InvariantsPreservation.lean` is ~779 lines and has grown
with every invariant RFC (019: +3 fields, 028: +1 field) and every
grammar RFC (024: +1 operation and two reworked branches). The v0.4.0
review flagged it: "not a blocker, but a warning — the next few
semantic RFCs should continue extracting projection and monotonicity
lemmas rather than letting the preservation proof grow monolithically."

The warning is timely because the three proposed semantic RFCs all grow
exactly this file: RFC 031 adds a task state, a state field, and three
invariant fields; RFC 032 adds an operation and two fields; RFC 033
adds three fields. Landing any of them into the monolith pushes it past
1,000 lines. The project's own guidelines say split at 300 effective
lines, strongly at 500.

This RFC is pure refactoring: **zero new theorems, zero renamed public
theorems, zero semantic change.** Its acceptance is that nobody
downstream can tell it happened except by file layout.

## Design

### Split axis: by operation, not by invariant

Two candidate decompositions:

**(A) By invariant** — `step_preserves_readyQ_nodup`,
`step_preserves_timers_sorted`, ... one lemma per field. Rejected:
each lemma would repeat the full eleven-branch operation scaffolding
(the `by_cases`/`cases` guard trees), duplicating the most verbose and
churn-prone part of the proof ten times. Adding an operation would then
touch ten files.

**(B) By operation** — one unconditional lemma per operation:

```lean
theorem preserves_wf_spawn (h : WellFormed s) :
    WellFormed ((step s (.spawn a)).1)
```

(unconditional: the lemma internally handles valid and invalid
branches, as the current per-branch proofs already do). Each lemma
states all current fields at once over a *single* guard tree.
**Chosen.** Adding an invariant field touches every per-op lemma but
only one proof obligation each (the new field's sub-proof — exactly
today's cost); adding an operation adds one new self-contained lemma
and one line in the assembly.

### File layout

```
Henret/Proofs/Preservation/
  Lifecycle.lean   -- spawn, schedule, yield, complete, cancel
  Messaging.lean   -- send, receive, inject  (mostly StepProjections)
  Time.lean        -- sleep, tick, wake
Henret/Proofs/InvariantsPreservation.lean   -- KEPT, now short:
  step_preserves_wf  (assembly: cases op <;> exact preserves_wf_*)
  run_preserves_wf, reachable_wf,
  reachable_* headline projections
```

Keeping `InvariantsPreservation.lean` as the public-surface file is
deliberate: every documented theorem name (`step_preserves_wf`,
`reachable_wf`, `reachable_queue_exact`, ...) keeps its module path's
*import barrel* unchanged (`Henret.Proofs` already imports it), the
proof index needs no edits, and gate 7's doc-symbol check passes
untouched. The grouping (lifecycle/messaging/time) matches the
operation families used everywhere else in the docs and the demo.

### Shared-shape lemma extraction

The per-branch sub-proofs repeat a small number of reasoning shapes.
Extract the recurring ones as named helpers (in
`Preservation/Common.lean` or appended to existing lemma modules):

1. **Point-update field reasoning** — "after `upd f k v`, a query at
   `u` is `v` if `u = k` else `f u`": used in nearly every
   `taskState`-writing branch; currently inlined as
   `by_cases hu : u = k; simp [upd, ...]` ~30 times. A pair of
   rewriting lemmas (`upd_eq_of`, `upd_ne_of`) plus a `simp` set tag
   shrinks each site to one line.
2. **Queue-append membership** — "`u ∈ q → u ∈ q ++ [t]`" and
   "`u ∈ q ++ [t] → u = t ∨ u ∈ q`" specializations used by every
   queueing branch (spawn/yield/tick/wake, and RFC 031/032 will add
   more).
3. **Filter-retain membership** — the cancel-branch shape
   "`u ∈ q → u ≠ t → u ∈ q.filter (· ≠ t)`".
4. **Mailbox monotonicity** is already extracted (RFC 024); the
   pattern generalizes to the RFC 031 `mailboxWaiters` field and is
   the template for its lemmas.

Only extract shapes that occur ≥3 times — the goal is removing
repetition, not inventing abstraction (per the project's
balance principle).

### What deliberately does NOT change

- No public theorem renames (gate 7 enforces).
- No statement strengthening/weakening — `step_preserves_wf` remains
  the exact theorem it is.
- No `WellFormed` restructuring (e.g. splitting into sub-structures
  was considered and rejected: it would rename every field projection
  in docs and downstream proofs for no proof-power gain).
- Axiom audit results byte-identical.

## Sequencing argument

Do this **before** RFC 031/032/033. The refactor is cheapest when the
content is stable (pure motion), and every subsequent RFC then pays
its preservation cost into a structure designed for growth: RFC 031's
three fields land as three sub-proofs per per-op lemma in three
domain files; RFC 032's `spawnChild` lands as one new lemma in
`Lifecycle.lean`; RFC 033's fields land mostly in `Messaging.lean`.
Refactoring *after* any of them means moving freshly written proofs.

## Risks

Low. The mechanical risk is bullet-indentation drift while moving
branch proofs into standalone lemmas (a known Lean 4.15 sharp edge in
this codebase — splice indentation must match the new `refine` depth).
Mitigated by moving one operation family at a time with a build between
each.

## Acceptance criteria

- [ ] All seven gates green with byte-identical gate-5 audit output.
- [ ] `grep`-verifiable: every public theorem name from
      `docs/proof-index.md` unchanged (gate 7 passes untouched).
- [ ] No file under `Henret/Proofs/` exceeds ~400 lines.
- [ ] `step_preserves_wf` body is a ≤15-line assembly.
- [ ] At least the three shared shapes above extracted and used at
      every applicable site.
