# Proof ergonomics metrics

This file *records observations* from the proof-ergonomics measurement method
defined in `docs/proof-style.md` (RFC 062). It is a review artifact, not a CI
gate, and carries no permanent numeric target — the meaningful numbers move as
the model evolves. Each entry is a dated observation.

The method, in brief (see `proof-style.md` for the full description): add a dummy
inert `RuntimeOp`, count the proof files that must change to keep the build
green, and classify each remaining touch as *meaningful* (a genuine,
op-specific decision that should stay) or *mechanical* (a pass-through obligation
that a helper should absorb). The metric exposes whether a refactor reduced real
cost or merely moved text around.

---

## Observation 1 — RFC 062 Phase 2A (Messaging.lean occurrence-trio extraction)

- **baseline version:** v0.30.0 (before) → v0.31.0 (after)
- **date:** 2026-06-16
- **subject:** extraction of the occurrence-identity fields under enqueue
  (`occ_fresh` / `occ_nodup` / `occ_disjoint`) into three `private`
  `*_under_enqueue` helpers, adopted at all five enqueue sites in
  `Preservation/Messaging.lean` (`send` no-waiter / timed-waiter / waiter, and
  `inject` no-waiter / waiter).

### Dummy-op file-touch accounting

The experiment adds one inert `RuntimeOp` (a no-op that returns the state
unchanged) and counts the files that must change.

| | files touched | of which in Messaging.lean |
|---|---|---|
| before Phase 2A (v0.30.0) | ~10 (Shape-A cascade) | 1 |
| after Phase 2A (v0.31.0) | ~10 (Shape-A cascade) | 1 |

**The file *count* is unchanged — and that is expected, not a regression.**
Adding a `RuntimeOp` forces edits across the *enumeration* cascade
(`StepProjections`, `Parenthood`, `Restart`, `Grammar.toQOps`, `Trace/Run`,
`Bridge/Preservation`, `Meta/Docs`, plus the op's own preservation proof). That
cascade is *Shape A* — an explicit, totality-checked enumeration the project
deliberately keeps visible (architect §6: no catch-all classification). Phase 2A
was scoped to *Shape B* (the intra-proof field bullets), so it does not — and is
not meant to — shrink the Shape-A file list. Collapsing that list is a separate,
still-gated concern (Phase 2B classification pilot at most).

### Where Phase 2A actually moved the cost (intra-file, Shape B)

The measurable win is *within* the one preservation file a new enqueue-style op
touches: the occurrence obligation no longer has to be re-derived per op.

| | value |
|---|---|
| `Messaging.lean` total lines | 2078 → 1989 (−89) |
| enqueue sites carrying the occ trio | 5 |
| occ-trio proof per site (before) | ~37 lines, written inline |
| occ obligation per site (after) | 3 helper calls (~3–5 lines) |
| occ proof definition sites | 5 copies → **1** (three shared helpers, 69 proof lines) |

### Meaningful vs mechanical classification

- **`occ_fresh` / `occ_nodup` / `occ_disjoint` under enqueue — mechanical.**
  Identical at every enqueue site; the proof reads only the *occurrence* field
  of the appended envelope, never its `source`, so `send` and `inject` share one
  proof. Correctly centralized into helpers. A new enqueue-style op now discharges
  these three fields by calling the helpers rather than copying ~37 lines.
- **`mailbox_within_capacity` — meaningful; left explicit.** `send`/`inject`
  *grow* a mailbox, so the bullet must prove the *new* length stays within
  capacity (it does, because the op guards on not-full:
  `rw [Mailbox.enqueue_length]; … lt_capacity_of_not_full hcap hfull; omega`).
  This is real, op-specific reasoning and is deliberately **not** folded into a
  pass helper (architect §10). 42 capacity references remain, fully explicit.
- **waiter / timer / taskState fields — meaningful; left explicit.** Messaging
  ops wake or park tasks, so these projections are *not* stable; the per-field
  `*_pass` vocabulary does not apply here and was not forced in.

### Outcome

- zero `sorry`, axiom posture unchanged (all six Messaging theorems remain
  `[propext, Quot.sound]`), all nine fast gates green;
- no public theorem statement or name changed (public surface still 101 names);
- the three helpers are `private` and local to `Messaging.lean` (they depend on
  the file-private `nextMsgId_fresh`), so they add no public API and are not
  subject to the `wf_*_pass` helper-usage gate;
- net: one occ-proof definition instead of five, with capacity and waiter
  reasoning left visibly real.

**Honest reading:** Phase 2A is a Shape-B (lines-and-duplication) improvement, not
a Shape-A (file-count) one. The file-touch number is the right metric to keep
watching, but the lever Phase 2A pulled is per-op proof duplication inside the
file a new op already had to touch.
