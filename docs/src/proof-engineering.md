# Proof Engineering Guide

This document explains the proof infrastructure added in RFC 042 and how to use
it when writing or extending WellFormed preservation proofs in Henret.

---

## The problem: repetitive occ/parent bullets

Every preservation proof for an operation that leaves `mailboxes`, `nextMsgId`,
and `taskParent` unchanged must discharge five boilerplate bullets:

- `occ_fresh` (field 17): every envelope's occurrence id < `nextMsgId`
- `occ_nodup` (field 18): occurrence ids within each mailbox are distinct
- `occ_disjoint` (field 19): occurrence ids across different mailboxes are distinct
- `parent_lt` (field 15): a task's parent TaskId is strictly less than the task's
- `parent_spawned` (field 16): a parent exists implies the parent was spawned

The raw proofs look like this (from the pre-RFC-042 `schedule` preservation):

```lean
· -- parent_lt (RFC 032)
  intro u p hp
  exact h.parent_lt u p (by simp only [step, hr, hq, if_pos hrun] at hp; exact hp)
· -- parent_spawned (RFC 032)
  intro u p hp
  have hpar : s.taskParent u = some p := by
    simp only [step, hr, hq, if_pos hrun] at hp; exact hp
  obtain ⟨st, hst⟩ := h.parent_spawned u p hpar
  by_cases hpt : p = t
  · exact ⟨.running, by simp [step, hr, hq, if_pos hrun, upd_self, hpt]⟩
  · exact ⟨st, by simp only [step, hr, hq, if_pos hrun, upd, if_neg hpt, hst]⟩
· -- occ_fresh (RFC 033): mailboxes unaffected
  intro a mb env hmb henv; simp only [step, hr, hq, if_pos hrun] at hmb ⊢
  exact h.occ_fresh a mb env hmb henv
· -- occ_nodup (RFC 033): mailboxes unaffected
  intro a mb hmb; simp only [step, hr, hq, if_pos hrun] at hmb
  exact h.occ_nodup a mb hmb
· -- occ_disjoint (RFC 033): mailboxes unaffected
  intro a b mba mbb hab hmba hmbb ea hea eb heb
  simp only [step, hr, hq, if_pos hrun] at hmba hmbb
  exact h.occ_disjoint a b mba mbb hab hmba hmbb ea hea eb heb
```

That is 20 lines for 5 bullets across every qualifying operation. With 10–12
such operations in the three preservation files, this amounts to roughly 200
lines of structurally identical code.

---

## The solution: `StepFields.lean` helpers

`Henret/Proofs/StepFields.lean` (RFC 042) provides five helper theorems:

```lean
-- Occurrence pass-throughs (require mailboxes/nextMsgId unchanged)
theorem wf_occ_fresh_pass    {s s' : RuntimeState} (h : WellFormed s)
    (hm : s'.mailboxes = s.mailboxes) (hn : s'.nextMsgId = s.nextMsgId) ...

theorem wf_occ_nodup_pass    {s s' : RuntimeState} (h : WellFormed s)
    (hm : s'.mailboxes = s.mailboxes) ...

theorem wf_occ_disjoint_pass {s s' : RuntimeState} (h : WellFormed s)
    (hm : s'.mailboxes = s.mailboxes) ...

-- Parent pass-throughs (require taskParent unchanged)
theorem wf_parent_lt_pass    {s s' : RuntimeState} (h : WellFormed s)
    (hp : s'.taskParent = s.taskParent) ...

theorem wf_parent_spawned_pass {s s' : RuntimeState} (h : WellFormed s)
    (hp : s'.taskParent = s.taskParent)
    (hsp : ∀ t, (∃ st, s.taskState t = some st) → ∃ st', s'.taskState t = some st') ...
```

With these, the same five bullets become:

```lean
· -- parent_lt (RFC 042)
  intro u p hp
  exact wf_parent_lt_pass h (by simp [step, hr, hq, if_pos hrun]) u p hp
· -- parent_spawned (RFC 042)
  intro u p hp
  obtain ⟨st, hst⟩ := h.parent_spawned u p (by simpa [step, hr, hq, if_pos hrun] using hp)
  exact step_preserves_spawned hst _
· -- occ_fresh (RFC 042)
  intro a mb env hmb henv
  exact wf_occ_fresh_pass h (by simp [step, hr, hq, if_pos hrun])
    (by simp [step, hr, hq, if_pos hrun]) a mb env hmb henv
· -- occ_nodup (RFC 042)
  intro a mb hmb
  exact wf_occ_nodup_pass h (by simp [step, hr, hq, if_pos hrun]) a mb hmb
· -- occ_disjoint (RFC 042)
  intro a b mba mbb hab hmba hmbb ea hea eb heb
  exact wf_occ_disjoint_pass h (by simp [step, hr, hq, if_pos hrun])
    a b mba mbb hab hmba hmbb ea hea eb heb
```

That is 10 lines for the same five bullets — a 50% reduction per operation,
and more importantly, a **zero-think** pattern: the only choice is the guard
expression.

---

## When to use the helpers

### Use `wf_occ_*_pass` when:

- The step does not modify `mailboxes` (i.e. no `upd s.mailboxes ...` in the
  operation's branch)
- The step does not modify `nextMsgId` (most operations; only `send` and `inject`
  increment it)

Operations that qualify: `schedule`, `yield`, `complete`, `cancel`, `wake`,
`sleep`, `tick`, `spawnChild`, `cancelTree`.

Operations that do NOT qualify (custom proofs required):
- `spawn` — conditionally creates a new empty mailbox
- `send` — appends an envelope and increments `nextMsgId`
- `inject` — appends an envelope and increments `nextMsgId`

For `receive`, the occ bullets are already minimal 1-liners because the
parking path leaves `mailboxes` and `nextMsgId` unchanged; these can be
left as direct `h.occ_*` calls without the pass-through helpers.

### Use `step_preserves_spawned` for `parent_spawned` when:

The simplest form of `parent_spawned` is:

```lean
· intro u p hp
  obtain ⟨st, hst⟩ := h.parent_spawned u p (by simpa [GUARDS] using hp)
  exact step_preserves_spawned hst _
```

`step_preserves_spawned` states that if a task was spawned before the step,
it remains in some state after. The `_` is inferred as the current operation.

**Important caveat**: `step_preserves_spawned hst _` only works when the proof
goal's LHS is literally `((step s op).1).taskState p`, not a simp-reduced
struct literal. In practice this means the pattern works in preservation proofs
where the step result has not been unfolded by simp in scope.

If the proof context has reduced the step result to a struct literal (e.g., via
`simp [step, guards]` applied to the goal), use the manual case split instead:

```lean
· intro u p hp
  obtain ⟨st, hst⟩ := h.parent_spawned u p (by simpa [GUARDS] using hp)
  by_cases hpt : p = AFFECTED_TASK
  · exact ⟨NEW_STATE, by simp [step, GUARDS, upd_self, hpt]⟩
  · exact ⟨st, by simp [step, GUARDS, upd, if_neg hpt]; exact hst⟩
```

This is currently required for `receive`'s parking branch.

### Use `wf_parent_lt_pass` when:

- The step does not write `taskParent` at all, OR
- The step writes `taskParent` only for the new task at `nextId` (as in
  `spawn`, where no existing task has `nextId` as its TaskId)

Operations that do NOT qualify: `spawnChild` (writes `taskParent nextId`).

---

## How to add a new operation

When adding a new `RuntimeOp` constructor that:

1. Does not modify `mailboxes` or `nextMsgId`
2. Does not modify `taskParent`

Use this template for the occ/parent bullets:

```lean
-- In the preservation proof for `newOp`, add to refine block:
· -- parent_lt (RFC 042)
  intro u p hp
  exact wf_parent_lt_pass h (by simp [step, GUARDS]) u p hp
· -- parent_spawned (RFC 042)
  intro u p hp
  obtain ⟨st, hst⟩ := h.parent_spawned u p (by simpa [step, GUARDS] using hp)
  exact step_preserves_spawned hst _
· -- occ_fresh (RFC 042)
  intro a mb env hmb henv
  exact wf_occ_fresh_pass h (by simp [step, GUARDS]) (by simp [step, GUARDS]) a mb env hmb henv
· -- occ_nodup (RFC 042)
  intro a mb hmb
  exact wf_occ_nodup_pass h (by simp [step, GUARDS]) a mb hmb
· -- occ_disjoint (RFC 042)
  intro a b mba mbb hab hmba hmbb ea hea eb heb
  exact wf_occ_disjoint_pass h (by simp [step, GUARDS]) a b mba mbb hab hmba hmbb ea hea eb heb
```

Replace `GUARDS` with the hypotheses that characterize the valid branch
(e.g., `hrt, hts` for running-task operations; `hts, hterm` for task-state
operations).

---

## Combined occ helper: `OccFields` + `wf_occ_pass`

If you need all three occ bullets as a package (e.g. to prove `OccFields s'`
for use in a larger structured proof), use:

```lean
have hocc : OccFields s' := wf_occ_pass h hm hn
```

where `hm : s'.mailboxes = s.mailboxes` and `hn : s'.nextMsgId = s.nextMsgId`.
The three components are then `hocc.fresh`, `hocc.nodup`, `hocc.disjoint`.

---

## Scope of RFC 042

RFC 042 delivers the minimum viable proof automation infrastructure:

- Five helper theorems in `StepFields.lean` (147 lines, zero `sorry`)
- Applied to `schedule`, `yield`, `complete`, `cancel`, `spawnChild` in
  `Preservation/Lifecycle.lean` (901 → 887 lines)
- Applied to `parent_spawned` bullets in `Preservation/Messaging.lean`
  (651 → 645 lines)
- Already applied in `Preservation/Time.lean` (sleep, tick, wake) as part
  of RFC 038/039 development

The primary payoff is **forward maintenance**: every new operation that qualifies
(no mailbox/msgId/parent mutation) gains these five bullets for free.

---

## Non-goals

RFC 042 deliberately does not:

- Provide per-operation `@[simp]` stable-field lemmas (130+ lemmas; maintenance
  cost exceeds benefit at current scale)
- Automate the 16 other WellFormed fields (e.g., `readyQ_nodup`,
  `waiters_waiting`; these are operation-specific and don't share structure)
- Use Lean 4 macros or tactics requiring metaprogramming imports (not in
  `Henret`'s dependency set)

---

## RFC 082 — Helper adoption and ergonomics v2 (supersedes RFC 042)

RFC 042 shipped the `StepFields.lean` pass-through helpers but the v0.17.0
audit found **eight** of them used zero times. RFC 082 adopts them and adds a
durable gate so they cannot drift back to dead.

### Helper-usage gate

`scripts/helper_usage_check.py` (RFC 080-adjacent, gate stage 7) requires every
exported `wf_*_pass` helper to be *used* — its identifier present, outside
`StepFields.lean`, in a library `.lean` source **after stripping comments and
string literals** (082-1, so a commented-out usage does not count) — or to
carry a valid `HENRET_HELPER_RESERVED: reason; target RFC; expiry` annotation
(082-2). The eight A1 helpers must be used, never annotated-away.

### Adoption sites

- `wf_parent_spawned_pass` and the bundled `wf_occ_pass` close the
  `parent_spawned` and occurrence bullets in the `sleep` preservation proof;
  `wf_parent_spawned_pass` replaces an eight-line `by_cases` bullet with two
  lines while keeping the guard (`taskParent` unchanged, spawned-preservation)
  visible (082-C).
- The six RFC 040 `wf_timed_*_pass` helpers close the timed-wait bullets in the
  `send`/`inject` no-waiter case, where `taskState`, `waitDeadline`, `timers`,
  and `timedMailboxWaiters` are all stable.

### Naming convention (082-D)

| suffix | meaning |
|---|---|
| `wf_<field>_pass`   | field unchanged by the operation |
| `wf_<field>_update` | field updated in a standard way |
| `wf_<field>_filter` | field preserved by a filter/remove operation |
| `wf_<field>_append` | field preserved by an append/wake operation |

### Metrics (082-B / 082-4)

| metric | value |
|---|---|
| exported `wf_*_pass` helpers | 12 |
| helpers used (outside `StepFields.lean`) | 12 / 12 |
| A1 (formerly-dead) helpers used | 8 / 8 |
| preservation field bullets (`· --`) | ~405 |
| `Preservation/*.lean` total lines | ~3,970 |
| `InvariantsPreservation` imports | 6 (unchanged) |

The 15–25% line-reduction target is **informative, not blocking** (082-B). This
pass establishes adoption and the durable usage gate rather than a large
reduction; the pass-through helpers are line-neutral at the definitional sites
where they apply, and `wf_parent_spawned_pass` is a small net reduction. The
broader reduction will come from operation-family unchanged-field lemmas applied
as RFC 056 (bounded mailboxes) and later features touch these files — which is
why RFC 082 is sequenced to **precede** RFC 056, so that feature is the first to
benefit from the now-adopted, gate-protected helper API. Guard/admission logic
remains visible in every operation-family proof, and no helper is `@[simp]`.
