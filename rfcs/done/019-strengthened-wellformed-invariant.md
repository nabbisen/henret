---
rfc: 19
title: Strengthened WellFormed Invariant
status: Implemented
implemented_in: v0.2.1
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: proofs
---

# RFC-HENRET-019: Strengthened WellFormed Invariant

## Motivation

The v0.2.0 review found `WellFormed` incomplete: it did not include timer
sortedness (proven separately via `run_preserves_sorted`) and did not relate
`taskOwner` to `taskState` or `mailboxes`. A well-formed state could have a
spawned task with no owner, or an owner with no mailbox — wrong for an
actor/task model.

## Design

Three fields added to `WellFormed`:

```lean
  timers_sorted : Timer.Sorted s.timers
  spawned_has_owner :
    ∀ t st, s.taskState t = some st → ∃ a, s.taskOwner t = some a
  owned_has_mailbox :
    ∀ t a, s.taskOwner t = some a → ∃ mb, s.mailboxes a = some mb
```

`owned_has_mailbox` is stated unconditionally over `taskOwner` (not gated on
spawnedness): `spawn` is the only owner write site and it guarantees the
actor's mailbox, and no operation ever removes a mailbox, so the stronger
form is preserved and simpler to use.

## Theorems

- `step_preserves_wf` / `run_preserves_wf` / `reachable_wf` re-proved for
  the nine-field invariant.
- New reachability headlines: `reachable_spawned_has_owner`,
  `reachable_owner_has_mailbox`, `reachable_timers_sorted`.
- Supporting: `wakeOne_none` / `wakeMany_none` (waking never spawns).

## Acceptance criteria

- [x] `reachable_wf` alone implies ready uniqueness, timer sortedness,
      timer/sleep coherence, owner existence, owner-mailbox existence, and
      location disjointness.
- [x] Axiom audit: standard kernel axioms only.

## Implementation note (v0.2.1)

`Henret/Proofs/Invariants.lean` (fields, `wf_init`),
`Henret/Proofs/InvariantsPreservation.lean` (per-operation proofs + the
three reachability corollaries), `Henret/Proofs/Ownership.lean`
(`wake*_none`).
