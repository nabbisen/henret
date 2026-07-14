---
rfc: 76
title: Counterexample Catalog
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [70]
blocks: []
category: pedagogy
---

# RFC 076 — Counterexample Catalog

## Status

Proposed strategic RFC.

## Summary

Create a catalog of bad states and bad traces that each invariant or theorem prevents. This makes Henret more educational, reviewable, and persuasive as a semantic reference model.

## Motivation

A theorem is easier to understand when users see the bug it rules out. For example:

- `runnable_queued` prevents lost runnable tasks.
- `waiters_waiting` prevents a ready task from appearing in a wait queue.
- `occ_disjoint` prevents duplicate delivery identity across mailboxes.
- `parent_lt` prevents supervision cycles.

A counterexample catalog turns abstract invariants into concrete engineering value.

## Goals

- Document at least one prevented bad state per major invariant family.
- Provide small Lean examples or pseudo-states where possible.
- Connect each counterexample to theorem support.
- Use the catalog in guided tour and external review.

## Non-goals

- Do not make unreachable bad states part of normal model execution.
- Do not require proving every bad state is impossible separately if already covered by `reachable_wf`.
- Do not turn examples into full fuzzing.

## Catalog entries

Each entry should include:

```markdown
## Lost runnable task

Bad state:
- taskState 3 = ready
- readyQ = []

Prevented by:
- WellFormed.runnable_queued
- reachable_runnable_is_queued
- reachable_queue_exact

Why it matters:
- scheduler could starve a ready task forever despite no blocking condition.
```

Recommended entries:

1. lost runnable task;
2. duplicate ready queue task;
3. running task also in ready queue;
4. timer entry for non-sleeping task;
5. waiting task missing from waiter queue;
6. waiter listed under wrong actor;
7. duplicate waiter within a mailbox waiter list;
8. same task waiting on two actors;
9. parent cycle;
10. parent points to never-spawned task;
11. duplicate occurrence id in one mailbox;
12. duplicate occurrence id across mailboxes;
13. receive from another actor's mailbox;
14. invalid operation mutates state.

## Design note

The catalog should be written for humans. It is not a replacement for formal proof. It is an explanation layer.

## Concerns

- Bad-state examples may require partial/arbitrary states that cannot be constructed through `run`; mark them as unreachable examples.
- The catalog can drift if theorem names change; use doc-symbol checking.
- Avoid implying that Henret proves liveness where it proves only safety.

## Implementation tasks

1. Create `docs/counterexample-catalog.md`.
2. Add at least 12 entries.
3. Cite theorem names and invariant fields for each entry.
4. Add optional Lean snippets constructing arbitrary bad states.
5. Add guided tour section linking invariants to prevented bugs.
6. Add doc-symbol checks for theorem names used in the catalog.

## Acceptance criteria

- Every major invariant family has at least one counterexample entry.
- Users can understand the practical value of `WellFormed` without reading preservation proofs.
- No liveness/fairness claim is implied by safety counterexamples.
