---
rfc: 55
title: Structured Cancellation and Shutdown
status: Implemented
implemented_in: v0.17.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC 055 — Structured Cancellation and Shutdown

## Status

Implemented (v0.17.0).

## Summary

Model structured cancellation and runtime/actor shutdown semantics without claiming fairness or guaranteed task completion.

## Motivation

Henret already has `cancel`, parenthood, parking, and timers. Practical execution management needs structured shutdown: cancelling a subtree, closing an actor to new messages, and shutting down the runtime so no new work is admitted. These are safety properties, not liveness properties.

## Non-goals

- Do not implement restart policies; RFC 049 already covered restart as a later feature.
- Do not claim cancelled tasks have executed cleanup unless cleanup semantics are added.
- Do not add OS signal or process management semantics.
- Do not claim fairness or eventual quiescence without a scheduling policy.

## Design

Add explicit shutdown state:

```lean
inductive ActorStatus where
  | open
  | closing
  | closed

inductive RuntimeStatus where
  | running
  | shuttingDown
  | stopped
```

Extend `RuntimeState`:

```lean
actorStatus : ActorId → ActorStatus
runtimeStatus : RuntimeStatus
```

Add operations:

```lean
| closeActor (a : ActorId)
| shutdown
| stopWhenIdle
| cancelSubtree (t : TaskId)
```

Semantics:

- `closeActor a` prevents future actor-to-actor sends and injects to `a`, but existing mailbox messages may remain unless explicitly drained.
- `shutdown` prevents new root spawns and environment injects.
- `cancelSubtree t` cancels `t` and all descendants known by `taskParent`.
- `stopWhenIdle` transitions to stopped only if no running, runnable, waiting, sleeping, or mailbox work remains.

## Formal model changes

Add fields to `RuntimeState` only after the operation design is stable. Add helper predicates:

```lean
def TaskLive (s : RuntimeState) (t : TaskId) : Prop

def RuntimeIdle (s : RuntimeState) : Prop

def DescendantOf (s : RuntimeState) (child parent : TaskId) : Prop
```

Consider whether `cancelSubtree` should compute descendants by scanning all task ids below `nextId`, which is acceptable in a pure model.

## Proof obligations

- `closed_actor_rejects_send`
- `shutdown_rejects_spawn`
- `cancelSubtree_cancels_descendants`
- `cancelSubtree_preserves_non_descendants`
- `stopWhenIdle_only_if_idle`
- `closed_actor_mailbox_exists` preservation if mailboxes remain allocated.
- Extend `WellFormed` with actor-status coherence if necessary.

## Tests and examples

- Demo: spawn parent/child/grandchild, cancel subtree, assert all descendants cancelled.
- Demo: shutdown rejects new spawn.
- Demo: closed actor rejects send/inject but does not delete mailbox contents.
- Negative tests for invalid close of nonexistent actor if the design chooses to reject it.

## Documentation updates

- Add shutdown semantics to guided tour.
- Add a safety/liveness distinction: shutdown is safety-only until fairness policy is added.
- Update proof matrix with no progress claims.

## Acceptance criteria

- Cancellation cannot leave cancelled tasks in readyQ, timers, running, or waiters.
- Shutdown prevents new admission.
- Close actor behavior is explicit and tested.
- No liveness claim is introduced accidentally.

## Risks and review questions

- Should actor closing reject `receive`, or allow draining existing mailbox contents?
- Should `cancelSubtree` cancel actors or tasks only?
- Should stopped runtime be terminal for every operation?

---

## Implementation (v0.17.0)

Shipped as the first true semantic-core extension since RFC 040. The
implementation is **safety-only**, as scoped: no fairness, liveness, or
guaranteed-quiescence claim is made.

### Scope decisions vs. the original proposal

- **`ActorStatus` is two-state (`active | closed`)**, not three. The
  proposed `open` is a Lean keyword (renamed `active`); the transient
  `closing` state was dropped — it had no specified reject semantics and
  an unused constructor is a maintenance burden. A closed actor rejects
  new `send`/`inject`; reopening / `closing` can be a follow-up if needed.
- **`cancelSubtree` was *not* added** — `cancelTree` (RFC 039) already
  implements structured subtree cancellation. The proposal's
  `cancelSubtree_cancels_descendants` / `_preserves_non_descendants`
  obligations are discharged by the existing `cancelTree_cancels_task`
  and `cancelTree_preserves_task_state` family
  (`Henret.Proofs.Supervision`).
- **`RuntimeIdle` is the computable `RuntimeQuiescent`**: no running task,
  empty `readyQ`, no pending timers. Parked waiters with no sender are a
  *deadlock*, not active work, and deliberately do not block quiescence
  (documented in `docs/shutdown-semantics.md`). `TaskLive` / `DescendantOf`
  helpers were unnecessary given existing `descendantsOf`.

### Admission guards (answering the review questions)

- **Actor closing rejects future `send`/`inject` but allows `receive`**
  to drain existing mailbox contents (`closeActor_preserves_mailboxes`).
- **`shutdown` blocks root `spawn` and environment `inject`**, leaving
  `spawnChild` and task-to-task work to drain. `stopped` is reached only
  via `stopWhenIdle` from a quiescent state.
- Subtree cancellation operates on tasks (via `taskParent`), not actors.

### Headline theorems (all kernel-proven, `{propext, Quot.sound}` only)

`closeActor_sets_closed`, `closeActor_no_mailbox_invalid`,
`closeActor_preserves_mailboxes`, `closeActor_preserves_other_status`,
`closed_actor_rejects_send`, `closed_actor_rejects_inject`,
`shutdown_sets_status`, `shutdown_rejects_spawn`, `shutdown_rejects_inject`,
`stopWhenIdle_requires_quiescent`, `stopWhenIdle_sets_stopped`,
`stopWhenIdle_not_quiescent_invalid` — all in `Henret.Proofs.Shutdown`.
Bridge preservation: `bridge_closeActor` / `bridge_shutdown` /
`bridge_stopWhenIdle` (all queue-stable). `WellFormed` preservation:
`preserves_wf_closeActor` / `_shutdown` / `_stopWhenIdle` via the new
`WellFormed.status_irrel` (the admission-status fields are
`WellFormed`-irrelevant; the 28-field base contract is unchanged).

### Semantic Impact Checklist

1. **Public types** — `RuntimeState` gains `actorStatus : ActorId →
   ActorStatus` and `runtimeStatus : RuntimeStatus`; two new enums
   `ActorStatus`/`RuntimeStatus`; `RuntimeOp` gains `closeActor`,
   `shutdown`, `stopWhenIdle` (18 → 21 ops). `RuntimeQuiescent` predicate.
2. **Step branches** — three new `step` cases; admission guards added to
   `spawn` (outer `if runtimeStatus = .running`), `send` (outer
   `if actorStatus b = .closed`), `inject` (outer
   `if runtimeStatus ≠ .running ∨ actorStatus a = .closed`).
3. **WellFormed fields** — none. The status fields are invariant-
   irrelevant; safety lives in the separate `Shutdown.lean`.
4. **Preservation cases** — new `preserves_wf_{closeActor,shutdown,
   stopWhenIdle}`; `preserves_wf_{spawn,send,inject}` wrapped with an
   outer guard `by_cases`; all op-dispatchers gained three arms
   (`Timers`×2, `Ownership`×3, `Parenthood`, `StepProjections`,
   `Restart`×2, `InvariantsPreservation`, `Bridge`).
5. **Examples** — `examples/16_structured_shutdown.lean` added.
6. **Bridge translation** — `toQOps` is guard-aware for the new admission
   checks; the three new ops map to `[]` (no `readyQ` effect); all
   `toQOps_{send,inject,spawn}_valid_*` characterization lemmas carry the
   new guard hypotheses.
7. **Trace events** — three new `TraceEvent`s: `actorClosed`,
   `shutdownBegun`, `stoppedWhenIdle` (rendered in `Render.Trace` and
   `Conformance.Export`).
8. **Matrix entries** — new safety rows under a "Shutdown (RFC 055)"
   group, all classified *kernel-proven, safety-only* with explicit
   "no liveness" notes.
9. **Migration note** — `docs/migration/v0.16-to-v0.17.md` (additive:
   two enums, two `RuntimeState` fields, three ops; `cancelSubtree`
   maps to existing `cancelTree`).
10. **Stale phrases** — register "18 RuntimeOps" / "18-operation"
    (now 21). No earlier doc claimed a closed-set count for the new
    fields, so no other phrase needs banning.

