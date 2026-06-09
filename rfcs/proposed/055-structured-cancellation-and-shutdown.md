# RFC 055 — Structured Cancellation and Shutdown

## Status

Proposed.

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
