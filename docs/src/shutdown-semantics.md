# Structured Cancellation & Shutdown (RFC 055)

Henret models orderly *shutdown* — closing actors to new messages and
winding the runtime down — as a small admission-control layer on top of
the existing model. This is the first true semantic-core extension since
RFC 040, and it is **safety-only**.

> **Safety, not liveness.** Every theorem here is a safety property: it
> says certain transitions are *rejected*, or that a transition *only*
> happens from a particular state. Nothing here claims that a shutting-
> down runtime *will* reach quiescence, that pending work *will* drain,
> or that anything happens within any time bound. Those are liveness
> claims and require a scheduling/fairness policy (see RFC 046 for the
> conditional-liveness groundwork). Do not read "shutdown" as "eventual
> termination."

## The two status fields

`RuntimeState` carries two admission-status fields, both
`WellFormed`-irrelevant (no invariant field mentions them; the 33-field
base contract is unchanged via `WellFormed.runtimeStatus_irrel`; since RFC
091 `closeActor` also marks the actor's actor-owned resources closing):

- `actorStatus : ActorId → ActorStatus`, where `ActorStatus = active |
  closed`. (`open` is a Lean keyword, hence `active`.)
- `runtimeStatus : RuntimeStatus`, where `RuntimeStatus = running |
  shuttingDown | stopped`.

In `RuntimeState.init` every actor is `active` and the runtime is
`running`, so a program that never closes an actor or shuts down behaves
exactly as it did before RFC 055.

## Three operations

- **`closeActor a`** — flips actor `a` to `.closed` (invalid if `a` has
  no mailbox). Closing rejects *future* `send`/`inject` to `a` but never
  deletes mailbox contents: a closed actor's queued messages can still be
  drained by `receive`. This is the key design choice — closing is about
  *admission*, not *destruction*.
- **`shutdown`** — sets `runtimeStatus := .shuttingDown`. Idempotent.
  After it, root `spawn` and environment `inject` are rejected, but
  in-flight tasks keep running (and may `spawnChild`, `send`,
  `schedule`, etc.) so existing work can drain.
- **`stopWhenIdle`** — sets `runtimeStatus := .stopped` **only if** the
  runtime is quiescent; otherwise it is invalid (a no-op).

## Quiescence

```lean
def RuntimeQuiescent (s : RuntimeState) : Prop :=
  s.running = none ∧ s.readyQ = [] ∧ s.timers = []
```

`RuntimeQuiescent` is *computable* (it is the guard `stopWhenIdle`
checks). It deliberately does **not** require empty mailboxes or empty
waiter lists: a task parked on a mailbox with no live sender is a
*deadlock*, not active work, and a message sitting in a mailbox with no
scheduled reader will never be processed on its own in this cooperative
model. Counting either as "work remaining" would make `stopWhenIdle`
unable to fire in exactly the situations where stopping is correct. The
honest reading: `stopWhenIdle` stops the *scheduler* when there is
nothing left to schedule.

## Admission guards

Three pre-existing operations gained an outer guard:

| Operation | Rejected when | Theorem |
|---|---|---|
| `spawn a`    | `runtimeStatus ≠ .running` | `shutdown_rejects_spawn` |
| `send t b m` | `actorStatus b = .closed`  | `closed_actor_rejects_send` |
| `inject a m` | `runtimeStatus ≠ .running` **or** `actorStatus a = .closed` | `shutdown_rejects_inject`, `closed_actor_rejects_inject` |

Note that `send` is gated only on the *target actor* being closed, not on
`runtimeStatus`: task-to-task sends are existing work and drain during
shutdown. `spawnChild` is likewise ungated — only *root* `spawn` is
"new admission" in the RFC's sense.

## Subtree cancellation is `cancelTree`

The RFC's "cancelSubtree" is the existing **`cancelTree`** (RFC 039),
which cancels a task and all `taskParent`-descendants and removes them
from `readyQ`, `timers`, and waiter lists. The RFC's descendant-
cancellation and non-descendant-preservation obligations are met by
`cancelTree_cancels_task` and `cancelTree_preserves_task_state`. No new
cancellation operation was added.

## Headline theorems

All in `Henret.Proofs.Shutdown`, kernel-proven with `{propext,
Quot.sound}` only:

- `closeActor_sets_closed`, `closeActor_no_mailbox_invalid`,
  `closeActor_preserves_mailboxes`, `closeActor_preserves_other_status`
- `closed_actor_rejects_send`, `closed_actor_send_noop`,
  `closed_actor_rejects_inject`
- `shutdown_sets_status`, `shutdown_rejects_spawn`,
  `shutdown_rejects_inject`
- `stopWhenIdle_requires_quiescent`, `stopWhenIdle_sets_stopped`,
  `stopWhenIdle_not_quiescent_invalid`

Preservation: `preserves_wf_{closeActor,shutdown,stopWhenIdle}`; `shutdown`
and `stopWhenIdle` go via `WellFormed.runtimeStatus_irrel`, while `closeActor`
additionally marks actor-owned resources closing (RFC 091). Bridge:
`bridge_{closeActor,shutdown,stopWhenIdle}` (all queue-stable — these ops do
not touch `readyQ`).

See [`examples/16_structured_shutdown.lean`](../../examples/16_structured_shutdown.lean).

## Stopped vs. clean-stopped (RFC 092)

`runtimeStatus = .stopped` is reached by **either** `stopWhenIdle` (scheduler
quiescence only) **or** `stopWhenDrained` (quiescence + drained ledger). These
two stops are **intentionally distinct** — `stopWhenIdle` models "no executable
scheduler work remains, but cleanup obligations may remain" (e.g. a parked task
or an actor-owned resource still holding a handle). The architect's ruling on the
`stopped → Drained` question was to **keep them distinct** rather than merge them
(which would be a breaking change to `stopWhenIdle`), and to expose a named
clean-stop predicate instead:

| Predicate | Meaning |
|---|---|
| `Stopped` | `runtimeStatus = .stopped`. **No** claim about resources. |
| `StoppedDrained` | `Stopped` ∧ `Drained`. |
| `CleanStopped` | `Stopped` ∧ `Frozen` (quiescent, non-running, drained). |

`stopWhenDrained_enters_cleanStopped` certifies a successful `stopWhenDrained`
lands in `CleanStopped`; `stopWhenIdle_can_stop_undrained` certifies (by witness)
that `stopWhenIdle` may reach `.stopped` with a live resource — so the two ops can
never silently be conflated. Note `.stopped` is an *entry* fact: a later
`shutdown` relabels `.stopped → .shuttingDown` (both `≠ .running`), so durable
permanence is exposed at the `Frozen` level (`cleanStopped_run_stays_frozen`),
not over the exact `.stopped` label.

**Contract rule.** Downstream consumers (bridge/adapter/replay/observability/API)
must treat "clean shutdown" as `CleanStopped` (or `StoppedDrained`), never as bare
`.stopped`.
