# Supervision Restart Policies (RFC 049)

Henret models failure and restart as a small semantic nucleus on top of
the existing parenthood and cascade-cancel groundwork. The first policy
is **one-for-one restart**: when a child fails, its supervisor may spawn
a replacement child with a fresh id, preserving a traceable parent
relationship and recording restart provenance.

This is deliberately *not* a production supervision tree. There is no
one-for-all restart, no restart-intensity window, and no automatic
restart — restart happens only when the explicit `restartOne` operation
is issued.

## Failure is distinct from cancellation

A new terminal task state, `TaskState.failed`, is distinct from
`.cancelled`. This distinction matters: a supervisor restarts *failures*,
not intentional cancellations. Both are terminal — no operation moves a
task out of either — but only `.failed` tasks are eligible for restart.

```
fail t  : non-terminal task t  -> failed   (clears ready/waiter/timer locations)
```

`fail` performs the same cleanup as `cancel` (dequeue, drop timer, remove
from waiter lists) but lands in `.failed`.

## The restart operation

```
restartOne parent failedChild actor
```

Guards (all required for a valid restart):

- `parent` is the running task (the supervisor);
- `failedChild`'s recorded parent is `parent`;
- `failedChild` is in the `.failed` state;
- a fresh `nextId` slot is available.

It creates a new child at `nextId` with parent `parent`, owner `actor`,
initial state `.new` (enqueued), and records provenance
`restartOf nextId = some failedChild`.

## Restart provenance

A new state field tracks provenance:

```lean
restartOf : TaskId → Option TaskId   -- restartOf new = some old
```

`restartOf new = some old` means task `new` was created by `restartOne`
as the replacement for failed task `old`.

## Invariants (kept separate from `WellFormed`)

The provenance facts live in a **separate** `RestartWellFormed`
structure, so the 33-field base safety contract is untouched. Three
fields hold in every reachable state:

| Field | Guarantee |
|---|---|
| `restart_parent_consistent` | a replacement and the task it replaces share the same supervising parent |
| `restart_old_failed` | the replaced task is `.failed` |
| `restart_fresh` | the replaced task has a strictly smaller id than its replacement |

Preservation leans on the base layer: the 16 other operations plus `fail`
leave `restartOf` unchanged, so the pairs are stable and
`step_preserves_parent` / `step_preserves_terminal` carry the per-pair
facts forward; `restartOne` establishes the new pair directly from its
guards.

## Headline theorems

| Theorem | Statement |
|---|---|
| `reachable_restart_fresh` | `restartOf new = some old → old < new` in every reachable state |
| `reachable_restart_old_failed` | the replaced task is `.failed` |
| `reachable_restart_parent_consistent` | replacement and replaced share a parent |
| `restart_preserves_parent_acyclicity` | parent acyclicity (`parent_lt`) holds after restart |
| `restarted_task_has_owner` | a restarted task has an owning actor |

All depend only on `propext`, `Classical.choice`, and `Quot.sound` — no
project axioms.

## Trace events

`fail` and `restartOne` emit `TraceEvent.failed t` and
`TraceEvent.restarted parent old new actor` respectively, so supervision
flows are legible in the RFC 045 trace ledger:

```text
[..., scheduled 1, failed 1, scheduled 0, restarted 0 1 2 7]
```

See `examples/12_supervision_restart.lean` for a worked supervisor →
child fails → restart scenario with the invariants discharged.

## Non-goals

No restart intensity windows, no one-for-all restart, no process
links/monitors beyond parenthood, and no liveness claim — restart occurs
only when a `restartOne` operation is issued. These are left for future
RFCs.
