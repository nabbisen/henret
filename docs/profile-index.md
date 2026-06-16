# Profile Index

Henret's semantic profiles (RFC 054) let a consumer name the subset of
the model it depends on. Profiles are metadata — they do not change any
theorem or the behavior of `step`/`run`. The vocabulary lives in
`Henret/Profile.lean`; this index maps the public theorems to the
**minimum profile** required to state them.

## The named profiles

| Profile | Features | Meaning |
|---|---|---|
| `core` | lifecycle | bare task lifecycle: spawn, schedule, yield, complete, cancel |
| `actor` | + actorMessaging, parking, occurrenceIdentity | actor mailboxes, parking on empty receive, message occurrence identity |
| `full` | + timers, supervision, bridge, boundedMailbox | every currently-implemented feature |

Inclusion is kernel-proven: `core_le_actor`, `actor_le_full`,
`core_le_full` (all depend only on `propext`). Reserved features
`schedulingPolicy` (RFC 058) and `resourceLifetime` (RFC 057) exist in
the `SemanticFeature` enum but appear in no named profile yet.

## Theorem → minimum profile

### `core`

| Theorem | Why core |
|---|---|
| `step_invalid_unchanged` | invalid ops are no-ops on any state |
| `wake_exact` | waking affects only the woken task |
| `preserves_wf_*` for lifecycle ops | lifecycle preservation |
| schedulable-completeness theorems | ready queue soundness/completeness |

### `actor`

| Theorem | Why actor |
|---|---|
| `receive_only_own` | actor-local receive |
| `send_appends`, `send_stamps_source`, `inject_stamps_none` | mailbox delivery and provenance |
| `reachable_occurrence_unique` | message occurrence identity |
| `receive_blocked_parks`, `reachable_waiters_exact`, `reachable_waiter_actor_unique` | parking / wait-queue integrity |

### `full`

| Theorem | Why full |
|---|---|
| `reachable_wf` | asserts all 29 `WellFormed` fields (spans lifecycle, actor, timer, parent, occurrence, capacity) |
| `reachable_mailbox_within_capacity`, `full_has_boundedMailbox` | bounded mailboxes / backpressure (RFC 056) |
| `reachable_parent_lt`, `parent_chain_terminates` | parenthood / supervision groundwork |
| `reachable_restart_fresh`, `reachable_restart_old_failed`, `reachable_restart_parent_consistent`, `restart_preserves_parent_acyclicity`, `restarted_task_has_owner` | supervision (RFC 049) |
| `bridge_step_single_worker`, `reachable_bridge` | bridge (single-worker projection) |
| timer/sleep theorems (`tick_advances_clock`, `sleep_sets_timer`, …) | timers |

## Example → profile

| Example | Profile |
|---|---|
| `01_task_lifecycle` | core |
| `02`–`07` (mailbox, parking, occurrence) | actor |
| `08`–`14` (matrix, parenthood, trace, conformance, supervision, rendering) | full |

## Which profile should I use?

- Reasoning only about spawn/schedule/complete? **core**.
- Building on actor messaging, mailboxes, and delivery identity? **actor**.
- Using timers, supervision, or the bridge? **full**.

`import Henret` brings in the full model and the profile vocabulary; the
profile is documentation/metadata, so there is no separate build target
to select. Future RFCs may use profiles to group imports or derive
specialized theorem bundles.

## Consistency

This index classifies the stable and experimental headline theorems (see
[`proof-index.md` § Stability](proof-index.md#theorem-stability)). When a
new headline theorem is added, classify it here by the smallest profile
whose features its statement uses.
