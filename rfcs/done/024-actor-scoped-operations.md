---
title: Actor-Scoped Operations
rfc: RFC-HENRET-024
status: Implemented (v0.3.0)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-024: Actor-Scoped Operations

## Motivation

Through v0.2.1, `send a m` and `receive a` were global: any caller could
name any mailbox, with no task or ownership involvement. The v0.2.0 review
called this out as the natural next semantic frontier — actor semantics
need messaging *performed by tasks on behalf of their actors*, which is
what lets the model prove actor-local receive discipline. The v0.2.1
owner-existence invariant (`spawned_has_owner`) made this tractable.

## Design

The grammar replaces the global pair with task-scoped operations and adds
an explicit environment path (eleven operations total):

```lean
| send    (t : TaskId) (b : ActorId) (m : Message)  -- running task t → actor b
| receive (t : TaskId)                              -- t receives from its OWN actor
| inject  (a : ActorId) (m : Message)               -- environment → actor a
```

Guards (each a theorem, not a convention): the sender/receiver must be the
running task in `running` state with an owning actor; the target mailbox
must exist; `receive` derives the mailbox from `taskOwner t` — the caller
never names it. `inject` models messages from outside the modeled system
(the only task-free delivery path). `spawn` remains an environment
operation; parent-task spawning is supervision-tree territory (future RFC).

## Theorems

- **`receive_only_own`** (headline) — any successful receive dequeues the
  head of the receiving task's own actor's mailbox and touches no other
  mailbox: actor-local receive discipline.
- Scoped `send_appends`, `receive_consumes_one`, `receive_length`,
  `send/receive_preserves_other`, `receive_empty_invalid`;
  `inject_appends`, `inject_preserves_other`.
- Guard theorems: `send_not_running_invalid`, `send_unowned_invalid`,
  `receive_unowned_invalid`.
- `Henret.Proofs.StepProjections` — all three messaging operations touch
  only `mailboxes`, proved once per projection as `@[simp]` lemmas; the
  big case-analysis proofs discharge their messaging cases in one line.
- Mailbox monotonicity (`send/receive/inject_mailbox_isSome`) — messaging
  never removes a mailbox; carries `owned_has_mailbox` through the new
  operations.

## Acceptance criteria

- [x] Receive cannot name a mailbox; ownership is the only route.
- [x] `receive_only_own` kernel-checked, audit-clean, in the audit
      allowlist.
- [x] All v0.2.1 invariants re-proved over the eleven-operation grammar.
- [x] Examples 02/04 and the demo reworked; guard failures demonstrated.

## Implementation note (v0.3.0)

`Henret/Scheduler/Op.lean`, `Henret/Scheduler/Model.lean`,
`Henret/Proofs/StepProjections.lean` (new), `Henret/Proofs/Messaging.lean`
(rewritten), messaging cases updated across Lifecycle/Timers/Ownership/
InvariantsPreservation.
