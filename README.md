# Henret

[![License](https://img.shields.io/github/license/nabbisen/henret)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-4.15.0-blueviolet.svg)](lean-toolchain)
![sorry-free](https://img.shields.io/badge/proofs-sorry--free-success.svg)
![axioms](https://img.shields.io/badge/axioms-propext%20%7C%20Classical.choice%20%7C%20Quot.sound-informational.svg)

**Executable actor and task runtime models for Lean 4.**

Henret is a Lean 4 package for executable actor/task runtime models, scheduler
semantics, refinement patterns, and auditable backend boundaries.

It shows that Lean 4 is not only a theorem prover: you can model how a task
runtime behaves — spawn, schedule, yield, send, receive, inject, sleep, tick, wake,
cancel, complete — as pure, executable state transitions, then prove the
properties that matter and *name* everything you cannot prove.

```text
Actor/task operation grammar
  -> pure model interpreter (step / run)
  -> executable reference drivers
  -> refinement contract + reference backend
  -> proof/trust/test matrix
```

## What Henret is not

Henret deliberately does **not** claim to be:

- a production async runtime,
- a Tokio clone,
- an OS process manager,
- a native thread library,
- a fully verified lock-free scheduler.

The Lean-only model is the product. The Lean-only core has zero
project-specific assumptions. The optional native-boundary module
(`Henret.Native.*`, see `rfcs/done/010-optional-ffi-backend-boundary.md`)
declares six project-specific axioms; actual C linkage and conformance tests
are planned follow-up work.

## Why and when to use Henret

- **Learn systems modeling in Lean.** The whole architecture is readable in
  about ten minutes: one operation grammar, one total `step` function, one
  `run` fold, a handful of theorems.
- **Copy the patterns.** Operation grammars, pure interpreters, fueled
  drivers, backend contracts, and proof/trust/test matrices transfer directly
  to other Lean systems projects (queues, protocols, storage layers).
- **Audit the claims.** Every correctness statement is classified PROVEN /
  ASSUMED / TESTED / OUTSCOPE in
  [`docs/proof-trust-test-matrix.md`](docs/proof-trust-test-matrix.md).
  For a reviewer's entry point — the top-level claims, their evidence, and
  known limits — see the
  [assurance case](docs/assurance-case.md), the
  [review playbook](docs/review-playbook.md), and the
  [risk register](docs/risk-register.md).

## Quickstart

Requirements: Lean 4 toolchain `leanprover/lean4:v4.15.0` (via elan). No C
compiler, no native dependencies — the default build is Lean-only.

```bash
lake build            # builds the model and all proofs (kernel-checked)
lake exe henret-demo  # runs executable scenarios with regression checks
```

The demo exercises a sequence of regression scenarios covering task lifecycle,
mailbox send/receive, sleep/tick, cancellation, parenthood, occurrence
identity, and bridge-facing behavior, and exits non-zero if any check
regresses.

In your own file:

```lean
import Henret
open Henret

-- spawn a task for actor 7, schedule it, complete it
#eval (run .init [.spawn 7, .schedule, .complete 0]).taskState 0
-- some Henret.TaskState.completed
```

## The model in one minute

- `RuntimeOp` (`Henret/Scheduler/Op.lean`) — the operation grammar: task
  lifecycle (`spawn`, `spawnChild`, `schedule`, `yield`, `complete`,
  `cancel`, `cancelTree`, `fail`, `restartOne`), messaging (`send`,
  `receive`, `inject`, and the selective `receiveUntil` / `receiveByOccurrence`
  / `receiveFrom`), time (`sleep`, `tick`, `wake`), and structured shutdown
  (`closeActor`, `shutdown`, `stopWhenIdle`).
- `RuntimeState` (`Henret/Scheduler/Model.lean`) — task states, ready queue,
  running slot, sorted logical-time timer queue, mailboxes, fresh-id counter,
  and per-actor / runtime admission status (RFC 055).
- `step : RuntimeState → RuntimeOp → RuntimeState × StepResult` — total and
  executable. Invalid operations never mutate state; they return
  `StepResult.invalid` with the state unchanged (RFC 005).
- `run : RuntimeState → List RuntimeOp → RuntimeState` — whole programs.

## What is proven (Lean kernel, no `sorry`, no extra axioms)

- **Terminal monotonicity** — completed tasks never resume, cancelled tasks
  never complete later, for every single step and every whole program
  (`step_preserves_terminal`, `run_preserves_terminal`).
- **Wake exactness** — `wake t` touches no other task; a duplicate wake is
  invalid, so it cannot duplicate ready entries (`wake_exact`,
  `wake_twice_invalid`).
- **Message ownership** — Mailbox payload effects: `send`/`inject` append
  exactly one envelope to the target mailbox; successful `receive` removes
  exactly the head envelope (`send_appends`, `receive_consumes_one`,
  `send_preserves_other`, ...). Scheduling side effects: under Mesa semantics,
  delivery may wake one waiting task; an empty own-mailbox `receive` parks the
  running task.
- **Timer correctness** — `tick now` never wakes a timer with
  `deadline > now`, wakes every expired sleeping task, and preserves timer
  queue sortedness (`tick_no_early_wake`, `tick_wakes_expired`,
  `run_preserves_sorted`).
- **Drain liveness** — the drain driver completes every queued runnable task
  (`drain_completes`).
- **Reachability invariant** (v0.2.0) — every reachable state is well-formed:
  the ready queue never duplicates a task, every queued task is runnable,
  every timer task is sleeping, and a task occupies at most one ownership
  location; wait-queue integrity is also guaranteed (`reachable_wf`,
  `WellFormed`, 28 fields).
- **Ownership immutability** (v0.2.0) — a spawned task's owning actor never
  changes (`WellFormed.spawned_has_owner`, `reachable_spawned_has_owner`).
- **Invalid is a no-op** (v0.2.0) — an invalid operation never mutates state
  (`step_invalid_unchanged`).
- **Monotone logical time** (v0.2.0) — no operation decreases the clock;
  backwards ticks are invalid no-ops (`step_clock_monotone`,
  `tick_backwards_invalid`).
- **Actor-local receive discipline** (v0.3.0) — a task receives only from
  its own actor's mailbox, derived from ownership; no other mailbox is
  touched (`receive_only_own`).
- **Messaging field projections** (v0.3.0, updated v0.5.0) — the fields
  unconditionally unchanged per messaging operation: `send`/`inject` leave
  `taskOwner`, `running`, `timers`, `now`, `nextId` untouched; `receive`
  leaves `taskOwner`, `readyQ`, `timers`, `now`, `nextId` untouched. (After
  RFC 031, `send`/`inject` may touch `taskState`/`readyQ`/`mailboxWaiters`
  when waking a waiter; `receive` may touch `taskState`/`running`/
  `mailboxWaiters` when parking. `Henret.Proofs.StepProjections` covers
  only the unconditionally-unchanged fields.)
- **Schedulable completeness** (v0.4.0) — every reachable runnable task is
  in the ready queue; equivalently, the ready queue contains *exactly* the
  runnable tasks (`reachable_runnable_is_queued`, `reachable_queue_exact`).
- **Blocked receive parking** (v0.5.0) — an empty own-mailbox receive is
  `blocked`, not invalid; it parks the running task in `TaskState.waiting`,
  clears the running slot, and appends the task to its actor's
  `mailboxWaiters` queue (`receive_empty_parks`, `receive_blocked_parks`). A
  later valid `send`/`inject` wakes the head waiter to `.ready`. Four new
  `WellFormed` fields (14 total, now 19 as of v0.7.0) guarantee wait-queue integrity in every
  reachable state (`waiters_waiting`, `waiters_owned`, `waiting_queued`,
  `waiters_nodup`); `reachable_waiters_exact` is the exact-membership theorem
  mirroring `reachable_queue_exact`.
- **Occurrence identity** (v0.7.0) — every envelope delivered by `send` or
  `inject` is stamped with a globally unique `MessageId` allocated from
  `nextMsgId`. Three new `WellFormed` fields (`occ_fresh`, `occ_nodup`,
  `occ_disjoint`) guarantee that no two envelopes in any reachable
  mailboxes share an occurrence id (`reachable_occurrence_unique`).
- **Backend contract** — both reference mailbox backends satisfy the
  `MailboxBackend` refinement contract (`listBackend`, `mailboxBackend`);
  updated for v0.7.0 to operate on `Envelope` (was `Message`).

See [`docs/proof-index.md`](docs/proof-index.md) for the full theorem list and
[`docs/proof-trust-test-matrix.md`](docs/proof-trust-test-matrix.md) for what
is merely tested or explicitly out of scope.

Every claim also records *where* its evidence lives, machine-readably, in
[`docs/evidence-ledger.yaml`](docs/evidence-ledger.yaml). This package verifies
only its in-tree model proofs and in-tree executable checks; the concurrent
runtime harnesses (differential, linearizability, stress) live in a separately
versioned sibling package and are **not** verified by this tarball's gates. See
[`docs/package-boundary.md`](docs/package-boundary.md) for the split.

## Learning path

1. [`docs/guided-tour.md`](docs/guided-tour.md) — read this first.
2. `Henret/Examples/Basic.lean` — `#eval`-able scenarios (opt-in import; the demo executable drives all regression scenarios).
3. `Henret/Scheduler/Model.lean` — the `step` function is the semantics.
4. `Henret/Proofs/Lifecycle.lean` — the flagship monotonicity proof.
5. [`docs/patterns/refinement-contract.md`](docs/patterns/refinement-contract.md)
   — how to copy the backend-contract pattern for your own component.

**Using Henret in your own project?** Start with
[`docs/integration-contract.md`](docs/integration-contract.md) — the stable
boundary contract (stable imports, public theorem surface, operation
mapping, Mesa-semantics requirements, trust boundary, and versioning
policy). See `examples/10_integration_contract.lean` for a worked
consumer trace.

## Which Henret profile should I use?

Henret's semantics are grouped into named **profiles** (RFC 054) so you
can say which subset you depend on:

- **core** — bare task lifecycle (spawn, schedule, yield, complete,
  cancel).
- **actor** — core plus actor messaging, parking on empty receive, and
  message occurrence identity.
- **full** — every implemented feature: actor plus timers, supervision
  (fail/restart), and the bridge.

Profiles are metadata, not a build flag — `import Henret` always brings in
the full model. The inclusion chain `core ≤ actor ≤ full` is
kernel-proven. See [`docs/profile-index.md`](docs/profile-index.md) for
the theorem-to-profile mapping.

## Design notes

- **One mutation primitive.** Every per-id map change goes through
  `Henret.upd`, keeping preservation proofs uniform.
- **Guarded transitions.** `step` guards each transition (e.g. `wake` requires
  `sleeping`, `complete` requires the task to actually be running), which is
  what makes terminal monotonicity *unconditional* — no reachability
  hypothesis needed.
- **Logical time.** Timers are logical ticks with a sorted queue, not
  wall-clock time (RFC 007).
- **Prior art.** Henret's patterns were extracted from an earlier
  runtime-workspace prototype (Lean model + C Chase-Lev deque + typed FFI
  assumptions). See
  [`docs/prior-art-runtime-workspace.md`](docs/prior-art-runtime-workspace.md)
  for what was reused and which claims were *not* inherited.

## Project governance

RFCs live in [`rfcs/`](rfcs/README.md) under the lifecycle policy
(`proposed/` → `done/` → `archive/`). The proof/trust/test matrix must be
updated by any change that adds a correctness claim. See
[`CONTRIBUTING.md`](CONTRIBUTING.md).

## License

Apache-2.0. See [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
