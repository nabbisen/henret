# Henret

**Executable actor and task runtime models for Lean 4.**

Henret is a Lean 4 package for executable actor/task runtime models, scheduler
semantics, refinement patterns, and auditable backend boundaries.

It shows that Lean 4 is not only a theorem prover: you can model how a task
runtime behaves — spawn, schedule, yield, send, receive, sleep, tick, wake,
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

The Lean-only model is the product. Native backends are optional, clearly
separated, future material (see `rfcs/proposed/010-optional-ffi-backend-boundary.md`).

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

## Quickstart

Requirements: Lean 4 toolchain `leanprover/lean4:v4.15.0` (via elan). No C
compiler, no native dependencies — the default build is Lean-only.

```bash
lake build            # builds the model and all proofs (kernel-checked)
lake exe henret-demo  # runs executable scenarios with regression checks
```

The demo exercises five scenarios — task lifecycle, mailbox send/receive,
sleep/tick with no early wake, terminal cancellation, and two drivers that
complete every spawned task — and exits non-zero if any check regresses.

In your own file:

```lean
import Henret
open Henret

-- spawn a task for actor 7, schedule it, complete it
#eval (run .init [.spawn 7, .schedule, .complete 0]).taskState 0
-- some Henret.TaskState.completed
```

## The model in one minute

- `RuntimeOp` (`Henret/Scheduler/Op.lean`) — the operation grammar:
  `spawn`, `schedule`, `yield`, `complete`, `cancel`, `send`, `receive`,
  `sleep`, `tick`, `wake`.
- `RuntimeState` (`Henret/Scheduler/Model.lean`) — task states, ready queue,
  running slot, sorted logical-time timer queue, mailboxes, fresh-id counter.
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
- **Message ownership** — `send` appends exactly one message to exactly one
  mailbox; `receive` consumes exactly the head; neither touches task state
  (`send_appends`, `receive_consumes_one`, `send_preserves_other`, ...).
- **Timer correctness** — `tick now` never wakes a timer with
  `deadline > now`, wakes every expired sleeping task, and preserves timer
  queue sortedness (`tick_no_early_wake`, `tick_wakes_expired`,
  `run_preserves_sorted`).
- **Drain liveness** — the drain driver completes every queued runnable task
  (`drain_completes`).
- **Backend contract** — both reference mailbox backends satisfy the
  `MailboxBackend` refinement contract (`listBackend`, `mailboxBackend`).

See [`docs/proof-index.md`](docs/proof-index.md) for the full theorem list and
[`docs/proof-trust-test-matrix.md`](docs/proof-trust-test-matrix.md) for what
is merely tested or explicitly out of scope.

## Learning path

1. [`docs/guided-tour.md`](docs/guided-tour.md) — read this first.
2. `Henret/Examples/Basic.lean` — five `#eval`-able scenarios.
3. `Henret/Scheduler/Model.lean` — the `step` function is the semantics.
4. `Henret/Proofs/Lifecycle.lean` — the flagship monotonicity proof.
5. [`docs/patterns/refinement-contract.md`](docs/patterns/refinement-contract.md)
   — how to copy the backend-contract pattern for your own component.

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
