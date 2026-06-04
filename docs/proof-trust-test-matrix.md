# Proof / Trust / Test Matrix

Every material claim Henret makes is classified here (RFC 009).

| Class | Meaning |
|---|---|
| PROVEN | Checked by the Lean kernel (no `sorry`; only `propext` / `Quot.sound`) |
| ASSUMED | Stated as a trusted interface or axiom |
| TESTED | Covered by an executable check in `lake exe henret-demo` |
| OUTSCOPE | Explicitly not claimed |

A pull request that adds a new correctness claim must update this file and the
relevant index (`proof-index.md`, `assumption-index.md`, `test-index.md`).

## Claims

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 1 | Completed tasks never resume (per step and per program) | PROVEN | `step_preserves_completed`, `run_preserves_completed` |
| 2 | Cancelled tasks never complete later | PROVEN | `step_preserves_cancelled`, `run_preserves_cancelled` |
| 3 | No operation moves any task out of a terminal state | PROVEN | `step_preserves_terminal`, `run_preserves_terminal` |
| 4 | `wake t` changes no task other than `t` | PROVEN | `wake_exact` |
| 5 | A valid wake moves exactly the sleeping task to ready, enqueued once at the tail | PROVEN | `wake_sets_ready` |
| 6 | Duplicate wake is invalid and changes nothing (no duplicate ready entries from wake) | PROVEN | `wake_twice_invalid` |
| 7 | `send` appends exactly one message to exactly the target mailbox | PROVEN | `send_appends`, `send_preserves_other` |
| 8 | `receive` consumes exactly one message (the head) | PROVEN | `receive_consumes_one`, `receive_length` |
| 9 | `receive` from an empty mailbox is invalid and changes nothing | PROVEN | `receive_empty_invalid` |
| 10 | `send`/`receive` never change task state | PROVEN | `send_preserves_tasks`, `receive_preserves_tasks` |
| 11 | `tick now` does not wake timers with `deadline > now` | PROVEN | `tick_no_early_wake`, `tick_keeps_future` |
| 12 | `tick now` wakes every expired sleeping task and enqueues the woken list | PROVEN | `tick_wakes_expired`, `tick_enqueues_woken` |
| 13 | The timer queue stays sorted under every operation and program | PROVEN | `step_preserves_sorted`, `run_preserves_sorted` |
| 14 | Mailbox dequeue spec: head removal, exactly | PROVEN | `Mailbox.dequeue_spec` |
| 15 | The drain driver empties the ready queue | PROVEN | `drain_empties` |
| 16 | The drain driver completes every queued drainable task (model-level liveness) | PROVEN | `drain_completes`, `completeAll_completes` |
| 17 | Both reference backends satisfy the mailbox refinement contract | PROVEN | `Refinement.listBackend`, `Refinement.mailboxBackend` (contract laws are fields, kernel-checked) |
| 18 | Invalid operations never mutate state | PROVEN by construction of `step` (every invalid branch returns `(s, .invalid)`); regression-TESTED in demo scenarios |
| 19 | Op-level round-robin driver (`driveOps`) completes spawned tasks | TESTED | demo scenario 5 |
| 20 | Concrete end-to-end scenarios (lifecycle, mailbox, sleep/tick, cancel) | TESTED | demo scenarios 1–4 |
| 21 | Native thread behavior, OS scheduling, wall-clock timers | OUTSCOPE | logical model only |
| 22 | C deque race-freedom / lock-free correctness | OUTSCOPE | prior-art material is not part of Henret's claims |
| 23 | Production runtime performance or fairness under OS threads | OUTSCOPE | not claimed |

## Assumptions

The Lean-only core makes **no project-specific assumptions**: there are no
custom axioms, no `sorry`, and no `native_decide`. All theorems depend only on
Lean's standard kernel axioms (`propext`, `Quot.sound`), verified with
`#print axioms`. See `assumption-index.md`.

## Native layer claims (Henret.Native.*)

These claims require `import Henret.Native.*` and are separate from the
zero-assumption core.

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 18 | `DequeModel` contract: any compliant backend tracks `listDeque` | PROVEN | `qRun_tracks` (depends: `propext` only) |
| 19 | `listDeque` satisfies `DequeModel` (all 6 laws by `rfl`) | PROVEN | `listDeque` struct fields |
| 20 | owner-end stack driver starves no fueled task | PROVEN | `driveStackB_complete` (`propext`, `Quot.sound`) |
| 21 | `nativeDequeModel` satisfies `DequeModel` | PROVEN given the 6 axioms | `nativeDequeModel` definition |
| 22 | Native deque programs track the reference | PROVEN given the 6 axioms | `nativeDequeModel_qRun_tracks` |
| 23 | `NativeDeque.toList_push` — push appends | ASSUMED | `NativeDeque.toList_push` axiom |
| 24 | `NativeDeque.steal_{val,rest}` — steal removes head | ASSUMED | 2 axioms |
| 25 | `NativeDeque.pop_{val,rest}` — pop removes last | ASSUMED | 2 axioms |
| 26 | `NativeDeque.toList_empty` — empty observes `[]` | ASSUMED | `NativeDeque.toList_empty` axiom |
| 27 | C deque race-freedom (concurrent steal + push) | OUTSCOPE | Requires Iris-style CSL |
| 28 | `@[extern]` C linkage, conformance differential tests | OUTSCOPE (planned follow-up work) | Planned for next iteration |

## v0.2.0 claims (invariants, ownership, time)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 29 | Every reachable state is well-formed | PROVEN | `reachable_wf` (`run_preserves_wf` ∘ `wf_init`) |
| 30 | The scheduler never duplicates a ready task | PROVEN | `WellFormed.readyQ_nodup` in every reachable state |
| 31 | A task occupies at most one ownership location (queued / running / timer) | PROVEN | `ready_not_running`, `ready_no_timer`, `running_no_timer` corollaries |
| 32 | A spawned task's owner is immutable | PROVEN | `spawn_sets_owner`, `step/run_preserves_owner` |
| 33 | Invalid operations never mutate state | PROVEN | `step_invalid_unchanged` |
| 34 | Logical time is monotone; backwards ticks are invalid no-ops | PROVEN | `step_clock_monotone`, `tick_backwards_invalid`, `tick_advances_clock` |
| 35 | `tick` wakes only genuinely sleeping tasks | PROVEN + TESTED | filter in `step` + `WellFormed.timers_sleep`; demo scenario 6 |

## v0.2.1 claims (strengthened invariant, RFC 019)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 36 | Timer queue sorted in every reachable state (now part of the single invariant) | PROVEN | `WellFormed.timers_sorted`, `reachable_timers_sorted` |
| 37 | Every reachable spawned task has an owning actor | PROVEN | `reachable_spawned_has_owner` |
| 38 | Every reachable owning actor has a mailbox | PROVEN | `reachable_owner_has_mailbox` |
| 39 | Per-operation message non-duplication (value semantics; occurrence identity not modeled — see RFC 022) | PROVEN, scoped | `send_appends`, `receive_consumes_one` |
