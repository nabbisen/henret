# Proof / Trust / Test Matrix

Every material claim Henret makes is classified here (RFC 009).

For the **minimum semantic profile** each headline theorem requires
(core / actor / full, RFC 054), see
[`docs/profile-index.md`](profile-index.md); profiles are kept in a
dedicated index rather than as a column here, to avoid duplicating this
table.

| Class | Meaning |
|---|---|
| PROVEN | Checked by the Lean kernel (no `sorry`; only `propext` / `Quot.sound`) |
| ASSUMED | Stated as a trusted interface or axiom |
| TESTED | Covered by an executable check in `lake exe henret-demo` |
| OUTSCOPE | Explicitly not claimed |

A pull request that adds a new correctness claim must update this file and the
relevant index (`proof-index.md`, `assumption-index.md`, `test-index.md`).

Each row also carries an **evidence-location** and **verified-here** column
(RFC 081): `in_tree_model_proof` / `in_tree_model_test` claims are present in
this package and verified by `scripts/check.sh --release`. `TESTED` here means
an **in-tree** executable check (the demo, conformance suite, or explorer) —
**not** the concurrent runtime harnesses, which live out-of-tree in the sibling
runtime package and are recorded only in
[`evidence-ledger.yaml`](evidence-ledger.yaml) with
`verified_by_this_tarball: false`. See
[`package-boundary.md`](package-boundary.md) for the split.

## Claims

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 1 | Completed tasks never resume (per step and per program) | PROVEN | `step_preserves_completed`, `run_preserves_completed` | in_tree_model_proof | yes |
| 2 | Cancelled tasks never complete later | PROVEN | `step_preserves_cancelled`, `run_preserves_cancelled` | in_tree_model_proof | yes |
| 3 | No operation moves any task out of a terminal state | PROVEN | `step_preserves_terminal`, `run_preserves_terminal` | in_tree_model_proof | yes |
| 4 | `wake t` changes no task other than `t` | PROVEN | `wake_exact` | in_tree_model_proof | yes |
| 5 | A valid wake moves exactly the sleeping task to ready, enqueued once at the tail | PROVEN | `wake_sets_ready` | in_tree_model_proof | yes |
| 6 | Duplicate wake is invalid and changes nothing (no duplicate ready entries from wake) | PROVEN | `wake_twice_invalid` | in_tree_model_proof | yes |
| 7 | one successful `send`/`inject` appends exactly one message *value* to exactly the target mailbox (per-operation; occurrence identity not modeled, RFC 022) | PROVEN | `send_appends`, `inject_appends`, `*_preserves_other` | in_tree_model_proof | yes |
| 8 | `receive` consumes exactly one message (the head) | PROVEN | `receive_consumes_one`, `receive_length` | in_tree_model_proof | yes |
| 9 | `receive` from an empty own mailbox is **blocked** and parks the task: `taskState` → `.waiting`, `running` → `none`, task appended to `mailboxWaiters` (RFC 031); non-running/unowned receive remains invalid | PROVEN | `receive_empty_parks`, `receive_blocked_parks`, `receive_unowned_invalid` | in_tree_model_proof | yes |
| 10 | Per-operation unconditionally-unchanged fields (RFC 031 updates): `send`/`inject` leave `taskOwner`, `running`, `timers`, `now`, `nextId` invariant; `receive` leaves `taskOwner`, `readyQ`, `timers`, `now`, `nextId` invariant | PROVEN | `Henret.Proofs.StepProjections` (e.g. `send_taskOwner`, `receive_readyQ`, `inject_taskOwner`) | in_tree_model_proof | yes |
| 11 | `tick now` does not wake timers with `deadline > now` | PROVEN | `tick_no_early_wake`, `tick_keeps_future` | in_tree_model_proof | yes |
| 12 | `tick now` wakes every expired sleeping task and enqueues the woken list | PROVEN | `tick_wakes_expired`, `tick_enqueues_woken` | in_tree_model_proof | yes |
| 13 | The timer queue stays sorted under every operation and program | PROVEN | `step_preserves_sorted`, `run_preserves_sorted` | in_tree_model_proof | yes |
| 14 | Mailbox dequeue spec: head removal, exactly | PROVEN | `Mailbox.dequeue_spec` | in_tree_model_proof | yes |
| 15 | The drain driver empties the ready queue | PROVEN | `drain_empties` | in_tree_model_proof | yes |
| 16 | The drain driver completes every queued drainable task (model-level liveness) | PROVEN | `drain_completes`, `completeAll_completes` | in_tree_model_proof | yes |
| 17 | Both reference backends satisfy the mailbox refinement contract | PROVEN | `Refinement.listBackend`, `Refinement.mailboxBackend` (contract laws are fields, kernel-checked) | in_tree_model_proof | yes |
| 18 | Invalid operations never mutate state | PROVEN by construction of `step` (every invalid branch returns `(s, .invalid)`); regression-TESTED in demo scenarios | in_tree_model_proof | yes |
| 19 | Op-level round-robin driver (`driveOps`) completes spawned tasks | TESTED | demo scenario 5 | in_tree_model_test | yes |
| 20 | Concrete end-to-end scenarios (lifecycle, mailbox, sleep/tick, cancel) | TESTED | demo scenarios 1–4 | in_tree_model_test | yes |
| 21 | Native thread behavior, OS scheduling, wall-clock timers | OUTSCOPE | logical model only | — | — |
| 22 | C deque race-freedom / lock-free correctness | OUTSCOPE | prior-art material is not part of Henret's claims | — | — |
| 23 | Production runtime performance or fairness under OS threads | OUTSCOPE | not claimed | — | — |

## Assumptions

The Lean-only core makes **no project-specific assumptions**: there are no
custom axioms, no `sorry`, and no `native_decide`. All theorems depend only on
Lean's standard kernel axioms (`propext`, `Quot.sound`), verified with
`#print axioms`. See `assumption-index.md`.

## Native layer claims (Henret.Native.*)

These claims require `import Henret.Native.*` and are separate from the
zero-assumption core.

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 18 | `DequeModel` contract: any compliant backend tracks `listDeque` | PROVEN | `qRun_tracks` (depends: `propext` only) | in_tree_model_proof | yes |
| 19 | `listDeque` satisfies `DequeModel` (all 6 laws by `rfl`) | PROVEN | `listDeque` struct fields | in_tree_model_proof | yes |
| 20 | owner-end stack driver starves no fueled task | PROVEN | `driveStackB_complete` (`propext`, `Quot.sound`) | in_tree_model_proof | yes |
| 21 | `nativeDequeModel` satisfies `DequeModel` | PROVEN given the 6 axioms | `nativeDequeModel` definition | in_tree_model_proof | yes |
| 22 | Native deque programs track the reference | PROVEN given the 6 axioms | `nativeDequeModel_qRun_tracks` | in_tree_model_proof | yes |
| 23 | `NativeDeque.toList_push` — push appends | ASSUMED | `NativeDeque.toList_push` axiom | in_tree_model_proof | yes |
| 24 | `NativeDeque.steal_{val,rest}` — steal removes head | ASSUMED | 2 axioms | in_tree_model_proof | yes |
| 25 | `NativeDeque.pop_{val,rest}` — pop removes last | ASSUMED | 2 axioms | in_tree_model_proof | yes |
| 26 | `NativeDeque.toList_empty` — empty observes `[]` | ASSUMED | `NativeDeque.toList_empty` axiom | in_tree_model_proof | yes |
| 27 | C deque race-freedom (concurrent steal + push) | OUTSCOPE | Requires Iris-style CSL | — | — |
| 28 | `@[extern]` C linkage, conformance differential tests | OUTSCOPE (planned follow-up work) | Planned for next iteration | — | — |

## v0.2.0 claims (invariants, ownership, time)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 29 | Every reachable state is well-formed | PROVEN | `reachable_wf` (`run_preserves_wf` ∘ `wf_init`) | in_tree_model_proof | yes |
| 30 | The scheduler never duplicates a ready task | PROVEN | `WellFormed.readyQ_nodup` in every reachable state | in_tree_model_proof | yes |
| 31 | A task occupies at most one ownership location (queued / running / timer) | PROVEN | `WellFormed.ready_not_running`, `WellFormed.ready_no_timer`, `WellFormed.running_no_timer` | in_tree_model_proof | yes |
| 32 | A spawned task's owner is immutable | PROVEN | `WellFormed.spawned_has_owner`, `reachable_spawned_has_owner` | in_tree_model_proof | yes |
| 33 | Invalid operations never mutate state | PROVEN | `step_invalid_unchanged` | in_tree_model_proof | yes |
| 34 | Logical time is monotone; backwards ticks are invalid no-ops | PROVEN | `step_clock_monotone`, `tick_backwards_invalid`, `tick_advances_clock` | in_tree_model_proof | yes |
| 35 | `tick` wakes only genuinely sleeping tasks | PROVEN + TESTED | filter in `step` + `WellFormed.timers_sleep`; demo scenario 6 | in_tree_model_proof | yes |

## v0.2.1 claims (strengthened invariant, RFC 019)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 36 | Timer queue sorted in every reachable state (now part of the single invariant) | PROVEN | `WellFormed.timers_sorted`, `reachable_timers_sorted` | in_tree_model_proof | yes |
| 37 | Every reachable spawned task has an owning actor | PROVEN | `reachable_spawned_has_owner` | in_tree_model_proof | yes |
| 38 | Every reachable owning actor has a mailbox | PROVEN | `reachable_owner_has_mailbox` | in_tree_model_proof | yes |
| 39 | Per-operation message non-duplication (value semantics; occurrence identity not modeled — see RFC 022) | PROVEN, scoped | `send_appends`, `receive_consumes_one` | in_tree_model_proof | yes |

## v0.3.0 claims (actor-scoped operations, RFC 024)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 40 | Actor-local receive discipline: a successful receive dequeues from the receiver's own actor's mailbox and touches no other mailbox | PROVEN | `receive_only_own` | in_tree_model_proof | yes |
| 41 | Only the running task sends/receives; unowned tasks cannot message | PROVEN | `send_not_running_invalid`, `send_unowned_invalid`, `receive_unowned_invalid` | in_tree_model_proof | yes |
| 42 | Messaging operations leave specific fields unconditionally unchanged (per projection; RFC 031 updates the scope — see row 10) | PROVEN | `Henret.Proofs.StepProjections` | in_tree_model_proof | yes |
| 43 | Messaging never removes a mailbox | PROVEN | `send/receive/inject_mailbox_isSome` | in_tree_model_proof | yes |
| 44 | All v0.2.1 invariants hold over the eleven-operation grammar | PROVEN | `reachable_wf` re-proved | in_tree_model_proof | yes |

## v0.4.0 claims (schedulable completeness + blocked receive)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 45 | The runtime never loses a runnable task: every reachable runnable task is queued | PROVEN | `reachable_runnable_is_queued` (`WellFormed.runnable_queued`) | in_tree_model_proof | yes |
| 46 | The ready queue contains exactly the runnable tasks in every reachable state | PROVEN | `reachable_queue_exact` | in_tree_model_proof | yes |
| 47 | Blocked receive is a parking transition (RFC 031): `taskState` → `.waiting`, `running` → `none`, task appended to its actor's `mailboxWaiters`; this replaces the v0.4.0 no-op characterisation | PROVEN | `receive_empty_parks`, `receive_blocked_parks` | in_tree_model_proof | yes |
| 48 | Empty own-mailbox receive is blocked and parks the task (legal wait-state transition), not invalid; illegal receive stays invalid | PROVEN + TESTED | `receive_empty_parks`, demo scenario 7 | in_tree_model_proof | yes |
| 49 | Past-deadline sleep policy: legal, wakes at next valid tick | DOCUMENTED (RFC 029) | `RuntimeOp.sleep` docstring | — | — |

## v0.5.0 claims (blocked waiting state + mailbox wait queue, RFC 031)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 50 | A blocked receive parks the running task in `TaskState.waiting` and removes it from `running` | PROVEN | `preserves_wf_receive` (parking branch) | in_tree_model_proof | yes |
| 51 | A parked task is in its owner actor's `mailboxWaiters` list and nowhere else | PROVEN | `WellFormed.waiters_owned`, `WellFormed.waiting_queued` in every reachable state | in_tree_model_proof | yes |
| 52 | The `mailboxWaiters` list for each actor contains only `.waiting` tasks | PROVEN | `WellFormed.waiters_waiting` in every reachable state | in_tree_model_proof | yes |
| 53 | Each actor's wait queue is duplicate-free | PROVEN | `WellFormed.waiters_nodup` in every reachable state | in_tree_model_proof | yes |
| 54 | A valid send/inject to an actor with a non-empty wait queue wakes exactly the head waiter to `.ready` and appends it to `readyQ` | PROVEN | `preserves_wf_send`, `preserves_wf_inject` (wake-one branches) | in_tree_model_proof | yes |
| 55 | Cancel removes the task from its actor's `mailboxWaiters` | PROVEN | `preserves_wf_cancel` (waiter sub-proofs) | in_tree_model_proof | yes |
| 56 | All 14 `WellFormed` fields hold in every reachable state | PROVEN | `reachable_wf` (extended from 10 fields) | in_tree_model_proof | yes |

## v0.6.0 claims (actor-scoped spawn / supervision groundwork, RFC 032)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 57 | A successful `spawnChild` sets the new task's parent to the calling task (`parentOwner`/`childActor` are distinct after RFC 038 generalization) | PROVEN | `spawnChild_sets_parent` | in_tree_model_proof | yes |
| 58 | A successful `spawnChild` sets the child's owner to `childActor` and enqueues it (RFC 038: no longer conflates parent owner with child actor) | PROVEN | `spawnChild_sets_owner`, `spawnChild_queues_child`, `spawnChild_child_spawned` | in_tree_model_proof | yes |
| 59 | Parenthood is immutable: no operation other than `spawnChild` writes `taskParent`, and `spawnChild` only writes the fresh slot | PROVEN | `step_preserves_parent` | in_tree_model_proof | yes |
| 60 | In every reachable state, every parent has a strictly smaller id than its child (parent_lt invariant) | PROVEN | `WellFormed.parent_lt`, `reachable_parent_lt` | in_tree_model_proof | yes |
| 61 | In every reachable state, every recorded parent exists in some state (parent_spawned invariant) | PROVEN | `WellFormed.parent_spawned` | in_tree_model_proof | yes |
| 62 | All ancestor chains terminate: every task reaches a root within `t` steps | PROVEN | `parent_chain_terminates` (acyclicity deliverable) | in_tree_model_proof | yes |
| 63 | All 21 `WellFormed` fields hold in every reachable state (RFC 038: extended from 19 to 21) | PROVEN | `reachable_wf` (extended) | in_tree_model_proof | yes |

## v0.9.1 claims (owner / parent exactness, RFC 038)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 85 | Every owned task is spawned: if `taskOwner t = some a` then `∃ st, taskState t = some st` | PROVEN | `WellFormed.owner_spawned`, `reachable_owner_spawned` | in_tree_model_proof | yes |
| 86 | Every task with a parent is itself spawned: if `taskParent t = some p` then `∃ st, taskState t = some st` | PROVEN | `WellFormed.parent_child_spawned`, `reachable_parent_child_spawned` | in_tree_model_proof | yes |
| 87 | `parentOwner` and `childActor` in `spawnChild` are independent; the child's actor is the argument, not derived from the parent | PROVEN | `spawnChild_sets_owner` (generalized in RFC 038) | in_tree_model_proof | yes |

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 64 | Every delivered envelope carries a unique occurrence id allocated from `nextMsgId` | PROVEN | `WellFormed.occ_fresh` in every reachable state | in_tree_model_proof | yes |
| 65 | Within each mailbox, all occurrence ids are distinct (per-mailbox uniqueness) | PROVEN | `WellFormed.occ_nodup` in every reachable state | in_tree_model_proof | yes |
| 66 | Across all mailboxes, all occurrence ids are distinct (global uniqueness) | PROVEN | `WellFormed.occ_disjoint` in every reachable state | in_tree_model_proof | yes |
| 67 | **Headline**: equal occurrence ids in any reachable mailboxes implies the same envelope in the same mailbox | PROVEN | `reachable_occurrence_unique` | in_tree_model_proof | yes |
| 68 | `send` stamps its envelope with `source = taskOwner t` (sender's actor) | PROVEN | `send_stamps_source` | in_tree_model_proof | yes |
| 69 | `inject` stamps its envelope with `source = none` (environment delivery) | PROVEN | `inject_stamps_none` | in_tree_model_proof | yes |
| 70 | All 19 `WellFormed` fields hold in every reachable state (extended from 16) | PROVEN | `reachable_wf` (extended) | in_tree_model_proof | yes |
| 71 | `MailboxBackend` contract updated: `enqueue/dequeue` now operate on `Envelope` | PROVEN | `Refinement.listBackend`, `Refinement.mailboxBackend` | in_tree_model_proof | yes |

## v0.8.0 / v0.9.0 claims (Lean-runtime bridge, RFC 035 skeleton → RFC 036 complete)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 72 | `QOp` grammar mirrors lean-runtime's queue-operation grammar plus `Filter` (RFC 036) | KERNEL | `Henret.Bridge.Grammar` (definition) | — | — |
| 73 | `toQOps` is guard-compatible: `toQOps s op = []` whenever `(step s op).2 = .invalid` | PROVEN | per-op invalid lemmas (`toQOps_*_invalid`, `toQOps_*_nil`) | in_tree_model_proof | yes |
| 74 | Every reachable henret state has a `BridgeState` witness | PROVEN | `reachable_bridge` (corollary of 80) | in_tree_model_proof | yes |
| 75 | `bridge_stable`: BridgeState preserved by readyQ-stable steps | PROVEN | `Henret.Bridge.bridge_stable` | in_tree_model_proof | yes |
| 76 | `bridge_spawn`: spawn step preserves BridgeState | PROVEN | `Henret.Bridge.bridge_spawn` | in_tree_model_proof | yes |
| 77 | `bridge_yield`: yield step preserves BridgeState | PROVEN | `Henret.Bridge.bridge_yield` | in_tree_model_proof | yes |
| 78 | `bridge_wake`: wake step preserves BridgeState (`Push 0 t` for sleeping task) | PROVEN | `Henret.Bridge.bridge_wake` | in_tree_model_proof | yes |
| 79 | `bridge_complete`, `bridge_receive`, `bridge_sleep`: readyQ-stable ops preserve BridgeState | PROVEN | `Henret.Bridge.bridge_complete/receive/sleep` | in_tree_model_proof | yes |
| 80 | `bridge_spawnChild`, `bridge_schedule`, `bridge_cancel`, `bridge_send`, `bridge_inject`, `bridge_tick`: all remaining ops preserve BridgeState (RFC 036) | PROVEN | `Henret.Bridge.*` | in_tree_model_proof | yes |
| 81 | `bridge_step_single_worker`: single unified bridge step for every RuntimeOp (single-worker) | PROVEN | `Henret.Bridge.bridge_step_single_worker` | in_tree_model_proof | yes |
| 82 | `bridge_run_tracks_single_worker`: trace-level bridge from init through any op sequence | PROVEN | `Henret.Bridge.bridge_run_tracks_single_worker` | in_tree_model_proof | yes |
| 83 | Bridge is a queue projection only: relates `readyQ` to worker 0; no fairness, no actor semantics | OUTSCOPE | Documented in `docs/bridge-architecture.md` | — | — |
| 84 | Multi-worker bridge extension | OUTSCOPE | Deferred to RFC 043 | — | — |

## v0.10.0 claims (cascade cancel, RFC 039)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 88 | `cancelTree root` sets every non-terminal spawned task in the subtree to `.cancelled` | PROVEN | `cancelTree_cancels_task`, `cancelTree_cancels_root` | in_tree_model_proof | yes |
| 89 | `cancelTree root` leaves every task outside the subtree with unchanged `taskState` | PROVEN | `cancelTree_preserves_task_state` | in_tree_model_proof | yes |
| 90 | After `cancelTree`, cancelled tasks are absent from `readyQ`, `timers`, and all `mailboxWaiters` | PROVEN | `cancelTree_removes_from_readyQ`, `cancelTree_removes_from_timers`, `cancelTree_removes_from_waiters` | in_tree_model_proof | yes |
| 91 | `cancelTree` always succeeds (returns `.ok`) regardless of `root` spawn status | PROVEN | `cancelTree_step_eq` (step returns `.ok`) | in_tree_model_proof | yes |
| 92 | All 21 `WellFormed` fields hold after `cancelTree` (preservation) | PROVEN | `preserves_wf_cancelTree` (in `Supervision.lean`) | in_tree_model_proof | yes |
| 93 | `descendantsOf s root` is duplicate-free (nodup) and bounded by `nextId` | PROVEN | `descendantsOf_nodup`, `descendantsOf_bound` | in_tree_model_proof | yes |
| 94 | `BridgeState` is preserved by `cancelTree`; `toQOps` emits `Filter 0 t` for each descendant | PROVEN | `bridge_cancelTree`, `bridge_step_single_worker` now covers 13 ops | in_tree_model_proof | yes |
| 95 | `isInSubtreeOf` is well-founded (terminates by `<` on `TaskId`; conservative `false` for non-decreasing chains) | PROVEN | Lean's well-founded recursion checker via `termination_by t` | in_tree_model_proof | yes |

## v0.11.0 claims (receive-timeout multi-wait, RFC 040)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 96 | `WellFormed` has 28 fields as of v0.11.0; all hold for every reachable state | PROVEN | `reachable_wf`, `wf_init` | in_tree_model_proof | yes |
| 97 | `receiveUntil t deadline` with available message: dequeues head envelope, returns `.received env`; WellFormed preserved | PROVEN | `preserves_wf_receiveUntil` (dequeue sub-case) | in_tree_model_proof | yes |
| 98 | `receiveUntil t deadline` with empty mailbox and past deadline: no-op, returns `.timedOut`; WellFormed preserved | PROVEN | `preserves_wf_receiveUntil` (past-deadline sub-case) | in_tree_model_proof | yes |
| 99 | `receiveUntil t deadline` with empty mailbox and future deadline: parks `t` to `.waitingTimed`, registers timer and deadline, appends to `timedMailboxWaiters a`; WellFormed preserved | PROVEN | `preserves_wf_receiveUntil` (park sub-case) | in_tree_model_proof | yes |
| 100 | Every `.waitingTimed` task has a `waitDeadline` entry and a timer entry | PROVEN | `WellFormed.timed_has_deadline`, `WellFormed.timed_has_timer` | in_tree_model_proof | yes |
| 101 | Every `.waitingTimed` task appears in exactly one `timedMailboxWaiters` list (exclusivity) | PROVEN | `WellFormed.timed_is_waiter`, `WellFormed.timed_waiters_exclusive` | in_tree_model_proof | yes |
| 102 | `tick t` wakes both `.sleeping` and `.waitingTimed` expired timers; both classes appended to `readyQ` | PROVEN | `preserves_wf_tick`, `bridge_tick` (updated for RFC 040) | in_tree_model_proof | yes |
| 103 | `send`/`inject` fall through to timed waiters when `mailboxWaiters` is empty | PROVEN | `preserves_wf_send`, `preserves_wf_inject` (timed-waiter branches) | in_tree_model_proof | yes |
| 104 | `BridgeState` preserved by `receiveUntil` (emits `[]`; no readyQ effect) | PROVEN | `bridge_step_single_worker` (receiveUntil case) | in_tree_model_proof | yes |
| 105 | `bridge_step_single_worker` covers every `RuntimeOp` (universally quantified) including `receiveUntil` | PROVEN | `Henret.Bridge.bridge_step_single_worker` | in_tree_model_proof | yes |

## v0.11.1 claims (selective receive, RFC 041)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 106 | `receiveByOccurrence t occ` with a matching envelope: removes exactly that envelope, returns `.received env` where `env.occurrence = occ`; relative order of nonmatching envelopes preserved | PROVEN | `receiveByOccurrence_removes_matching`, `receiveByOccurrence_preserves_nonmatching_order` | in_tree_model_proof | yes |
| 107 | `receiveFrom t src` with a matching envelope: removes exactly that envelope, returns `.received env` where `env.source = some src`; relative order of nonmatching envelopes preserved | PROVEN | `receiveFrom_source_matches`, `receiveFrom_preserves_nonmatching_order` | in_tree_model_proof | yes |
| 108 | `receiveByOccurrence`/`receiveFrom` with no matching envelope: parks `t` in `mailboxWaiters a`, returns `.blocked` (Option A / Mesa semantics) | PROVEN | `receiveByOccurrence_parks_on_miss`, `receiveFrom_parks_on_miss` | in_tree_model_proof | yes |
| 109 | All 28 `WellFormed` fields preserved by `receiveByOccurrence` and `receiveFrom` | PROVEN | `preserves_wf_receiveByOccurrence`, `preserves_wf_receiveFrom` | in_tree_model_proof | yes |
| 110 | `dequeueFirst` removes exactly one envelope while preserving all others in order | PROVEN | `listDequeueFirst_sublist`, `listDequeueFirst_matches`, `listDequeueFirst_mem`, `listDequeueFirst_none` | in_tree_model_proof | yes |
| 111 | Blocking is mailbox-level, not selector-level (Option A): any delivery to the actor wakes a parked selective-receive task | DOCUMENTED | Mesa semantics; `receiveByOccurrence_parks_on_miss` shows parking in `mailboxWaiters` | — | — |
| 112 | `bridge_step_single_worker` covers all 16 `RuntimeOp`s including `receiveByOccurrence` and `receiveFrom` | PROVEN | `bridge_step_single_worker` (both emit `[]`, readyQ unchanged) | in_tree_model_proof | yes |

## v0.12.0 claims (multi-worker bridge, RFC 043)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 113 | `MultiBridgeState` relates henret `readyQ` to the union of worker queues by membership (soundness + completeness + global uniqueness + per-worker nodup) | PROVEN | `MultiBridgeState` (structure) | in_tree_model_proof | yes |
| 114 | The single-worker `BridgeState` is a strict special case of `MultiBridgeState` (given `readyQ.Nodup`) | PROVEN | `single_bridge_implies_multi_bridge` | in_tree_model_proof | yes |
| 115 | `Push w t` of a fresh task preserves the multi-worker membership relation | PROVEN | `multi_bridge_push` | in_tree_model_proof | yes |
| 116 | `Filter w t` preserves the relation, mirroring `readyQ.filter (· ≠ t)` | PROVEN | `multi_bridge_filter` | in_tree_model_proof | yes |
| 117 | Work stealing (`Steal src dst`, src ≠ dst) preserves membership: the stolen task moves between workers without leaving the ready set | PROVEN | `multi_bridge_steal` | in_tree_model_proof | yes |
| 118 | Every reachable state has a worker-queue witness satisfying `MultiBridgeState` | PROVEN | `reachable_multi_bridge` | in_tree_model_proof | yes |
| 119 | Multi-worker bridge preserves membership, not order (work stealing does not preserve a global ready order) | DOCUMENTED | `docs/bridge-architecture.md`; relation is set-based by construction | — | — |
| 120 | No worker-placement field added to `RuntimeState`; worker assignment is bridge-level only | PROVEN | `RuntimeState` unchanged; `MultiBridgeState` over `WorkerQueues` | in_tree_model_proof | yes |

## v0.13.0 claims (execution trace ledger, RFC 045)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 121 | `stepTrace` agrees with `step` on resulting state and result (by construction) | PROVEN | `stepTrace_state_eq_step`, `stepTrace_result_eq_step` | in_tree_model_proof | yes |
| 122 | `runTraceLedger` agrees with `run` on final state | PROVEN | `runTraceLedger_state_eq_run` | in_tree_model_proof | yes |
| 123 | `runTraceLedger` agrees with `runTrace` on the per-op result list | PROVEN | `runTraceLedger_results_eq_runTrace` | in_tree_model_proof | yes |
| 124 | A `received` event certifies the dequeue actually occurred with the stated occurrence | PROVEN | `event_received_sound` | in_tree_model_proof | yes |
| 125 | A `parked` event certifies the receiver is now `.waiting` and queued in the actor's waiter list | PROVEN | `event_parked_sound` | in_tree_model_proof | yes |
| 126 | A `directWoke` event certifies the task was `.sleeping` | PROVEN | `event_directWoke_sound` | in_tree_model_proof | yes |
| 127 | A `timerWoke now t` event certifies `now` is not in the past and `t`'s timer expired by `now` | PROVEN | `event_timerWoke_sound` | in_tree_model_proof | yes |
| 128 | A `spawnChild` event certifies the parent was running and the child is the fresh `nextId` | PROVEN | `event_spawnChild_sound` | in_tree_model_proof | yes |
| 129 | A `scheduled t` event certifies nothing was running and `t` was the runnable `readyQ` head | PROVEN | `event_scheduled_sound` | in_tree_model_proof | yes |
| 130 | A `waiterWoke` event from `send` certifies the woken task is the head of the actor's waiter list | PROVEN | `event_waiterWoke_send_sound` | in_tree_model_proof | yes |
| 131 | Trace events are a model-level observation layer; not yet frozen as public API | DOCUMENTED | `docs/trace-ledger.md` (deferred to RFC 052) | — | — |

## v0.13.1 claims (golden trace conformance, RFC 047)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 132 | Ten golden scenarios encode Henret's canonical observable behavior (lifecycle, yield, sleep/tick, park, send/inject Mesa wake, cancel, spawnChild, occurrence uniqueness) | PROVEN | `goldenScenarios`, `conformance_suite_passes` | in_tree_model_proof | yes |
| 133 | Every golden scenario's observed trace equals its checked-in expected trace (kernel-checked, no native_decide) | PROVEN | `conformance_suite_passes` (`by decide`) | in_tree_model_proof | yes |
| 134 | Every kernel-reducible RFC 083 branch scenario's observed StepResult sequence and final-state predicate match (negative/security cases incl. Mesa re-park; cancelTree runtime-checked) | PROVEN | `branch_suite_passes` (`by decide`) | in_tree_model_proof | yes |
| 135 | Every executable RuntimeOp branch is tied to an existing golden scenario and no scenario claims unregistered coverage | PROVEN | `coverage_complete` (`by decide`) | in_tree_model_proof | yes |
| 134 | The conformance suite is executable and reports the first mismatching event on failure | TESTED | `lake exe henret-conformance`, `firstMismatch`, `scenarioReport` | in_tree_model_test | yes |
| 135 | Trace refinement is exact equality for single-worker conformance; relaxed matching deferred until a multi-worker adapter exists | DOCUMENTED | `TraceRefines`, `docs/conformance-suite.md` | — | — |
| 136 | External runtimes need only expose the observable event stream, not internal queues | DOCUMENTED | `docs/conformance-suite.md` adapter contract | — | — |

## v0.14.0 claims (fairness / conditional liveness, RFC 046)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 137 | The FIFO head of `readyQ` is the next task scheduled (unconditional, local progress) | PROVEN | `schedule_schedules_head`, `head_scheduled_within_one` | in_tree_model_proof | yes |
| 138 | Under an explicit bounded-fairness assumption, a runnable task is scheduled within the window | PROVEN (conditional) | `ready_eventually_scheduled_under_bounded_fairness` | in_tree_model_proof | yes |
| 139 | Whole-program fairness is NOT unconditional: an op sequence that stops scheduling starves runnable tasks | PROVEN | `unfairOps_not_bounded_fair_0`, `unfair_task1_never_scheduled` | in_tree_model_proof | yes |
| 140 | A fair op sequence schedules each runnable task | PROVEN | `fair_task0_scheduled`, `fair_task1_scheduled` | in_tree_model_proof | yes |
| 141 | No unconditional liveness is added to `reachable_wf`; safety and liveness layers stay separate | DOCUMENTED | `docs/progress-policy.md`; `WellFormed` unchanged | — | — |

## v0.14.1 claims (bounded model explorer, RFC 048)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 142 | The explorer enumerates all op sequences up to a bounded depth | TESTED | `genPrograms`, `henret-explore` (25,260 programs at default depth 3) | in_tree_model_test | yes |
| 143 | Well-formedness, occurrence uniqueness, and single-worker bridge tracking hold over the entire bounded sample | TESTED (confirms proven invariants) | `confirms ... propWellFormed/propOccurrenceUnique/propBridge` | in_tree_model_test | yes |
| 144 | The explorer finds and minimizes a deliberately false property to its shortest counterexample | TESTED | `findAndShrink ... propReadyAlwaysEmpty` → `[spawn 0]` | in_tree_model_test | yes |
| 145 | The explorer is empirical model-search support, not a proof; checkers are bounded necessary conditions only | DOCUMENTED | `docs/model-explorer.md`; `HenretExplore` outside default import | — | — |
| 146 | The explorer does not affect the verified model or its axiom budget | PROVEN (by construction) | separate Lake library; `import Henret` unchanged | in_tree_model_proof | yes |

## v0.15.0 claims (supervision restart policies, RFC 049)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 147 | Failure (`.failed`) is a terminal state distinct from cancellation | PROVEN | `TaskState.failed`, `isTerminal_failed`, `step_preserves_terminal` | in_tree_model_proof | yes |
| 148 | `fail` and `restartOne` preserve the 33-field WellFormed invariant | PROVEN | `preserves_wf_fail`, `preserves_wf_restartOne` | in_tree_model_proof | yes |
| 149 | A restart creates a fresh task id strictly greater than the failed one | PROVEN | `reachable_restart_fresh` | in_tree_model_proof | yes |
| 150 | The task replaced by a restart is failed | PROVEN | `reachable_restart_old_failed` | in_tree_model_proof | yes |
| 151 | A restart replacement shares the failed task's supervising parent | PROVEN | `reachable_restart_parent_consistent` | in_tree_model_proof | yes |
| 152 | Parent acyclicity is preserved across restart | PROVEN | `restart_preserves_parent_acyclicity` | in_tree_model_proof | yes |
| 153 | A restarted task has an owning actor | PROVEN | `restarted_task_has_owner` | in_tree_model_proof | yes |
| 154 | Restart provenance is inspectable via `restartOf` and the trace ledger | TESTED/DOCUMENTED | `examples/12_supervision_restart.lean`, `TraceEvent.restarted` | in_tree_model_test | yes |
| 155 | No liveness claim is made; restart occurs only on an explicit `restartOne` | DOCUMENTED | `docs/supervision-restart.md` | — | — |

## v0.15.1 claims (observability / visualization, RFC 050)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 156 | States, traces, and actor/task relations have human-readable renderers | TESTED | `examples/13_trace_rendering.lean`, `examples/14_state_diagrams.lean` | in_tree_model_test | yes |
| 157 | Renderers cover ready/waiting/sleeping/running/completed/cancelled/failed tasks | TESTED | `Render.taskLocation`, `Render.stateWord` | in_tree_model_test | yes |
| 158 | Mermaid output is valid for Markdown preview tools | DOCUMENTED | `docs/observability.md` (rendered parent tree) | — | — |
| 159 | Renderers add no theorems and do not affect the axiom budget | PROVEN (by construction) | pure `String` functions; `import Henret` axiom audit unchanged | in_tree_model_proof | yes |

## v0.16.0 claims (semantic profiles, RFC 054)

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 160 | Named profiles (`core`/`actor`/`full`) have no duplicate features | PROVEN | `Profile.core/actor/full` `nodup` field (`by decide`) | in_tree_model_proof | yes |
| 161 | Profile inclusion forms the chain `core ≤ actor ≤ full` | PROVEN | `core_le_actor`, `actor_le_full`, `core_le_full` | in_tree_model_proof | yes |
| 162 | Profile inclusion is a preorder (reflexive, transitive) | PROVEN | `SemanticProfile.le_refl`, `SemanticProfile.le_trans` | in_tree_model_proof | yes |
| 163 | Each headline theorem is classified by its minimum profile | DOCUMENTED | `docs/profile-index.md` | — | — |
| 164 | Profiles are metadata only — no existing theorem or `step`/`run` behavior changes | PROVEN (by construction) | `Henret/Profile.lean` adds no model dependency; `import Henret` behavior additive | in_tree_model_proof | yes |

## v0.17.0 claims (structured cancellation / shutdown, RFC 055)

All claims here are **safety-only**: no fairness, liveness, or guaranteed-quiescence claim is made.

| # | Claim | Class | Evidence | Location | Verified here |
|---:|---|---|---|---|:---:|
| 165 | Closing an actor with a mailbox sets its status to `.closed` | PROVEN | `closeActor_sets_closed` | in_tree_model_proof | yes |
| 166 | Closing never deletes or alters any mailbox (queued messages still drain via `receive`) | PROVEN | `closeActor_preserves_mailboxes`, `closeActor_preserves_other_status` | in_tree_model_proof | yes |
| 167 | A `.closed` actor rejects every `send` and environment `inject` targeting it | PROVEN | `closed_actor_rejects_send`, `closed_actor_rejects_inject` | in_tree_model_proof | yes |
| 168 | A non-`running` runtime rejects root `spawn` and environment `inject` | PROVEN | `shutdown_rejects_spawn`, `shutdown_rejects_inject`, `shutdown_sets_status` | in_tree_model_proof | yes |
| 169 | `stopWhenIdle` reaches `.stopped` only from a quiescent state | PROVEN | `stopWhenIdle_requires_quiescent`, `stopWhenIdle_sets_stopped` | in_tree_model_proof | yes |
| 170 | The admission-status fields are `WellFormed`-irrelevant; the 28-field base contract is unchanged | PROVEN | `WellFormed.status_irrel`, `preserves_wf_{closeActor,shutdown,stopWhenIdle}` | in_tree_model_proof | yes |
| 171 | The new ops are queue-stable under the single-worker bridge | PROVEN | `bridge_closeActor`, `bridge_shutdown`, `bridge_stopWhenIdle` | in_tree_model_proof | yes |
| 172 | Subtree cancellation reuses `cancelTree` (RFC 039); no new cancellation op | DOCUMENTED | `cancelTree_cancels_task`, `cancelTree_preserves_task_state`, `docs/shutdown-semantics.md` | — | — |
| 173 | No liveness or eventual-quiescence claim is introduced | DOCUMENTED | `docs/shutdown-semantics.md`, `examples/16_structured_shutdown.lean` | — | — |
| 174 | No reachable mailbox ever exceeds its configured capacity (`WellFormed` field 29; vacuous under the default unbounded policy) | PROVEN | `reachable_mailbox_within_capacity`, `wf_init` | in_tree_model_proof | yes |
| 175 | A valid `send`/`inject` to a full mailbox is rejected with `.backpressured` (Option A, reject-only) | PROVEN | `send_full_backpressured`, `inject_full_backpressured` | in_tree_model_proof | yes |
| 176 | `.backpressured` is a no-op: the state is unchanged and no occurrence id is consumed | PROVEN | `step_backpressured_unchanged`, `backpressured_not_invalid` | in_tree_model_proof | yes |
| 177 | Under the default unbounded policy `send`/`inject` are never backpressured (behaviourally identical to pre-RFC-056) | PROVEN | `send_unbounded_not_backpressured`, `inject_unbounded_not_backpressured` | in_tree_model_proof | yes |
| 178 | A full mailbox with a parked Mesa waiter still backpressures further delivery (a waiter does not imply an empty mailbox) | PROVEN | `branch_suite_passes` (`full_mailbox_with_waiter_{send,inject}_backpressured`) | in_tree_model_proof | yes |
| 179 | Capacity-zero is a documented reject-all policy: every `send`/`inject` is backpressured | PROVEN | `branch_suite_passes` (`capacity_zero_{send,inject}_backpressured`) | in_tree_model_proof | yes |
| 180 | The single-worker bridge stays queue-stable under backpressure (`toQOps` emits `[]` for a full mailbox) | PROVEN | `bridge_send`, `bridge_inject` | in_tree_model_proof | yes |
| 181 | Park-policy overflow (Option B: blocking senders) is out of scope and not implemented | DOCUMENTED | `docs/migration/v0.17-to-v0.18.md`, RFC 056 | — | — |
| 182 | A running task's `acquire` allocates a fresh task-owned `allocated` resource and advances the counter; the result is `.acquired` of the old id | PROVEN | `acquire_running_allocates`, `nextResourceId_monotone_step` | in_tree_model_proof | yes |
| 183 | The owning running task's `release` flips its `allocated` resource to `released`; a non-owner or non-`allocated` release is `.invalid` | PROVEN | `release_owner_allocated_ok`, `release_non_owner_invalid`, `release_released_invalid`, `release_closing_invalid` | in_tree_model_proof | yes |
| 184 | `finalize` flips a `closing` resource to `released` with no running-task guard; a non-`closing` finalize is `.invalid` | PROVEN | `finalize_closing_ok`, `finalize_allocated_invalid`, `finalize_released_invalid` | in_tree_model_proof | yes |
| 185 | When an owner goes terminal (`complete`/`cancel`/`fail`/`cancelTree`) its `allocated` resources are moved to `closing` | PROVEN | `complete_marks_owned_resource_closing`, `cancel_marks_owned_resource_closing`, `fail_marks_owned_resource_closing`, `cancelTree_marks_descendant_resource_closing` | in_tree_model_proof | yes |
| 186 | A live task never owns a `closing` resource and a terminal task never owns an `allocated` one (carried across all 24 ops) | PROVEN | `reachable_allocated_owner_nonterminal`, `reachable_closing_owner_terminal`, `preserves_wf_acquire`, `preserves_wf_release`, `preserves_wf_finalize` | in_tree_model_proof | yes |
| 187 | The allocation counter never decreases along a run, so resource ids are never reused | PROVEN | `nextResourceId_monotone_run` | in_tree_model_proof | yes |
| 188 | Every reachable resource is owned by a spawned task and ids at/above the counter are unallocated | PROVEN | `reachable_resource_owner_spawned`, `reachable_resource_fresh` | in_tree_model_proof | yes |
| 189 | The full acquire→release and acquire→cancel→finalize lifecycles, and every rejection branch, execute as specified end-to-end | TESTED | `branch_suite_passes` (`resource_*`), `coverage_complete` | in_tree_model_proof | yes |
| 190 | Physical reclamation of the native resource on `finalize` (FFI close/free) | TRUSTED | native-finalizer trust boundary; `docs/resource-lifetime.md` | trusted_boundary | — |
| 191 | Liveness/timeliness of finalization, drain-before-stop, actor-owned resources, and resource transfer across `restartOne` are out of scope for Tier 1 | DOCUMENTED | `docs/migration/v0.18-to-v0.19.md`, RFC 057 | — | — |
| 192 | `released` is a terminal ledger state: a released resource stays released under every operation and in every reachable future (the ledger only moves records forward) | PROVEN | `released_resource_never_live_step`, `released_resource_never_live_run`, `reachable_released_resource_never_live` | in_tree_model_proof | yes |
| 193 | Execution outcomes are classified into a total taxonomy (`progress`/`waiting`/`timeout`/`protocolInvalid`); every `StepResult` is classified | PROVEN | `faultClass` (total), `scripts/fault_taxonomy_check.py` | in_tree_model_proof | yes |
| 194 | Ordinary waiting (`blocked`/`backpressured`) and timeout (`timedOut`) are distinct classes from protocol invalidity (`invalid`) and are not faults | PROVEN | `blocked_not_invalid_class`, `backpressured_not_invalid_class`, `timedOut_not_invalid_class`, `blocked_not_fault`, `backpressured_not_fault`, `timedOut_not_fault` | in_tree_model_proof | yes |
| 195 | Cancellation, task fault, supervisor fault, runtime-adapter failure, and trusted-backend failure are documented taxonomy classes; task-fault payloads, supervisor signals, and adapter/backend faults are state-level or out-of-model (reserved/not StepResult) | DOCUMENTED | `docs/fault-taxonomy.md`, RFC 064 | — | — |
| 196 | A scheduling policy can reorder which ready task runs next but only ever picks a ready task (`choose_sound`); reordering preserves all 33 `WellFormed` fields | PROVEN | `reorder_preserves_wf`, `SchedulingPolicy.choose_sound` | in_tree_model_proof | yes |
| 197 | Every scheduling policy (FIFO, LIFO, any sound policy) preserves `WellFormed` and never creates a task; the FIFO policy equals the core `schedule` | PROVEN | `policyStep_preserves_wf`, `policy_does_not_create_task`, `fifo_policy_equiv_schedule` | in_tree_model_proof | yes |
| 198 | Policy choice changes ordering, not core safety; the core scheduler is unchanged and no fairness is claimed | DOCUMENTED | `docs/scheduling-policy.md`, RFC 058 | — | — |
| 199 | Optional per-task priority/deadline metadata; `setPriority`/`setDeadline` are guarded on spawned tasks and preserve all 33 `WellFormed` fields (metadata is not part of the invariant) | PROVEN | `preserves_wf_setPriority`, `preserves_wf_setDeadline`, `wf_taskMeta_only`, `setPriority_meta_of_spawned` | in_tree_model_proof | yes |
| 200 | The three metadata policies (priority, EDF, hybrid) are sound — the chosen task is always ready — and inherit full `WellFormed` preservation from the policy layer | PROVEN | `pickBy_mem`, `priorityPolicy.choose_sound`, `edfPolicy.choose_sound`, `hybridPolicy.choose_sound` | in_tree_model_proof | yes |
| 201 | The highest-priority policy selects a ready task with maximal priority among ready tasks | PROVEN | `priority_policy_selects_max`, `foldl_best_ge` | in_tree_model_proof | yes |
| 202 | Deadlines are logical-time ordering metadata only; no theorem claims a deadline is met, and a deadline can be missed without a liveness policy | DOCUMENTED | `docs/deadline-priority.md`, RFC 059 | — | — |
| 203 | The earliest-deadline-first policy selects a ready task whose deadline is minimal — no ready task is strictly earlier (an ordering fact, not a real-time guarantee) | PROVEN | `deadline_policy_selects_min_deadline`, `foldl_winner`, `deadlineLt_irrefl` | in_tree_model_proof | yes |
| 204 | Drain progress: a `closing` resource is always finalizable in one step, so (with Tier-1 terminal-marks-closing) the drain path is never blocked | PROVEN | `closing_finalize_releases` | in_tree_model_proof | yes |
| 205 | The additive `stopWhenDrained` operation reaches `stopped` only when quiescent and the ledger is fully drained; a drained stop never leaves a resource leaked. Preserves all 33 `WellFormed` fields | PROVEN | `stopWhenDrained_stops_drained`, `resourceDrained_drained`, `stopWhenDrained_stops`, `stopWhenDrained_noop`, `preserves_wf_stopWhenDrained` | in_tree_model_proof | yes |
| 206 | Drain discipline is a safety/possibility guarantee only — no theorem claims a resource is eventually finalized or that a stop eventually happens (no wall-clock liveness) | DOCUMENTED | `docs/resource-drain.md`, RFC 087 | — | — |
| 207 | From a drained state with no running task, every operation preserves `Drained`: an existing resource stays `released` and no new resource can appear (`acquire` is blocked without a running task) | PROVEN | `drained_step_drained`, `step_resources_none_run_none` | in_tree_model_proof | yes |
| 208 | Immediately after a successful `stopWhenDrained`, the next operation cannot leak a resource (the post-stop state keeps `running = none` and the unchanged ledger) | PROVEN | `stopWhenDrained_then_step_drained` | in_tree_model_proof | yes |
| 209 | Drained-state persistence is proven for a single step only; multi-step permanence is deferred because it requires a `sleeping → timer` invariant (the converse of `timers_sleep`) not yet in `WellFormed` | DOCUMENTED | `docs/resource-drain.md`, RFC 088 | — | — |
| 210 | Every sleeping task has a registered timer, in every reachable state (the converse of the timers→sleeping well-formedness field) | PROVEN | `reachable_sleepingHasTimer`, `step_preserves_sleepingHasTimer` | in_tree_model_proof | yes |
| 211 | A quiescent runtime (empty timer queue) has no sleeping tasks | PROVEN | `quiescent_no_sleeping` | in_tree_model_proof | yes |
| 212 | Multi-step drained permanence and "stopped stays quiescent" — proven in RFC 090 via the `Frozen` bundle invariant built on claims 210/211 | PROVEN | `reachable_stopWhenDrained_stays_drained`, `reachable_stopWhenDrained_stays_quiescent` | in_tree_model_proof | yes |
| 213 | The `Frozen` bundle (no running task, empty ready/timer queues, non-running status, drained) is preserved by every operation | PROVEN | `step_preserves_frozen` | in_tree_model_proof | yes |
| 214 | From any reachable state, after a successful `stopWhenDrained`, the runtime stays drained across every subsequent operation sequence (permanent, not single-step) | PROVEN | `reachable_stopWhenDrained_stays_drained` | in_tree_model_proof | yes |
| 215 | Likewise the runtime stays quiescent (no running task, empty ready/timer queues) across every subsequent operation sequence | PROVEN | `reachable_stopWhenDrained_stays_quiescent` | in_tree_model_proof | yes |
