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
| 7 | one successful `send`/`inject` appends exactly one message *value* to exactly the target mailbox (per-operation; occurrence identity not modeled, RFC 022) | PROVEN | `send_appends`, `inject_appends`, `*_preserves_other` |
| 8 | `receive` consumes exactly one message (the head) | PROVEN | `receive_consumes_one`, `receive_length` |
| 9 | `receive` from an empty own mailbox is **blocked** and parks the task: `taskState` → `.waiting`, `running` → `none`, task appended to `mailboxWaiters` (RFC 031); non-running/unowned receive remains invalid | PROVEN | `receive_empty_parks`, `receive_blocked_parks`, `receive_unowned_invalid` |
| 10 | Per-operation unconditionally-unchanged fields (RFC 031 updates): `send`/`inject` leave `taskOwner`, `running`, `timers`, `now`, `nextId` invariant; `receive` leaves `taskOwner`, `readyQ`, `timers`, `now`, `nextId` invariant | PROVEN | `Henret.Proofs.StepProjections` (e.g. `send_taskOwner`, `receive_readyQ`, `inject_taskOwner`) |
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
| 31 | A task occupies at most one ownership location (queued / running / timer) | PROVEN | `WellFormed.ready_not_running`, `WellFormed.ready_no_timer`, `WellFormed.running_no_timer` |
| 32 | A spawned task's owner is immutable | PROVEN | `WellFormed.spawned_has_owner`, `reachable_spawned_has_owner` |
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

## v0.3.0 claims (actor-scoped operations, RFC 024)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 40 | Actor-local receive discipline: a successful receive dequeues from the receiver's own actor's mailbox and touches no other mailbox | PROVEN | `receive_only_own` |
| 41 | Only the running task sends/receives; unowned tasks cannot message | PROVEN | `send_not_running_invalid`, `send_unowned_invalid`, `receive_unowned_invalid` |
| 42 | Messaging operations leave specific fields unconditionally unchanged (per projection; RFC 031 updates the scope — see row 10) | PROVEN | `Henret.Proofs.StepProjections` |
| 43 | Messaging never removes a mailbox | PROVEN | `send/receive/inject_mailbox_isSome` |
| 44 | All v0.2.1 invariants hold over the eleven-operation grammar | PROVEN | `reachable_wf` re-proved |

## v0.4.0 claims (schedulable completeness + blocked receive)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 45 | The runtime never loses a runnable task: every reachable runnable task is queued | PROVEN | `reachable_runnable_is_queued` (`WellFormed.runnable_queued`) |
| 46 | The ready queue contains exactly the runnable tasks in every reachable state | PROVEN | `reachable_queue_exact` |
| 47 | Blocked receive is a parking transition (RFC 031): `taskState` → `.waiting`, `running` → `none`, task appended to its actor's `mailboxWaiters`; this replaces the v0.4.0 no-op characterisation | PROVEN | `receive_empty_parks`, `receive_blocked_parks` |
| 48 | Empty own-mailbox receive is blocked and parks the task (legal wait-state transition), not invalid; illegal receive stays invalid | PROVEN + TESTED | `receive_empty_parks`, demo scenario 7 |
| 49 | Past-deadline sleep policy: legal, wakes at next valid tick | DOCUMENTED (RFC 029) | `RuntimeOp.sleep` docstring |

## v0.5.0 claims (blocked waiting state + mailbox wait queue, RFC 031)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 50 | A blocked receive parks the running task in `TaskState.waiting` and removes it from `running` | PROVEN | `preserves_wf_receive` (parking branch) |
| 51 | A parked task is in its owner actor's `mailboxWaiters` list and nowhere else | PROVEN | `WellFormed.waiters_owned`, `WellFormed.waiting_queued` in every reachable state |
| 52 | The `mailboxWaiters` list for each actor contains only `.waiting` tasks | PROVEN | `WellFormed.waiters_waiting` in every reachable state |
| 53 | Each actor's wait queue is duplicate-free | PROVEN | `WellFormed.waiters_nodup` in every reachable state |
| 54 | A valid send/inject to an actor with a non-empty wait queue wakes exactly the head waiter to `.ready` and appends it to `readyQ` | PROVEN | `preserves_wf_send`, `preserves_wf_inject` (wake-one branches) |
| 55 | Cancel removes the task from its actor's `mailboxWaiters` | PROVEN | `preserves_wf_cancel` (waiter sub-proofs) |
| 56 | All 14 `WellFormed` fields hold in every reachable state | PROVEN | `reachable_wf` (extended from 10 fields) |

## v0.6.0 claims (actor-scoped spawn / supervision groundwork, RFC 032)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 57 | A successful `spawnChild` sets the new task's parent to the calling task (`parentOwner`/`childActor` are distinct after RFC 038 generalization) | PROVEN | `spawnChild_sets_parent` |
| 58 | A successful `spawnChild` sets the child's owner to `childActor` and enqueues it (RFC 038: no longer conflates parent owner with child actor) | PROVEN | `spawnChild_sets_owner`, `spawnChild_queues_child`, `spawnChild_child_spawned` |
| 59 | Parenthood is immutable: no operation other than `spawnChild` writes `taskParent`, and `spawnChild` only writes the fresh slot | PROVEN | `step_preserves_parent` |
| 60 | In every reachable state, every parent has a strictly smaller id than its child (parent_lt invariant) | PROVEN | `WellFormed.parent_lt`, `reachable_parent_lt` |
| 61 | In every reachable state, every recorded parent exists in some state (parent_spawned invariant) | PROVEN | `WellFormed.parent_spawned` |
| 62 | All ancestor chains terminate: every task reaches a root within `t` steps | PROVEN | `parent_chain_terminates` (acyclicity deliverable) |
| 63 | All 21 `WellFormed` fields hold in every reachable state (RFC 038: extended from 19 to 21) | PROVEN | `reachable_wf` (extended) |

## v0.9.1 claims (owner / parent exactness, RFC 038)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 85 | Every owned task is spawned: if `taskOwner t = some a` then `∃ st, taskState t = some st` | PROVEN | `WellFormed.owner_spawned`, `reachable_owner_spawned` |
| 86 | Every task with a parent is itself spawned: if `taskParent t = some p` then `∃ st, taskState t = some st` | PROVEN | `WellFormed.parent_child_spawned`, `reachable_parent_child_spawned` |
| 87 | `parentOwner` and `childActor` in `spawnChild` are independent; the child's actor is the argument, not derived from the parent | PROVEN | `spawnChild_sets_owner` (generalized in RFC 038) |

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 64 | Every delivered envelope carries a unique occurrence id allocated from `nextMsgId` | PROVEN | `WellFormed.occ_fresh` in every reachable state |
| 65 | Within each mailbox, all occurrence ids are distinct (per-mailbox uniqueness) | PROVEN | `WellFormed.occ_nodup` in every reachable state |
| 66 | Across all mailboxes, all occurrence ids are distinct (global uniqueness) | PROVEN | `WellFormed.occ_disjoint` in every reachable state |
| 67 | **Headline**: equal occurrence ids in any reachable mailboxes implies the same envelope in the same mailbox | PROVEN | `reachable_occurrence_unique` |
| 68 | `send` stamps its envelope with `source = taskOwner t` (sender's actor) | PROVEN | `send_stamps_source` |
| 69 | `inject` stamps its envelope with `source = none` (environment delivery) | PROVEN | `inject_stamps_none` |
| 70 | All 19 `WellFormed` fields hold in every reachable state (extended from 16) | PROVEN | `reachable_wf` (extended) |
| 71 | `MailboxBackend` contract updated: `enqueue/dequeue` now operate on `Envelope` | PROVEN | `Refinement.listBackend`, `Refinement.mailboxBackend` |

## v0.8.0 / v0.9.0 claims (Lean-runtime bridge, RFC 035 skeleton → RFC 036 complete)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 72 | `QOp` grammar mirrors lean-runtime's queue-operation grammar plus `Filter` (RFC 036) | KERNEL | `Henret.Bridge.Grammar` (definition) |
| 73 | `toQOps` is guard-compatible: `toQOps s op = []` whenever `(step s op).2 = .invalid` | PROVEN | per-op invalid lemmas (`toQOps_*_invalid`, `toQOps_*_nil`) |
| 74 | Every reachable henret state has a `BridgeState` witness | PROVEN | `reachable_bridge` (corollary of 80) |
| 75 | `bridge_stable`: BridgeState preserved by readyQ-stable steps | PROVEN | `Henret.Bridge.bridge_stable` |
| 76 | `bridge_spawn`: spawn step preserves BridgeState | PROVEN | `Henret.Bridge.bridge_spawn` |
| 77 | `bridge_yield`: yield step preserves BridgeState | PROVEN | `Henret.Bridge.bridge_yield` |
| 78 | `bridge_wake`: wake step preserves BridgeState (`Push 0 t` for sleeping task) | PROVEN | `Henret.Bridge.bridge_wake` |
| 79 | `bridge_complete`, `bridge_receive`, `bridge_sleep`: readyQ-stable ops preserve BridgeState | PROVEN | `Henret.Bridge.bridge_complete/receive/sleep` |
| 80 | `bridge_spawnChild`, `bridge_schedule`, `bridge_cancel`, `bridge_send`, `bridge_inject`, `bridge_tick`: all remaining ops preserve BridgeState (RFC 036) | PROVEN | `Henret.Bridge.*` |
| 81 | `bridge_step_single_worker`: single unified bridge step for all 12 RuntimeOps | PROVEN | `Henret.Bridge.bridge_step_single_worker` |
| 82 | `bridge_run_tracks_single_worker`: trace-level bridge from init through any op sequence | PROVEN | `Henret.Bridge.bridge_run_tracks_single_worker` |
| 83 | Bridge is a queue projection only: relates `readyQ` to worker 0; no fairness, no actor semantics | OUTSCOPE | Documented in `docs/bridge-architecture.md` |
| 84 | Multi-worker bridge extension | OUTSCOPE | Deferred to RFC 043 |

## v0.10.0 claims (cascade cancel, RFC 039)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 88 | `cancelTree root` sets every non-terminal spawned task in the subtree to `.cancelled` | PROVEN | `cancelTree_cancels_task`, `cancelTree_cancels_root` |
| 89 | `cancelTree root` leaves every task outside the subtree with unchanged `taskState` | PROVEN | `cancelTree_preserves_task_state` |
| 90 | After `cancelTree`, cancelled tasks are absent from `readyQ`, `timers`, and all `mailboxWaiters` | PROVEN | `cancelTree_removes_from_readyQ`, `cancelTree_removes_from_timers`, `cancelTree_removes_from_waiters` |
| 91 | `cancelTree` always succeeds (returns `.ok`) regardless of `root` spawn status | PROVEN | `cancelTree_step_eq` (step returns `.ok`) |
| 92 | All 21 `WellFormed` fields hold after `cancelTree` (preservation) | PROVEN | `preserves_wf_cancelTree` (in `Supervision.lean`) |
| 93 | `descendantsOf s root` is duplicate-free (nodup) and bounded by `nextId` | PROVEN | `descendantsOf_nodup`, `descendantsOf_bound` |
| 94 | `BridgeState` is preserved by `cancelTree`; `toQOps` emits `Filter 0 t` for each descendant | PROVEN | `bridge_cancelTree`, `bridge_step_single_worker` now covers 13 ops |
| 95 | `isInSubtreeOf` is well-founded (terminates by `<` on `TaskId`; conservative `false` for non-decreasing chains) | PROVEN | Lean's well-founded recursion checker via `termination_by t` |

## v0.11.0 claims (receive-timeout multi-wait, RFC 040)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 96 | `WellFormed` has 28 fields as of v0.11.0; all hold for every reachable state | PROVEN | `reachable_wf`, `wf_init` |
| 97 | `receiveUntil t deadline` with available message: dequeues head envelope, returns `.received env`; WellFormed preserved | PROVEN | `preserves_wf_receiveUntil` (dequeue sub-case) |
| 98 | `receiveUntil t deadline` with empty mailbox and past deadline: no-op, returns `.timedOut`; WellFormed preserved | PROVEN | `preserves_wf_receiveUntil` (past-deadline sub-case) |
| 99 | `receiveUntil t deadline` with empty mailbox and future deadline: parks `t` to `.waitingTimed`, registers timer and deadline, appends to `timedMailboxWaiters a`; WellFormed preserved | PROVEN | `preserves_wf_receiveUntil` (park sub-case) |
| 100 | Every `.waitingTimed` task has a `waitDeadline` entry and a timer entry | PROVEN | `WellFormed.timed_has_deadline`, `WellFormed.timed_has_timer` |
| 101 | Every `.waitingTimed` task appears in exactly one `timedMailboxWaiters` list (exclusivity) | PROVEN | `WellFormed.timed_is_waiter`, `WellFormed.timed_waiters_exclusive` |
| 102 | `tick t` wakes both `.sleeping` and `.waitingTimed` expired timers; both classes appended to `readyQ` | PROVEN | `preserves_wf_tick`, `bridge_tick` (updated for RFC 040) |
| 103 | `send`/`inject` fall through to timed waiters when `mailboxWaiters` is empty | PROVEN | `preserves_wf_send`, `preserves_wf_inject` (timed-waiter branches) |
| 104 | `BridgeState` preserved by `receiveUntil` (emits `[]`; no readyQ effect) | PROVEN | `bridge_step_single_worker` (receiveUntil case) |
| 105 | `bridge_step_single_worker` now covers all 14 RuntimeOps including `receiveUntil` | PROVEN | `Henret.Bridge.bridge_step_single_worker` |

## v0.11.1 claims (selective receive, RFC 041)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 106 | `receiveByOccurrence t occ` with a matching envelope: removes exactly that envelope, returns `.received env` where `env.occurrence = occ`; relative order of nonmatching envelopes preserved | PROVEN | `receiveByOccurrence_removes_matching`, `receiveByOccurrence_preserves_nonmatching_order` |
| 107 | `receiveFrom t src` with a matching envelope: removes exactly that envelope, returns `.received env` where `env.source = some src`; relative order of nonmatching envelopes preserved | PROVEN | `receiveFrom_source_matches`, `receiveFrom_preserves_nonmatching_order` |
| 108 | `receiveByOccurrence`/`receiveFrom` with no matching envelope: parks `t` in `mailboxWaiters a`, returns `.blocked` (Option A / Mesa semantics) | PROVEN | `receiveByOccurrence_parks_on_miss`, `receiveFrom_parks_on_miss` |
| 109 | All 28 `WellFormed` fields preserved by `receiveByOccurrence` and `receiveFrom` | PROVEN | `preserves_wf_receiveByOccurrence`, `preserves_wf_receiveFrom` |
| 110 | `dequeueFirst` removes exactly one envelope while preserving all others in order | PROVEN | `listDequeueFirst_sublist`, `listDequeueFirst_matches`, `listDequeueFirst_mem`, `listDequeueFirst_none` |
| 111 | Blocking is mailbox-level, not selector-level (Option A): any delivery to the actor wakes a parked selective-receive task | DOCUMENTED | Mesa semantics; `receiveByOccurrence_parks_on_miss` shows parking in `mailboxWaiters` |
| 112 | `bridge_step_single_worker` covers all 16 `RuntimeOp`s including `receiveByOccurrence` and `receiveFrom` | PROVEN | `bridge_step_single_worker` (both emit `[]`, readyQ unchanged) |

## v0.12.0 claims (multi-worker bridge, RFC 043)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 113 | `MultiBridgeState` relates henret `readyQ` to the union of worker queues by membership (soundness + completeness + global uniqueness + per-worker nodup) | PROVEN | `MultiBridgeState` (structure) |
| 114 | The single-worker `BridgeState` is a strict special case of `MultiBridgeState` (given `readyQ.Nodup`) | PROVEN | `single_bridge_implies_multi_bridge` |
| 115 | `Push w t` of a fresh task preserves the multi-worker membership relation | PROVEN | `multi_bridge_push` |
| 116 | `Filter w t` preserves the relation, mirroring `readyQ.filter (· ≠ t)` | PROVEN | `multi_bridge_filter` |
| 117 | Work stealing (`Steal src dst`, src ≠ dst) preserves membership: the stolen task moves between workers without leaving the ready set | PROVEN | `multi_bridge_steal` |
| 118 | Every reachable state has a worker-queue witness satisfying `MultiBridgeState` | PROVEN | `reachable_multi_bridge` |
| 119 | Multi-worker bridge preserves membership, not order (work stealing does not preserve a global ready order) | DOCUMENTED | `docs/bridge-architecture.md`; relation is set-based by construction |
| 120 | No worker-placement field added to `RuntimeState`; worker assignment is bridge-level only | PROVEN | `RuntimeState` unchanged; `MultiBridgeState` over `WorkerQueues` |

## v0.13.0 claims (execution trace ledger, RFC 045)

| # | Claim | Class | Evidence |
|---:|---|---|---|
| 121 | `stepTrace` agrees with `step` on resulting state and result (by construction) | PROVEN | `stepTrace_state_eq_step`, `stepTrace_result_eq_step` |
| 122 | `runTraceLedger` agrees with `run` on final state | PROVEN | `runTraceLedger_state_eq_run` |
| 123 | `runTraceLedger` agrees with `runTrace` on the per-op result list | PROVEN | `runTraceLedger_results_eq_runTrace` |
| 124 | A `received` event certifies the dequeue actually occurred with the stated occurrence | PROVEN | `event_received_sound` |
| 125 | A `parked` event certifies the receiver is now `.waiting` and queued in the actor's waiter list | PROVEN | `event_parked_sound` |
| 126 | A `directWoke` event certifies the task was `.sleeping` | PROVEN | `event_directWoke_sound` |
| 127 | A `timerWoke now t` event certifies `now` is not in the past and `t`'s timer expired by `now` | PROVEN | `event_timerWoke_sound` |
| 128 | A `spawnChild` event certifies the parent was running and the child is the fresh `nextId` | PROVEN | `event_spawnChild_sound` |
| 129 | A `scheduled t` event certifies nothing was running and `t` was the runnable `readyQ` head | PROVEN | `event_scheduled_sound` |
| 130 | A `waiterWoke` event from `send` certifies the woken task is the head of the actor's waiter list | PROVEN | `event_waiterWoke_send_sound` |
| 131 | Trace events are a model-level observation layer; not yet frozen as public API | DOCUMENTED | `docs/trace-ledger.md` (deferred to RFC 052) |
