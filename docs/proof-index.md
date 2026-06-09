# Proof Index

All theorems are kernel-checked; none uses `sorry` or `native_decide`.
Axiom audit: only `propext` and `Quot.sound` (Lean standard).

## Core primitives — `Henret/Core/Id.lean`
- `upd_self`, `upd_ne` — the single map-update primitive behaves pointwise.

## Mailbox — `Henret/Actor/Mailbox.lean`
- `Mailbox.enqueue_messages` — enqueue appends at the tail.
- `Mailbox.dequeue_spec` — dequeue is exactly head removal.

## Task states — `Henret/Actor/Task.lean`
- `TaskState.isTerminal_completed`, `TaskState.isTerminal_cancelled`.

## Timer queue — `Henret/Scheduler/Timer.lean`
- `Timer.mem_insertSorted`, `Timer.insertSorted_sorted` — sorted insertion.
- `Timer.mem_expired`, `Timer.mem_remaining` — exact split by `now`.
- `Timer.sorted_filter`, `Timer.remaining_sorted` — sortedness closure.

## Scheduler model — `Henret/Scheduler/Model.lean`
- `run_nil`, `run_cons` — program execution unfolding.

## Lifecycle — `Henret/Proofs/Lifecycle.lean`
- `wakeOne_preserves_of_ne_sleeping`, `wakeMany_preserves_of_ne_sleeping`,
  `wakeOne_other`, `wakeMany_preserves_other`, `wakeMany_wakes` — wake helper laws.
- `step_preserves_terminal` — flagship: full case analysis over the
  twelve-operation grammar.
- `step_preserves_completed`, `step_preserves_cancelled` — corollaries.
- `run_preserves_terminal`, `run_preserves_completed`, `run_preserves_cancelled`.
- `wake_exact`, `wake_sets_ready`, `wake_twice_invalid` — RFC 006 wake laws.

## Messaging — `Henret/Proofs/Messaging.lean`
- `send_appends`, `send_preserves_other` (task-scoped, RFC 024).
- `receive_consumes_one`, `receive_length`, `receive_preserves_other`,
  `receive_empty_parks`, `receive_blocked_parks`, `receive_only_own` (RFC 024/031).

## Timers — `Henret/Proofs/Timers.lean`
- `tick_keeps_future`, `tick_no_early_wake`, `tick_wakes_expired`,
  `tick_enqueues_woken`, `step_preserves_sorted`, `run_preserves_sorted`.

## Drivers — `Henret/Scheduler/Driver.lean`
- `drain_empties`, `completeOne_completed`, `completeAll_preserves_completed`,
  `completeOne_drainable`, `completeAll_completes`, `drain_completes`.

## Refinement — `Henret/Refinement/*.lean`
- `MailboxBackend.dequeue_length` — derived from the contract laws.
- `listBackend`, `mailboxBackend` — reference backends; the contract laws
  (`MailboxBackend.toList_empty`, `MailboxBackend.toList_enqueue`,
  `MailboxBackend.toList_dequeue`) are proof fields.

## Native layer — `Henret/Native/DequeModel.lean`

All kernel-checked; no custom axioms.  `#print axioms` → only `propext`/`Quot.sound`.

- `stealHead`, `popLast` — FIFO and LIFO list dequeue helpers.
- `DequeModel` — abstract 6-law contract.
- `listDeque` — reference implementation; laws by `rfl`.
- `qStep_tracks` — one-step tracking lemma.
- `qRun_tracks` — whole-program refinement (PROVEN, `propext` only).
- `totalFuel_nil`, `totalFuel_cons`, `totalFuel_append_single` — fuel arithmetic.
- `driveStackB_complete` — owner-end stack driver liveness (PROVEN, `propext`, `Quot.sound`).

## Native assumptions — `Henret/Native/Assumptions.lean`

Six typed axioms (ASSUMED) + derived PROVEN results:
- `NativeDeque.toList_empty/push/steal_val/steal_rest/pop_val/pop_rest`
- `nativeDequeModel : DequeModel` — definitional, no proof burden beyond axioms.
- `nativeDequeModel_qRun_tracks` — PROVEN; depends on exactly the 6 axioms.
- `nativeDequeModel_driveComplete` — PROVEN; no native axioms.

## v0.2.0 — `Henret/Proofs/Ownership.lean`

- `wakeOne_isSome`, `wakeMany_isSome` — waking never un-spawns.
- `step_preserves_spawned` — `some` states never return to `none`.
- `WellFormed.spawned_has_owner` (field), `reachable_spawned_has_owner` —
  ownership set at spawn, immutable forever.

## v0.2.0 — `Henret/Proofs/Invariants.lean`

- `nodup_of_sublist`, `nodup_append_singleton`, `nodup_append`,
  `nodup_task_inj`, `mem_map_insertSorted`, `insertSorted_task_nodup` —
  core-only list/timer helpers.
- `WellFormed` — the reachability invariant (nineteen fields as of RFC 033):
  ready-queue soundness *and* completeness, running-slot consistency,
  timer discipline (uniqueness, sleep-coherence, sortedness), fresh-id
  discipline, ownership existence, owner-mailbox existence; wait-queue
  integrity (waiters are `.waiting`, owned, queued, and nodup); location
  disjointness derived as corollaries.
- `wf_init`; corollaries `WellFormed.ready_not_running`,
  `WellFormed.ready_no_timer`, `WellFormed.running_no_timer`
  (location disjointness derived from state uniqueness).

## v0.2.0 — `Henret/Proofs/InvariantsPreservation.lean`

- `step_preserves_wf` — all twelve operations preserve `WellFormed`.
- `run_preserves_wf`, `reachable_wf` — every reachable state is well-formed.

## v0.2.0 — additions to existing files

- `Henret/Proofs/Lifecycle.lean`: `step_invalid_unchanged`.
- `Henret/Proofs/Timers.lean`: `tick_advances_clock`,
  `tick_backwards_invalid`, `step_clock_monotone`; tick theorems
  re-proved under the monotonicity guard.

## v0.2.1 — RFC 019 additions

- `WellFormed` gains `timers_sorted`, `spawned_has_owner`,
  `owned_has_mailbox` (nine fields total).
- `reachable_spawned_has_owner`, `reachable_owner_has_mailbox`,
  `reachable_timers_sorted` — reachability headlines.
- `wakeOne_none`, `wakeMany_none` (`Ownership.lean`) — waking never spawns.
- `drivePopB` → `driveStackB` (RFC 023 rename; orientation documented).

## v0.3.0 — RFC 024 additions

- `Henret/Proofs/StepProjections.lean` — 21 `@[simp]` projection lemmas:
  `send`/`receive`/`inject` leave every field but `mailboxes` untouched.
- `Henret/Proofs/Messaging.lean` (rewritten) — scoped `send_appends`,
  `receive_consumes_one`, `receive_length`, `*_preserves_other`,
  `receive_empty_parks`, `receive_blocked_parks`; guard theorems `send_not_running_invalid`,
  `send_unowned_invalid`, `receive_unowned_invalid`; environment
  `inject_appends`/`inject_preserves_other`; mailbox monotonicity
  `send/receive/inject_mailbox_isSome`; headline `receive_only_own`.

## v0.4.0 — RFC 028/029 additions

- `WellFormed.runnable_queued` (tenth field) — schedulable completeness.
- `reachable_runnable_is_queued`, `reachable_queue_exact` — the runtime
  never loses a runnable task; queue membership ⟺ runnable.
- `StepResult.blocked` — blocked is a legal result distinct from invalid.
  Note: the v0.4.0 theorems receive_empty_blocked and step_blocked_unchanged
  were superseded in v0.5.1 — blocked receive now parks the task; those names
  no longer exist. Use `receive_empty_parks` / `receive_blocked_parks` instead.

## v0.5.0 — RFC 031: blocked waiting state + mailbox wait queue

**`Henret/Proofs/Preservation/Messaging.lean`** (extended):
- `preserves_wf_send` (wake-one branch): proves all 14 WF fields including
  the four new waiter fields; mail dequeue from `mailboxWaiters` head.
- `preserves_wf_receive` (parking branch): parks running task into
  `TaskState.waiting`, appends to `mailboxWaiters a`; proves waiter
  invariants.
- `preserves_wf_inject` added (was inadvertently absent after v0.5.0 split).

**`Henret/Proofs/Preservation/Lifecycle.lean`** (extended):
- `preserves_wf_cancel`: four new waiter sub-proofs with taskOwner
  case-split to handle the filtered `mailboxWaiters` update.
- All five lifecycle operations updated to prove all 14 WF fields.

**`Henret/Proofs/Preservation/Time.lean`** (extended):
- `preserves_wf_sleep`, `preserves_wf_tick`, `preserves_wf_wake`: four new
  waiter fields each, all proved by pass-through (time ops do not touch
  `mailboxWaiters`).

**New `WellFormed` fields** (11–14):
- `WellFormed.waiters_waiting` — every task in any `mailboxWaiters` list has
  `taskState = some .waiting`.
- `WellFormed.waiters_owned` — every task in `mailboxWaiters a` has
  `taskOwner = some a`.
- `WellFormed.waiting_queued` — every `.waiting` task appears in its owner's
  `mailboxWaiters`.
- `WellFormed.waiters_nodup` — each `mailboxWaiters` list is duplicate-free.

### RFC 032 — Actor-scoped spawn / supervision groundwork

| Theorem | File | Notes |
|---|---|---|
| `spawnChild_sets_parent` | `Henret/Proofs/Parenthood.lean` | Child's `taskParent` = calling task |
| `spawnChild_sets_owner` | `Henret/Proofs/Parenthood.lean` | Child's `taskOwner` = calling actor |
| `spawnChild_queues_child` | `Henret/Proofs/Parenthood.lean` | Child appended to `readyQ` |
| `spawnChild_not_running_invalid` | `Henret/Proofs/Parenthood.lean` | Guard: must be running |
| `spawnChild_unowned_invalid` | `Henret/Proofs/Parenthood.lean` | Guard: must have owner |
| `step_preserves_parent` | `Henret/Proofs/Parenthood.lean` | `taskParent` immutable post-creation |
| `reachable_parent_lt` | `Henret/Proofs/Parenthood.lean` | Every parent has smaller id |
| `parent_chain_terminates` | `Henret/Proofs/Parenthood.lean` | Chains terminate (acyclicity) |
| `preserves_wf_spawnChild` | `Henret/Proofs/Preservation/Lifecycle.lean` | 16-field WF preservation |

### RFC 033 — Message envelope and occurrence identity

`WellFormed` extended to **nineteen fields** (+3 over RFC 032's sixteen):
`occ_fresh`, `occ_nodup`, `occ_disjoint`.

**`Henret/Actor/Mailbox.lean`** — model changes:
- `MessageId := Nat` — occurrence id type alias.
- `Envelope` — new structure: `occurrence : MessageId`, `source : Option ActorId`, `body : Message`.
- `Mailbox.messages : List Envelope` (was `List Message`).
- `Mailbox.enqueue : Mailbox → Envelope → Mailbox` (was `→ Message →`).
- `Mailbox.dequeue : Mailbox → Option (Envelope × Mailbox)` (was `Message ×`).

**`Henret/Scheduler/Model.lean`** — model changes:
- `RuntimeState.nextMsgId : MessageId` (new field, init = 0).
- `send t b m` stamps `env := ⟨s.nextMsgId, s.taskOwner t, m⟩`, bumps `nextMsgId`.
- `inject a m` stamps `env := ⟨s.nextMsgId, none, m⟩`, bumps `nextMsgId`.
- `receive t` dequeues `Envelope`; `StepResult.received` carries `Envelope`.

**`Henret/Proofs/Invariants.lean`** — three new `WellFormed` fields (17–19):
- `occ_fresh` — every envelope's `occurrence < nextMsgId`.
- `occ_nodup` — within each mailbox, all occurrence ids are distinct.
- `occ_disjoint` — across different mailboxes, all occurrence ids are distinct.

**`Henret/Proofs/Occurrence.lean`** — headline theorems:

| Theorem | Notes |
|---|---|
| `reachable_occurrence_unique` | **Global uniqueness**: equal occurrence ids in any reachable mailboxes imply same envelope in same mailbox |
| `send_stamps_source` | Envelope appended by `send t b m` has `source = s.taskOwner t` |
| `inject_stamps_none` | Envelope appended by `inject a m` has `source = none` |

**Updated preservation proofs** — all three preservation files extended to 19 fields:
- `Henret/Proofs/Preservation/Lifecycle.lean` — 7 refine blocks × 3 occ bullets.
- `Henret/Proofs/Preservation/Time.lean` — 3 refine blocks × 3 occ bullets.
- `Henret/Proofs/Preservation/Messaging.lean` — 6 refine blocks × 3 occ bullets.

**`Henret/Refinement/Contract.lean`** and **`ReferenceBackend.lean`** — updated to `Envelope` (was `Message`).

### RFC 035 / RFC 036 — Lean-Runtime Bridge (complete single-worker projection)

**`Henret/Bridge/Grammar.lean`** — QOp grammar and translation (RFC 036):
- `QOp` — bridge queue-operation grammar: Push, Pop, Filter (new in RFC 036),
  Steal, Wake, Inject (mirrored from lean-runtime; not emitted by single-worker `toQOps`).
- `toQOps : RuntimeState → RuntimeOp → List QOp` — guard-compatible translation;
  `toQOps s op = []` whenever `step s op` would return `.invalid`.
  Emits only `Push`, `Pop`, and `Filter` in the single-worker bridge.
- Direct-effect lemmas: `toQOps_spawn_valid`, `toQOps_spawn_invalid`,
  `toQOps_spawnChild_valid`, `toQOps_schedule_nonempty`, `toQOps_schedule_empty`,
  `toQOps_yield_valid`, `toQOps_yield_invalid`,
  `toQOps_wake_valid`, `toQOps_wake_invalid`,
  `toQOps_cancel_valid`, `toQOps_cancel_invalid_terminal`, `toQOps_cancel_invalid_unspawned`,
  `toQOps_send_valid_waiter`, `toQOps_send_valid_no_waiter`,
  `toQOps_inject_valid_waiter`, `toQOps_inject_valid_no_waiter`, `toQOps_inject_invalid`,
  `toQOps_tick_valid`, `toQOps_tick_invalid`,
  `toQOps_complete_nil`, `toQOps_receive_nil`, `toQOps_sleep_nil`.

**`Henret/Bridge/State.lean`** — BridgeState relation and queue model:
- `WorkerQueues := WorkerIdx → List TaskId` — per-worker task queues.
- `WorkerQueues.init` — empty initial worker-queue map.
- `BridgeState : RuntimeState → WorkerQueues → Prop` — queue projection bridge:
  `queue_eq` (worker 0 = henret readyQ) + `other_empty` (single-worker model).
- `bridgeState_init`, `bridgeState_push0`, `bridgeState_pop0`, `bridgeState_filter0` (RFC 036),
  `bridgeState_readyQ_unchanged` — structural constructors.
- `applyQOp`, `applyQOps` — queue-model QOp application (Filter case added in RFC 036).
- `toQOpsTrace` — state-threading trace translation.

**`Henret/Bridge/Preservation.lean`** — complete bridge preservation (RFC 036):
- `bridge_stable` — BridgeState is preserved by readyQ-stable steps.
- `applyQOps_append` — `applyQOps wqs (as ++ bs) = applyQOps (applyQOps wqs as) bs`.
- Per-op bridge theorems (all 12 RuntimeOps covered):
  `bridge_spawn`, `bridge_spawnChild`, `bridge_schedule`, `bridge_yield`, `bridge_wake`,
  `bridge_cancel`, `bridge_send`, `bridge_inject`, `bridge_receive`, `bridge_sleep`,
  `bridge_tick`, `bridge_complete`.
- **`bridge_step_single_worker`** — unified single-step bridge: for any `RuntimeOp`, if
  `BridgeState s wqs` holds, then `BridgeState (step s op).1 (applyQOps wqs (toQOps s op))`.
- **`bridge_run_general`** — trace bridge from any starting state.
- **`bridge_run_tracks_single_worker`** — headline trace theorem: `BridgeState (run init ops) (applyQOps WorkerQueues.init (toQOpsTrace init ops))`.
- `reachable_bridge` — backward-compatible existential form (proved via `bridge_run_tracks_single_worker`).

**Bridge scope note**: this is a queue projection bridge. It relates `readyQ` to worker 0's
queue. It does not claim fairness, native execution, or actor semantics. Multi-worker
extension is deferred to RFC 043. See `docs/bridge-architecture.md`.
