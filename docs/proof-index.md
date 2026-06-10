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

### RFC 032 / RFC 038 — Actor-scoped spawn / supervision groundwork / owner-parent exactness

| Theorem | File | Notes |
|---|---|---|
| `spawnChild_sets_parent` | `Henret/Proofs/Parenthood.lean` | Child's `taskParent` = calling task; `parentOwner`/`childActor` now distinct (RFC 038) |
| `spawnChild_sets_owner` | `Henret/Proofs/Parenthood.lean` | Child's `taskOwner` = `childActor` (generalized in RFC 038; parent actor need not equal child actor) |
| `spawnChild_queues_child` | `Henret/Proofs/Parenthood.lean` | Child appended to `readyQ`; generalized (RFC 038) |
| `spawnChild_child_spawned` | `Henret/Proofs/Parenthood.lean` | Child's `taskState` = `some .new` after creation (RFC 038) |
| `spawnChild_not_running_invalid` | `Henret/Proofs/Parenthood.lean` | Guard: must be running |
| `spawnChild_unowned_invalid` | `Henret/Proofs/Parenthood.lean` | Guard: must have owner |
| `step_preserves_parent` | `Henret/Proofs/Parenthood.lean` | `taskParent` immutable post-creation |
| `reachable_parent_lt` | `Henret/Proofs/Parenthood.lean` | Every parent has smaller id |
| `parent_chain_terminates` | `Henret/Proofs/Parenthood.lean` | Chains terminate (acyclicity) |
| `reachable_owner_spawned` | `Henret/Proofs/Parenthood.lean` | Every owned task has a `taskState` (RFC 038, from `WellFormed.owner_spawned`) |
| `reachable_parent_child_spawned` | `Henret/Proofs/Parenthood.lean` | Every task with a parent has a `taskState` (RFC 038, from `WellFormed.parent_child_spawned`) |
| `preserves_wf_spawnChild` | `Henret/Proofs/Preservation/Lifecycle.lean` | 21-field WF preservation |

`WellFormed` extended to **twenty-one fields** in RFC 038 (+2 over RFC 033's nineteen):
- `owner_spawned` (field 20) — every task with a `taskOwner` has a `taskState`.
- `parent_child_spawned` (field 21) — every task with a `taskParent` has a `taskState`.

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
  `bridge_tick`, `bridge_complete`, `bridge_cancelTree` (RFC 039).
- **`bridge_step_single_worker`** — unified single-step bridge: for any `RuntimeOp`, if
  `BridgeState s wqs` holds, then `BridgeState (step s op).1 (applyQOps wqs (toQOps s op))`.
- **`bridge_run_general`** — trace bridge from any starting state.
- **`bridge_run_tracks_single_worker`** — headline trace theorem: `BridgeState (run init ops) (applyQOps WorkerQueues.init (toQOpsTrace init ops))`.
- `reachable_bridge` — backward-compatible existential form (proved via `bridge_run_tracks_single_worker`).

**Bridge scope note**: this is a queue projection bridge. It relates `readyQ` to worker 0's
queue. It does not claim fairness, native execution, or actor semantics. Multi-worker
extension is deferred to RFC 043. See `docs/bridge-architecture.md`.

---

### RFC 039 — Supervision Semantics: Cascade Cancel

| Theorem | File | Notes |
|---|---|---|
| `cancelTree_step_eq` | `Henret/Proofs/Supervision.lean` | `(step s (.cancelTree r)).1 = applyCancelTree s (descendantsOf s r)` — `rfl` |
| `cancelTree_cancels_task` | `Henret/Proofs/Supervision.lean` | Non-terminal tasks in `descendantsOf s root` are `.cancelled` after step |
| `cancelTree_preserves_task_state` | `Henret/Proofs/Supervision.lean` | Tasks not in `descendantsOf s root` retain their state |
| `cancelTree_cancels_root` | `Henret/Proofs/Supervision.lean` | The root itself is `.cancelled` (if spawned and non-terminal) |
| `cancelTree_removes_from_readyQ` | `Henret/Proofs/Supervision.lean` | Cancelled tasks are not in `readyQ` after step |
| `cancelTree_removes_from_timers` | `Henret/Proofs/Supervision.lean` | Cancelled timer entries are removed |
| `cancelTree_removes_from_waiters` | `Henret/Proofs/Supervision.lean` | Cancelled tasks are removed from all `mailboxWaiters` lists |
| `preserves_wf_cancelTree` | `Henret/Proofs/Supervision.lean` | All 21 `WellFormed` fields preserved by `cancelTree` |
| `bridge_cancelTree` | `Henret/Bridge/Preservation.lean` | `BridgeState` preserved by `cancelTree`; `toQOps` emits `Filter 0 t` per descendant |
| `descendantsOf_includes_root` | `Henret/Proofs/Supervision.lean` | Root is in `descendantsOf s root` when spawned |
| `descendantsOf_nodup` | `Henret/Proofs/Supervision.lean` | No duplicates in the cancellation set |

**New infrastructure:**
- `isInSubtreeOf s root t : Bool` — computable parent-chain check (well-founded by `<` on `TaskId`)
- `descendantsOf s root : List TaskId` — computable cancellation set (all spawned subtree tasks)
- `applyCancelTree s tc : RuntimeState` — direct conditional state transformer (not foldl)

`RuntimeOp` extended to **13 constructors** (`cancelTree (root : TaskId)` added in RFC 039).

---

### RFC 040 — Receive Timeout / Multi-Wait Semantics

`WellFormed` extended to **28 fields** (+7 over RFC 039's 21). `RuntimeOp` extended to **14 constructors** (`receiveUntil (t : TaskId) (deadline : Nat)` added).

**New `TaskState`**: `TaskState.waitingTimed` — task parked in `timedMailboxWaiters`, holding a timer-backed deadline.

**New `WellFormed` fields** (22–28, `Henret/Proofs/Invariants.lean`):

| Field | Invariant |
|---|---|
| `timed_has_deadline` | Every `.waitingTimed` task has a `waitDeadline` entry |
| `deadline_is_timed` | Every task with a `waitDeadline` is in `.waitingTimed` state |
| `timed_has_timer` | Every `.waitingTimed` task has a corresponding timer entry |
| `timed_is_waiter` | Every `.waitingTimed` task is in some `timedMailboxWaiters` list |
| `timed_waiters_valid` | Every task in a `timedMailboxWaiters` list is `.waitingTimed` |
| `timed_waiters_nodup` | Each `timedMailboxWaiters` list is duplicate-free |
| `timed_waiters_exclusive` | A task appears in at most one `timedMailboxWaiters` list |

**New operation semantics** (`Henret/Scheduler/Model.lean`):
- `receiveUntil t deadline` — three-branch: (1) message available → immediate dequeue, (2) past-deadline → no-op `timedOut`, (3) park with deadline → sets `.waitingTimed`, registers timer + deadline, appends to `timedMailboxWaiters`.
- `tick t` updated — now wakes both `.sleeping` and `.waitingTimed` expired timers (appends both to `readyQ`, removes from `timedMailboxWaiters`).
- `send`/`inject` updated — when `mailboxWaiters b = []`, fall through to wake the head of `timedMailboxWaiters b` if non-empty.

**Preservation theorems** (`Henret/Proofs/Preservation/Messaging.lean`):
- `preserves_wf_receiveUntil` — all 28 `WellFormed` fields preserved across all three `receiveUntil` sub-cases.
- All 28 fields updated in `preserves_wf_send`, `preserves_wf_receive`, `preserves_wf_inject`.

**Bridge updates** (`Henret/Bridge/Grammar.lean`, `Henret/Bridge/Preservation.lean`):
- `toQOps` for `send`/`inject` extended: emits `Push 0 w` for timed-waiter fallback.
- `toQOps_send_valid_timed_waiter`, `toQOps_inject_valid_timed_waiter` — new lemmas.
- `toQOps_tick_valid` updated: woken list is `sleeping_filter ++ waitingTimed_filter`.
- `bridge_step_single_worker` covers `receiveUntil` (no readyQ effect, emits `[]`).
- `bridge_send`, `bridge_inject`, `bridge_tick` updated for new waiter/tick semantics.

| Theorem | File | Notes |
|---|---|---|
| `preserves_wf_receiveUntil` | `Henret/Proofs/Preservation/Messaging.lean` | All 28 WellFormed fields |
| `WellFormed.timed_has_deadline` | `Henret/Proofs/Invariants.lean` | Field 22 |
| `WellFormed.deadline_is_timed` | `Henret/Proofs/Invariants.lean` | Field 23 |
| `WellFormed.timed_has_timer` | `Henret/Proofs/Invariants.lean` | Field 24 |
| `WellFormed.timed_is_waiter` | `Henret/Proofs/Invariants.lean` | Field 25 |
| `WellFormed.timed_waiters_valid` | `Henret/Proofs/Invariants.lean` | Field 26 |
| `WellFormed.timed_waiters_nodup` | `Henret/Proofs/Invariants.lean` | Field 27 |
| `WellFormed.timed_waiters_exclusive` | `Henret/Proofs/Invariants.lean` | Field 28 — cross-actor uniqueness |

---

### RFC 041 — Selective Receive

`RuntimeOp` extended to **16 constructors** — `receiveByOccurrence (t : TaskId) (occ : MessageId)` and `receiveFrom (t : TaskId) (src : ActorId)` added.

**Design: Option A (Mesa-style blocking)**. When no matching envelope is present, the task parks in the ordinary `mailboxWaiters` list. This is mailbox-level (not selector-level) blocking: any future delivery wakes the task, which then re-runs the selective receive. Spurious wakeups are possible and explicitly documented.

**Foundation: `listDequeueFirst`** (`Henret/Actor/Mailbox.lean`) — structural-recursion function that removes the first list element satisfying a decidable predicate, preserving relative order. Avoids index-bounds reasoning; all properties are proved by structural induction.

**Properties of `listDequeueFirst` / `dequeueFirst`:**

| Lemma | Statement |
|---|---|
| `listDequeueFirst_matches` | Result satisfies the predicate |
| `listDequeueFirst_mem` | Result is a member of the original list |
| `listDequeueFirst_sublist` | Remainder is a `Sublist` of the original — order preserved |
| `listDequeueFirst_none` | On failure, no element satisfies the predicate |
| `dequeueFirst_matches` | Top-level: result matches |
| `dequeueFirst_sublist` | Top-level: remainder sublist |
| `dequeueFirst_none` | Top-level: no match |

**Preservation**: `preserves_wf_receiveByOccurrence`, `preserves_wf_receiveFrom` — both use the `dequeueFirst_sublist`-based sublist membership proof instead of `dequeue_spec`'s head-removal. All 28 `WellFormed` fields preserved.

**Behavioral theorems** (`Henret/Proofs/Messaging.lean`, section `SelectiveReceive`):

| Theorem | Statement |
|---|---|
| `receiveByOccurrence_removes_matching` | Returned envelope has `occurrence = occ` |
| `receiveFrom_source_matches` | Returned envelope has `source = some src` |
| `receiveByOccurrence_parks_on_miss` | No match → parks `t` in `mailboxWaiters a`, result `.blocked` |
| `receiveFrom_parks_on_miss` | No match → parks `t` in `mailboxWaiters a`, result `.blocked` |
| `receiveByOccurrence_preserves_nonmatching_order` | `rest.messages.Sublist mb.messages` — order preserved |
| `receiveFrom_preserves_nonmatching_order` | `rest.messages.Sublist mb.messages` — order preserved |

---

### RFC 043 — Multi-Worker Bridge Model Extension

Generalises the single-worker `BridgeState` (list-equality on worker 0) to a **membership-based** multi-worker relation suitable for comparison with work-stealing scheduler semantics. No worker-placement field is added to `RuntimeState` — worker assignment stays a bridge/refinement concern (`Henret/Bridge/MultiState.lean`).

**`MultiBridgeState` (Option B — membership, not order):**

| Field | Statement |
|---|---|
| `sound` | Every queued task is ready in henret (`t ∈ wqs w → t ∈ s.readyQ`) |
| `complete` | Every ready task is queued somewhere (`t ∈ s.readyQ → ∃ w, t ∈ wqs w`) |
| `worker_nodup` | Each worker queue is duplicate-free |
| `global_unique` | A task sits in at most one worker queue |

**Multi-worker queue application** (`applyMQOp`): unlike the single-worker `applyQOp`, `Steal src dst` has real semantics — it moves the head of `src`'s queue to `dst`'s tail (the model-level analogue of stealing from the top end). `Wake`/`Inject` target worker 0 (wake-to-worker-0 policy).

**Theorems:**

| Theorem | Statement |
|---|---|
| `single_bridge_implies_multi_bridge` | `BridgeState s wqs → s.readyQ.Nodup → MultiBridgeState s wqs` — single-worker bridge is a strict special case |
| `multi_bridge_push` | `Push w t` (fresh `t`) preserves the membership relation |
| `multi_bridge_filter` | `Filter w t` preserves the relation, mirroring `readyQ.filter (· ≠ t)` |
| `multi_bridge_steal` | `Steal src dst` (src ≠ dst) preserves membership — the stolen task moves between workers without leaving the ready set |
| `reachable_multi_bridge` | Every reachable state has a `WorkerQueues` witness satisfying `MultiBridgeState` (via `single_bridge_implies_multi_bridge` + `reachable_wf.readyQ_nodup`) |

**Scope note**: this is a model-level membership bridge. Order is deliberately not preserved (work stealing does not preserve a single global ready order). It does not prove C race-freedom, fairness, or liveness — those remain out of scope. See `docs/bridge-architecture.md`.

---

### RFC 045 — Execution Trace Ledger

Makes execution traces first-class. `stepTrace`/`runTraceLedger` emit a list of semantic `TraceEvent`s alongside the ordinary `(state, result)` effect. New module `Henret/Trace/` (`Event.lean`, `Run.lean`, `Theorems.lean`) + aggregator `Henret/Trace.lean`.

**Agreement by construction**: `stepTrace` reuses `step` for state/result and only adds the event computation, so:

| Theorem | Statement |
|---|---|
| `stepTrace_state_eq_step` | `(stepTrace s op).1 = (step s op).1` (`rfl`) |
| `stepTrace_result_eq_step` | `(stepTrace s op).2.1 = (step s op).2` (`rfl`) |
| `runTraceLedger_state_eq_run` | `(runTraceLedger s ops).1 = run s ops` (induction) |
| `runTraceLedger_results_eq_runTrace` | results list agrees with `runTrace` |

**Event soundness** (`Henret/Trace/Theorems.lean`):

| Theorem | Guarantee |
|---|---|
| `event_received_sound` | `received t a occ` ⇒ `t` running, owns `a`, mailbox head dequeued with that occurrence |
| `event_parked_sound` | `parked t a` ⇒ `t` now `.waiting`, in `a`'s waiter list |
| `event_directWoke_sound` | `directWoke t` ⇒ `t` was `.sleeping` |
| `event_timerWoke_sound` | `timerWoke now t` ⇒ `now` not past, `t`'s timer expired by `now` |
| `event_spawnChild_sound` | `spawnChild parent child a` ⇒ `parent` running, `child = nextId` fresh |
| `event_scheduled_sound` | `scheduled t` ⇒ nothing running, `t` was runnable `readyQ` head |
| `event_waiterWoke_send_sound` | `waiterWoke a w` from `send` ⇒ `w` head of `a`'s regular/timed waiter list |

See `docs/trace-ledger.md`.

---

### RFC 047 — Golden Trace Conformance Suite

A behavioral conformance suite built on the RFC 045 trace ledger. External runtimes compare their observed `TraceEvent` traces against Henret's canonical golden traces. New module `Henret/Conformance/` (`Scenario.lean`, `Golden.lean`, `Export.lean`) + aggregator `Henret/Conformance.lean`, and a `henret-conformance` executable.

**Scenario infrastructure** (`Scenario.lean`): `GoldenScenario` structure, `observe`/`checkScenario`/`scenarioReport`, `TraceRefines` (exact equality, v1), `firstMismatch` (reports the first differing event).

**Ten golden scenarios** (`Golden.lean`): `spawn_schedule_complete`, `yield_requeues`, `sleep_tick_wakes`, `empty_receive_parks`, `send_wakes_waiter_mesa`, `inject_wakes_waiter_mesa`, `cancel_ready_task`, `cancel_waiting_task`, `spawn_child_parent_lt`, `occurrence_unique_two_mailboxes`.

**Regression gate**:

| Theorem | Statement |
|---|---|
| `conformance_suite_passes` | `allPass = true` — every golden scenario's observed trace equals its checked-in expected trace. Kernel-checked by `decide` (no `native_decide`, no extra axioms). |

Any change to `step` or `traceEvents` that alters observable behavior breaks this proof. See `docs/conformance-suite.md` for the adapter contract.

---

### RFC 046 — Fairness and Conditional Liveness Layer

An **optional** policy layer for conditional progress reasoning. Nothing is added to `WellFormed`; the safety model and liveness layer stay separate. New module `Henret/Progress/` (`Policy.lean`, `Examples.lean`) + aggregator `Henret/Progress.lean`.

**Trace-step predicates** (`Policy.lean`): `stateAt` (state after `i` ops), `runnableAtStep` (task queued in `readyQ`), `scheduledAtStep` (op `i` schedules the task) — both decidable.

**The explicit assumption**: `BoundedReadyFair k s ops` — every task runnable at some step is scheduled within `k` further steps. A property of the op sequence, not of `WellFormed`.

| Theorem | Statement |
|---|---|
| `ready_eventually_scheduled_under_bounded_fairness` | conditional progress: under `BoundedReadyFair k`, a runnable task is scheduled within `k` steps |
| `schedule_schedules_head` | **unconditional, local**: the FIFO head of `readyQ` is the next task scheduled |
| `head_scheduled_within_one` | the head is scheduled within one step (no fairness assumption) |
| `unfairOps_not_bounded_fair_0` | a representable starvation: an op sequence that stops scheduling fails `BoundedReadyFair 0` |

**Fair/unfair witnesses** (`Examples.lean`, all `by decide`): `fair_task0_scheduled`, `fair_task1_scheduled`, `unfair_task1_runnable`, `unfair_task1_never_scheduled`.

Honesty: the model's `readyQ` is FIFO so head-progress is unconditional, but whole-program fairness depends on the scheduler issuing `schedule` ops — starvation is representable. See `docs/progress-policy.md`.
