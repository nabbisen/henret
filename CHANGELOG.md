# Changelog

## v0.13.1 — Golden Trace Conformance Suite (RFC 047)

A behavioral conformance suite built on the RFC 045 trace ledger.
External runtimes compare their observed `TraceEvent` traces against
Henret's canonical golden traces to certify conformance. New module
`Henret/Conformance/` (`Scenario`, `Golden`, `Export`) with aggregator
`Henret/Conformance.lean` and a `henret-conformance` executable.

### Scenario infrastructure

`GoldenScenario` pairs a named operation sequence with the canonical
`TraceEvent` trace Henret produces. `observe`/`checkScenario` run and
check; `firstMismatch` reports the first differing event; `TraceRefines`
is the refinement relation (exact equality in v1, per the RFC).

### Ten golden scenarios

`spawn_schedule_complete`, `yield_requeues`, `sleep_tick_wakes`,
`empty_receive_parks`, `send_wakes_waiter_mesa`,
`inject_wakes_waiter_mesa`, `cancel_ready_task`, `cancel_waiting_task`,
`spawn_child_parent_lt`, `occurrence_unique_two_mailboxes`.

### Kernel-checked regression gate

```lean
theorem conformance_suite_passes : allPass = true := by decide
```

Verified by `decide` (not `native_decide`, so no extra axioms). Any
change to `step` or `traceEvents` that alters observable behavior breaks
this proof — golden traces cannot silently drift from the semantics.

### Executable

`lake exe henret-conformance` prints a per-scenario PASS/FAIL report and
exits non-zero on any failure.

### Docs

`docs/conformance-suite.md` documents the suite, the refinement relation,
and the adapter contract for external runtimes (which need only expose
the observable event stream, not internal queues).

### Axiom budget: unchanged

`conformance_suite_passes` depends only on `propext` and `Quot.sound`.
No project axioms.

---

## v0.13.0 — Execution Trace Ledger (RFC 045)

Makes execution traces first-class. Each operation now emits, alongside
its ordinary `(state, result)` effect, a list of semantic `TraceEvent`s
— which task was scheduled, which envelope delivered, which task parked,
which timer fired. New module `Henret/Trace/` (`Event`, `Run`,
`Theorems`) with aggregator `Henret/Trace.lean`, wired into the top-level
`Henret` import.

### Event vocabulary

`TraceEvent` has one constructor per meaningful runtime observation:
`spawned`, `spawnChild`, `scheduled`, `yielded`, `completed`,
`cancelled`, `slept`, `timerWoke`, `directWoke`, `sent`, `injected`,
`received`, `parked`, `waiterWoke`, `invalid`, `noEffect`.

### Agreement by construction

`stepTrace` reuses `step` for its state and result and only *adds* a
separate `traceEvents` computation, so the agreement theorems are
definitional:

- `stepTrace_state_eq_step` — `(stepTrace s op).1 = (step s op).1` (`rfl`);
- `stepTrace_result_eq_step` — result agrees (`rfl`);
- `runTraceLedger_state_eq_run` — final state agrees with `run` (induction);
- `runTraceLedger_results_eq_runTrace` — result list agrees with `runTrace`.

There is no risk of the ledger drifting from the semantics, because it
never recomputes the state.

### Event soundness

Seven soundness theorems certify that an emitted event reflects a real
semantic fact: `event_received_sound`, `event_parked_sound`,
`event_directWoke_sound`, `event_timerWoke_sound`,
`event_spawnChild_sound`, `event_scheduled_sound`, and
`event_waiterWoke_send_sound`. Each is a guard-case analysis, since
`traceEvents` mirrors `step`'s guards exactly.

### Example and docs

`examples/11_trace_ledger.lean` prints a readable trace and discharges
the agreement and soundness theorems. `docs/trace-ledger.md` documents
the design.

### Axiom budget: unchanged

All trace theorems depend only on `propext` and `Quot.sound`. No project
axioms. Verified by `scripts/axiom_audit.py`.

---

## v0.12.1 — Runtime Integration Contract (RFC 044)

Documentation and ecosystem-maturity release. No model or proof changes;
the public surface is unchanged. Adds a stable boundary contract for
downstream consumers.

### New: `docs/integration-contract.md`

The boundary contract for projects using Henret as a semantic reference
model. Ten sections:

1. **Project role** — Henret is a reference model, not a runtime library.
2. **Stable imports** — stability levels per import (`Henret.Model` and
   `Henret.Proofs` are fully stable; `Henret.Native.*` is trusted;
   examples are unstable).
3. **Operation mapping** — external runtime events → all 16 `RuntimeOp`s.
4. **Mesa semantics contract** — wake-one, no atomic handoff, re-run
   receive; selective receive parks at mailbox level.
5. **Occurrence identity contract** — fresh ids, global uniqueness,
   `send`/`inject` source stamping.
6. **Supervision contract** — acyclic parenthood, cascade cancel
   (`cancelTree`) stable since v0.10.0; restart policies not yet modeled.
7. **Bridge contract** — single-worker (exact) and multi-worker
   (membership) levels; headline theorems; no native-concurrency claim.
8. **Theorem contract** — the public theorem table; warning not to depend
   on internal `preserves_wf_*` / `step_*` / `toQOps_*` helpers.
9. **Trust boundary** — kernel-proven / trusted / tested / out-of-scope.
10. **Versioning policy** — what counts as breaking vs non-breaking.

### New: `examples/10_integration_contract.lean`

A worked consumer trace: maps a small actor scenario to Henret ops, runs
it, and discharges `reachable_wf` and `reachable_occurrence_unique` on
the result — using only the public theorem surface.

### README

Adds a "Using Henret in your own project?" pointer to the integration
contract in the learning path.

---

## v0.12.0 — Multi-Worker Bridge Model Extension (RFC 043)

Generalises the bridge from a single-worker queue projection to a
**membership-based** multi-worker projection suitable for comparison with
`lean-runtime`'s work-stealing scheduler. New file
`Henret/Bridge/MultiState.lean`.

### `MultiBridgeState` (Option B — membership)

Relates henret's `readyQ` to the *union* of all worker queues by
membership, not order:

- `sound` — every queued task is ready;
- `complete` — every ready task is queued on some worker;
- `worker_nodup` — each worker queue is duplicate-free;
- `global_unique` — a task is queued on at most one worker.

Order is deliberately not preserved: a work-stealing scheduler does not
maintain a single global ready order, so a membership relation is the
right invariant — it survives `Steal` where list-equality would not.

### Multi-worker `Steal` semantics

`applyMQOp`'s `Steal src dst` actually moves the head of `src`'s queue to
`dst`'s tail (the single-worker `applyQOp` left `Steal` a no-op).
`Wake`/`Inject` target worker 0 (wake-to-worker-0 policy, deterministic
and compatible with the single-worker projection).

### Theorems

- `single_bridge_implies_multi_bridge` — the single-worker `BridgeState`
  is a strict special case (given `readyQ.Nodup`).
- `multi_bridge_push`, `multi_bridge_filter`, `multi_bridge_steal` —
  per-op membership preservation. `multi_bridge_steal` is the headline:
  work stealing moves a task between workers without changing the ready
  set.
- `reachable_multi_bridge` — every reachable state has a `WorkerQueues`
  witness satisfying `MultiBridgeState`, via the single-worker trace
  theorem and `reachable_wf.readyQ_nodup`.

### Design constraint honoured

No worker-placement field added to `RuntimeState`. Worker assignment
stays a bridge/refinement concern; the kernel remains actor/task
semantic, per RFC 043's design decision.

### Axiom budget: unchanged

`single_bridge_implies_multi_bridge` uses only `propext`;
`reachable_multi_bridge` adds `Classical.choice` and `Quot.sound`
(via `reachable_wf`). No project axioms. Verified by
`scripts/axiom_audit.py`.

---

## v0.11.1 — Selective Receive (RFC 041)

Adds `receiveByOccurrence (t : TaskId) (occ : MessageId)` and
`receiveFrom (t : TaskId) (src : ActorId)` as ops 15–16. Both use
**Option A (Mesa-style) blocking**: when no matching envelope is present
the task parks in the ordinary `mailboxWaiters` list. Any future
delivery wakes it; the task re-runs the selective receive. Blocking is
mailbox-level, not selector-level. Spurious wakeups are possible and
explicitly documented.

### Mailbox foundation: `listDequeueFirst`

New structural-recursion primitive in `Henret/Actor/Mailbox.lean`.
Removes the first list element satisfying a decidable predicate while
preserving the relative order of every other element. Properties:
`..._matches`, `..._mem`, `..._sublist`, `..._none` — all proved by
structural induction, avoiding index arithmetic entirely.

### Preservation

`preserves_wf_receiveByOccurrence` and `preserves_wf_receiveFrom` —
all 28 `WellFormed` fields. The occurrence-uniqueness bullets
(`occ_fresh`, `occ_nodup`, `occ_disjoint`) use `dequeueFirst_sublist`'s
`Sublist` relation instead of `dequeue_spec`'s head-removal `hcons`.

### Behavioral theorems (section `SelectiveReceive`)

- `receiveByOccurrence_removes_matching` — returned envelope has `occurrence = occ`
- `receiveFrom_source_matches` — returned envelope has `source = some src`
- `receiveByOccurrence_parks_on_miss` / `receiveFrom_parks_on_miss` — parks on no-match
- `receiveByOccurrence_preserves_nonmatching_order` / `receiveFrom_preserves_nonmatching_order` — `Sublist` order preservation

### Bridge and wiring

`toQOps` emits `[]` for both ops (no readyQ effect); `bridge_step_single_worker`
now covers all **16 `RuntimeOp`s**. `step_preserves_parent`,
`step_taskParent_stable`, `Timers`, `Ownership` all updated.

### Axiom budget: unchanged

No new axioms. All new proofs depend only on `propext`, `Quot.sound`,
and `Classical.choice`. Verified by `scripts/axiom_audit.py`.

---



Adds `receiveUntil (t : TaskId) (deadline : Nat)` as the 14th `RuntimeOp`,
completing the actor-system's timed-receive semantics. A task can park on an
empty mailbox with a hard deadline; `tick` wakes it when the timer expires.

### New `TaskState`: `.waitingTimed`

A sixth runnable variant. Tasks in `.waitingTimed` are registered in the
actor-local `timedMailboxWaiters` list **and** in the timer wheel with a
`waitDeadline` entry. Distinguished from `.waiting` (no deadline) and
`.sleeping` (no mailbox).

### `WellFormed` extended to 28 fields (+7)

Six new timed invariants (fields 22–27) describe the relationship between
`.waitingTimed` task state, `timedMailboxWaiters`, `timers`, and `waitDeadline`.
A seventh field, **`timed_waiters_exclusive`** (field 28), closes the
cross-actor uniqueness gap: a task appears in at most one `timedMailboxWaiters`
list. This exclusivity was required for `timed_waiters_valid` preservation
across `send`/`inject` timed-waiter wakeups.

### New and updated proofs (all zero `sorry`, all 28 fields)

- **`preserves_wf_receiveUntil`** (`Preservation/Messaging.lean`) — 28-field
  preservation proof across three sub-cases: immediate dequeue, past-deadline
  no-op, and park-with-deadline.
- **`preserves_wf_send`**, **`preserves_wf_inject`** — updated for the timed-waiter
  fallback path (when `mailboxWaiters b = []` but `timedMailboxWaiters b` is non-empty).
- **All six other operations** (Lifecycle, Time, Supervision) — 27→28 fields;
  `timed_waiters_exclusive` passes through cleanly for ops that don't modify
  `timedMailboxWaiters`.
- **`step_preserves_parent`** (`Parenthood.lean`) — `receiveUntil` added to the
  `taskParent`-stable match arm.

### Bridge layer updated

- **`toQOps`** (`Bridge/Grammar.lean`): `send`/`inject` now emit `Push 0 w` for
  the timed-waiter fallback; `tick` emits `Push 0 u` for both `.sleeping` and
  `.waitingTimed` woken tasks.
- New grammar lemmas: `toQOps_send_valid_timed_waiter`,
  `toQOps_inject_valid_timed_waiter`.
- `toQOps_tick_valid` updated to include both woken classes.
- **`bridge_step_single_worker`** now covers all **14 `RuntimeOp`s** including
  `receiveUntil` (emits `[]`; readyQ unchanged in all three branches).

### Axiom budget: unchanged

All new proofs depend only on `propext`, `Quot.sound`, and `Classical.choice`
(the last used by `by_cases` / `obtain`; present since RFC 013). Zero project
axioms added. Verified by `scripts/axiom_audit.py`.

---



Adds proof infrastructure in `StepFields.lean` that reduces the most repetitive
WellFormed preservation bullets to one-liners.

### New file: `Henret/Proofs/StepFields.lean` (147 lines, zero `sorry`)

Five helper theorems:

- **`wf_occ_fresh_pass`** — `occ_fresh` holds in `s'` when both `mailboxes` and
  `nextMsgId` are unchanged relative to `s`.
- **`wf_occ_nodup_pass`** — `occ_nodup` holds in `s'` when `mailboxes` is unchanged.
- **`wf_occ_disjoint_pass`** — `occ_disjoint` holds in `s'` when `mailboxes` is
  unchanged.
- **`wf_parent_lt_pass`** — `parent_lt` holds in `s'` when `taskParent` is unchanged.
- **`wf_parent_spawned_pass`** — `parent_spawned` holds in `s'` when `taskParent`
  is unchanged and spawned tasks stay spawned.

`OccFields` structure and `wf_occ_pass` bundle all three occurrence bullets for
cases where callers need the full package.

### Preservation files updated

- **`Preservation/Lifecycle.lean`**: 901 → 887 lines. `schedule`, `yield`,
  `complete`, `cancel` occ/parent bullets refactored. `spawnChild` occ_*
  bullets refactored. `spawn` `parent_lt` refactored.
- **`Preservation/Messaging.lean`**: 651 → 645 lines. `send` and `inject`
  `parent_spawned` bullets refactored using `step_preserves_spawned`.
- **`Preservation/Time.lean`**: already refactored during RFC 038/039 development.

### Caveat documented

`step_preserves_spawned hst _` only applies when the goal's LHS is in
`((step s op).1).taskState` form. When simp has reduced the step result to a
struct literal in the proof context (currently the `receive` parking branch),
the manual case split remains. This is documented in `docs/proof-engineering.md`.

### New documentation

`docs/proof-engineering.md` — full before/after diff examples, usage rules,
when-to-use guidance, and a template for new operations.

### Invariants maintained
- Zero `sorry`, zero project-specific axioms.
- `lake build Henret` passes cleanly (40 RFCs in `done/`).
- Doc-symbol check: 170 names verified.

---

## v0.10.0 — Supervision Semantics: Cascade Cancel (RFC 039)

Adds the first supervision operation: `cancelTree root`, which cancels a task
and every task in its subtree (all tasks whose `taskParent` chain reaches `root`).

### New `RuntimeOp`: `cancelTree (root : TaskId)` (13th constructor)

Always returns `.ok`. Cancels root and all descendants regardless of
`root`'s spawn status (no-op if the subtree is empty or already terminal).

### New infrastructure (in `Henret/Scheduler/Model.lean`)

- **`isInSubtreeOf s root t : Bool`** — computable parent-chain check.
  Well-founded by strict decrease (`p < t` enforced at each step); returns
  `false` conservatively for non-decreasing chains.
- **`descendantsOf s root : List TaskId`** — the cancellation set: all tasks
  in `[0, nextId)` that are spawned and whose parent chain reaches `root`.
- **`applyCancelTree s toCancel : RuntimeState`** — direct conditional
  state transformer: `if t ∈ toCancel then (cancel t) else (leave t)`.
  All five affected fields (`taskState`, `readyQ`, `running`, `timers`,
  `mailboxWaiters`) are defined directly from the original state.

### New file: `Henret/Proofs/Supervision.lean` (290 lines, zero `sorry`)

Twelve theorems including `preserves_wf_cancelTree` (all 21 `WellFormed`
fields) and the correctness lemmas:

- `cancelTree_cancels_task` — non-terminal subtree tasks → `.cancelled`
- `cancelTree_preserves_task_state` — outside-subtree tasks unchanged
- `cancelTree_cancels_root` — root itself cancelled (if non-terminal)
- `cancelTree_removes_from_readyQ / timers / waiters` — cleanup verified

### Bridge extended

`toQOps (.cancelTree root)` emits `(descendantsOf s root).map (.Filter 0 ·)`,
completing the bridge coverage for all 13 RuntimeOps. `bridge_cancelTree` is
proved using two helper lemmas: `applyQOps_filters0_at0` (worker-0 value) and
`applyQOps_filters0_other` (non-zero workers unchanged).

### Proof engineering notes

- Import cycle avoided by placing `preserves_wf_cancelTree` in `Supervision.lean`
  (imports `Invariants` + `Ownership` only; `InvariantsPreservation` imports
  `Supervision`, not vice versa through `Parenthood`).
- `decide_eq_decide.mpr` proved critical for `Bool` equality from `Prop ↔ Prop`
  without triggering `▸` motive errors.
- Explicit `rw [← Bool.decide_and]` + `decide_eq_decide.mpr` replaced all
  `simp`-loop-prone predicate equality proofs.

### Invariants maintained
- Zero `sorry`, zero project-specific axioms.
- All 95 proof-trust-test-matrix claims pass.
- Doc-symbol check: 170 names verified.
- Demo scenario 10 (cancelTree regression) added to `Main.lean`.

---



Strengthens `WellFormed` with two new exactness fields and generalizes
the `spawnChild` theorem family to properly separate parent actor from
child actor.

### New `WellFormed` fields (21 total, up from 19)

- **`owner_spawned`** (field 20) — every task with a `taskOwner` has a
  `taskState`; i.e., owned tasks are always spawned.
- **`parent_child_spawned`** (field 21) — every task with a `taskParent`
  has a `taskState`; i.e., tasks with parents are always spawned.

Both fields hold trivially in `init` (no owners or parents) and are
preserved by all 12 scheduler operations.

### Generalized `spawnChild` theorem family (`Henret/Proofs/Parenthood.lean`)

The `spawnChild` theorems previously conflated the parent task's actor
(`parentOwner`) with the child's actor (`childActor`), accepting only
the same-actor case. All four theorems now use separate `parentOwner` and
`childActor` parameters, accurately reflecting that a child may be owned
by any actor:

- `spawnChild_sets_parent` — child's `taskParent` = calling task id.
- `spawnChild_sets_owner` — child's `taskOwner` = `childActor` (not the
  parent's owner). *(RFC 038 key fix)*
- `spawnChild_queues_child` — child appended to `readyQ`.
- `spawnChild_child_spawned` — child's `taskState` = `some .new`. *(new)*

### New reachability corollaries

- `reachable_owner_spawned` — projects `WellFormed.owner_spawned` through
  `reachable_wf`.
- `reachable_parent_child_spawned` — projects `WellFormed.parent_child_spawned`
  through `reachable_wf`.

### Preservation updates

All three preservation files updated for the 2 new fields:
`Preservation/Lifecycle.lean`, `Preservation/Messaging.lean`,
`Preservation/Time.lean`. Each adds `import Henret.Proofs.Ownership`
for access to `step_preserves_spawned`.

### Invariants maintained
- Zero `sorry`, zero project-specific axioms.
- New fields depend only on Lean kernel axioms (`propext`, `Quot.sound`,
  `Classical.choice`).
- All 9 previous gate checks remain green.
- Doc-symbol check: 158 names verified (down 2 from 160 due to bare
  field names `owner_spawned`/`parent_child_spawned` correctly moved to
  IGNORE; their `WellFormed.X` fully-qualified forms remain checked).

---



Completes the single-worker queue-projection bridge and resolves all
v0.8.0 public claim issues identified in the architect review.

### RFC 037 — Public Claim Repair

- `docs/guided-tour.md` — replaced stale "Six scenarios" count with
  count-free prose matching the actual demo sequence.
- `scripts/check.sh` gate 6 — extended with v0.8.0 stale-phrase checks
  (hard-coded scenario count, parenthood field counts, provenance note,
  task-state claim, RFC 035 old title). All gates now green.
- All other RFC 037 edits (send provenance note, README messaging section,
  guided tour field counts, RFC 035 status) were already applied in the
  v0.8.0 working copy.

### RFC 036 — Bridge Claim Repair and Single-Worker Bridge Completion

#### QOp grammar (`Henret/Bridge/Grammar.lean`)
- `QOp.Filter` — new constructor for cancellation queue effect.
- `toQOps` rewritten to be fully guard-compatible: `toQOps s op = []`
  whenever `(step s op).2 = .invalid`, for all 12 operations.
  - `tick` now uses the argument `t` (not `s.now`).
  - `cancel` emits `[Filter 0 t]` for non-terminal tasks.
  - `send`/`inject` fully check running state, task state, owner, and
    mailbox existence before emitting queue effects.
  - `Wake` is no longer emitted (Design A per RFC 036); all wake effects
    are expressed as `Push 0 t`.
- New direct-effect lemmas: `toQOps_cancel_valid`,
  `toQOps_cancel_invalid_terminal`, `toQOps_cancel_invalid_unspawned`,
  `toQOps_send_valid_waiter`, `toQOps_send_valid_no_waiter`,
  `toQOps_inject_valid_waiter`, `toQOps_inject_valid_no_waiter`,
  `toQOps_inject_invalid`, `toQOps_tick_valid`, `toQOps_tick_invalid`,
  `toQOps_schedule_empty`, `toQOps_spawnChild_valid`.

#### BridgeState and queue model (`Henret/Bridge/State.lean`)
- `WorkerQueues.init` — empty initial worker-queue map.
- `bridgeState_filter0` — BridgeState is preserved by `Filter 0 t`.
- `applyQOp .Filter` — removes all occurrences of task `t` from a worker's queue.
- `toQOpsTrace` — state-threading trace translation for the trace theorem.

#### Bridge preservation (`Henret/Bridge/Preservation.lean`)
- New per-op theorems: `bridge_spawnChild`, `bridge_schedule`,
  `bridge_cancel`, `bridge_send`, `bridge_inject`, `bridge_tick`.
- `applyQOps_append` — `applyQOps wqs (as ++ bs) = applyQOps (applyQOps wqs as) bs`.
- **`bridge_step_single_worker`** — unified single-step bridge for all 12 `RuntimeOp`s.
- **`bridge_run_general`** — trace bridge from any starting `BridgeState`.
- **`bridge_run_tracks_single_worker`** — headline trace theorem:
  `BridgeState (run init ops) (applyQOps WorkerQueues.init (toQOpsTrace init ops))`.
- `reachable_bridge` now proved via `bridge_run_tracks_single_worker`.

#### Documentation
- `docs/bridge-architecture.md` — new document describing bridge scope,
  QOp grammar, translation table, headline theorems, and what is not claimed.
- `docs/proof-index.md` — bridge section updated for RFC 036 completion.
- `docs/proof-trust-test-matrix.md` — claims 80–84 added (all 12 bridge ops,
  bridge_step_single_worker, bridge_run_tracks_single_worker, scope notes).
- `scripts/check.sh` gate 5 — axiom audit extended with RFC 036 bridge theorems.
- `scripts/doc_symbol_check.py` — IGNORE list updated; 153 names now checked
  (up from 135); `open Henret.Bridge` added to preamble.

### Invariants maintained
- Zero `sorry`, zero project-specific axioms.
- All new bridge theorems depend only on `propext`, `Quot.sound`, and
  `Classical.choice` — the standard Lean 4 kernel axioms.
- `WellFormed` and all 19-field reachability proofs unchanged.

---

## v0.8.0 — Lean-Runtime Bridge (RFC 035)

Formally connects the henret model to the lean-runtime work-stealing scheduler.
Introduces the `Henret.Bridge` module: a `QOp` grammar translation, a
`BridgeState` relation, and per-operation preservation theorems covering spawn,
yield, wake, complete, receive, and sleep.

### New (`Henret/Bridge/Grammar.lean`)
- `QOp` — mirror of lean-runtime's queue-operation grammar (Push, Pop, Steal,
  Wake, Inject) as a henret-internal inductive type.
- `toQOps : RuntimeState → RuntimeOp → List QOp` — validity-aware translation;
  returns `[]` when `step` would return `.invalid` (guards are checked).
- Lemmas: `toQOps_spawn_valid/invalid`, `toQOps_yield_valid/invalid`,
  `toQOps_wake_valid/invalid`, `toQOps_complete/receive/sleep_nil`,
  `toQOps_schedule_nonempty`, `toQOps_send/inject_*_waiter`.
- `wake` emits `Push 0 t` (not `Wake t`), correctly reflecting that a waking
  sleeping task is appended to worker 0's ready queue.

### New (`Henret/Bridge/State.lean`)
- `WorkerQueues := WorkerIdx → List TaskId` — per-worker queue model.
- `BridgeState : RuntimeState → WorkerQueues → Prop` — `queue_eq` (worker 0
  equals henret's `readyQ`) + `other_empty` (single-worker model).
- `applyQOp`, `applyQOps` — queue-model application of QOp sequences.
- Structural constructors: `bridgeState_init`, `bridgeState_push0`,
  `bridgeState_pop0`, `bridgeState_readyQ_unchanged`.

### New (`Henret/Bridge/Preservation.lean`)
- `bridge_stable` — BridgeState is preserved by readyQ-stable steps.
- `reachable_bridge` — every reachable state has a `BridgeState` witness.
- `bridge_spawn`, `bridge_yield`, `bridge_wake` — Push-effect operations.
- `bridge_complete`, `bridge_receive`, `bridge_sleep` — readyQ-stable operations.

### Documented gaps (RFC 036 scope)
- `cancel` — filters `readyQ`; needs a `Filter` QOp.
- `send`/`inject` with waiter — append to readyQ on wake; needs `Push`.
- `tick` — wakes expired timers; needs `Push` per expiry.
- `schedule` — `Pop 0` case; building block `bridgeState_pop0` exists.

### Ecosystem
- `lean-runtime-workspace` confirmed buildable (all 37 targets) and all
  `runtimeTests` pass in the current sandbox environment.
- RFC 035 document moved from `rfcs/proposed/` to `rfcs/done/`.

---

## v0.7.0 — Message envelope and occurrence identity (RFC 033)

Delivers globally unique delivery identity: every envelope carried by `send`
or `inject` is stamped with a `MessageId` allocated from `nextMsgId`, and the
kernel proves that no two envelopes in any reachable state share the same id.

### Model changes

**`Henret/Actor/Mailbox.lean`**
- `MessageId := Nat` — occurrence-id type alias.
- `Envelope` (new structure) — `occurrence : MessageId`, `source : Option ActorId`,
  `body : Message`. The unit of in-transit storage; replaces bare `Message`.
- `Mailbox.messages : List Envelope` (was `List Message`).
- `Mailbox.enqueue : Mailbox → Envelope → Mailbox` (was `→ Message →`).
- `Mailbox.dequeue : Mailbox → Option (Envelope × Mailbox)`.

**`Henret/Scheduler/Model.lean`**
- `RuntimeState.nextMsgId : MessageId` (new field, init = 0).
- `send t b m` — stamps `env := ⟨s.nextMsgId, s.taskOwner t, m⟩`, bumps `nextMsgId`.
- `inject a m` — stamps `env := ⟨s.nextMsgId, none, m⟩`, bumps `nextMsgId`.
- `receive t` — dequeues an `Envelope`; `StepResult.received` now carries `Envelope`.

**`Henret/Core/Result.lean`**
- `StepResult.received` carries `Envelope` (was `Message`).

### New (`Henret/Proofs/Invariants.lean`)
- `WellFormed.occ_fresh` (field 17) — every envelope's occurrence id is
  strictly less than `nextMsgId`.
- `WellFormed.occ_nodup` (field 18) — within each mailbox all occurrence ids
  are distinct.
- `WellFormed.occ_disjoint` (field 19) — across different mailboxes all
  occurrence ids are distinct.
- `wf_init` extended to 19 fields.

### New (`Henret/Proofs/Occurrence.lean`)
- `reachable_occurrence_unique` — **headline**: in every reachable state, equal
  occurrence ids in any two (possibly equal) mailboxes imply the same envelope
  in the same mailbox. Globally unique delivery identity.
- `send_stamps_source` — the envelope delivered by `send t b m` carries
  `source = s.taskOwner t`.
- `inject_stamps_none` — the envelope delivered by `inject a m` carries
  `source = none`.

### Updated

**All three preservation files** — extended to 19 fields (3 new occ bullets per
refine block):
- `Henret/Proofs/Preservation/Lifecycle.lean` — 7 refine blocks.
- `Henret/Proofs/Preservation/Time.lean` — 3 refine blocks.
- `Henret/Proofs/Preservation/Messaging.lean` — 6 refine blocks;
  send/inject occ proofs use `send_appends` / `inject_appends` for
  the cons-waiter case.

**`Henret/Proofs/Messaging.lean`** — `send_appends`, `inject_appends`,
`receive_only_own`, `receive_consumes_one`, `receive_length` updated for `Envelope`.

**`Henret/Refinement/Contract.lean`** and **`ReferenceBackend.lean`** — updated:
`enqueue`/`dequeue`/`toList` now operate on `Envelope` (was `Message`).

**`Henret/Proofs.lean`** — exports `Henret.Proofs.Occurrence`.

### Demo and examples
- Scenarios 2 and 7 updated with exact `Envelope` constructor values (occurrence
  ids are deterministic and kernel-assigned).
- `examples/02_actor_mailbox.lean` — `#eval` comment updated; stale
  `spawn_sets_owner` reference replaced.

---

## v0.6.0 — Actor-scoped spawn and supervision groundwork (RFC 032)

Implements the actor-scoped spawn operation and its full kernel-proven
invariant structure. Extends `WellFormed` from 14 to 16 fields, adds the
`spawnChild` runtime operation, and delivers the acyclicity guarantee for
supervision trees.

### New (`Henret/Scheduler/Model.lean`)
- `RuntimeOp.spawnChild (t : TaskId) (a : ActorId)` — the running task `t`
  spawns a new child task owned by actor `a`.
- `RuntimeState.taskParent : TaskId → Option TaskId` — records each task's
  parent (set once at spawn, `none` for roots).

### New (`Henret/Proofs/Invariants.lean`)
- `WellFormed.parent_lt` (field 15) — every recorded parent has a strictly
  smaller `TaskId` than its child.
- `WellFormed.parent_spawned` (field 16) — every recorded parent is in some
  non-`none` state.
- `wf_init` extended to 16 fields.

### New (`Henret/Proofs/Parenthood.lean`)
- `spawnChild_sets_parent`, `spawnChild_sets_owner`, `spawnChild_queues_child`
  — direct effects of a valid spawn.
- `spawnChild_not_running_invalid`, `spawnChild_unowned_invalid` — guard
  theorems.
- `step_preserves_parent` — `taskParent` is immutable after creation; only
  `spawnChild` writes it and only to the fresh slot.
- `reachable_parent_lt` — headline: in every reachable state every parent has
  a smaller id than its child.
- `parent_chain_terminates` — acyclicity deliverable: every ancestor chain
  reaches a root in at most `t + 1` steps.

### New (`Henret/Proofs/StepProjections.lean`)
- `spawnChild_taskState_other`, `spawnChild_taskOwner_other`,
  `spawnChild_taskParent_other`, `step_taskParent_stable`.

### Extended (`Henret/Proofs/Preservation/`)
- `preserves_wf_spawnChild` (new) — all 16 WF fields for the new operation.
- All 11 existing preservation theorems extended to the 16-field `WellFormed`.

### Extended (`Henret/Proofs/InvariantsPreservation.lean`)
- `step_preserves_wf` dispatch extended with `spawnChild` case.

### Extended (`Henret/Proofs/Ownership.lean`)
- `step_preserves_spawned`, `step_preserves_terminal`, `step_invalid_unchanged`
  extended with `spawnChild` cases.

### Extended (`Henret/Proofs/Timers.lean`)
- `step_clock_monotone`, `run_preserves_sorted` extended.

### New (`Henret/Examples/Basic.lean`)
- Demo scenario 8: `spawnChild` round-trip (3 `native_decide` checks).

### Updated docs
- `docs/proof-trust-test-matrix.md` rows 57–63.
- `docs/proof-index.md` RFC 032 section.
- `docs/guided-tour.md` section 9b.
- `scripts/check.sh` and `scripts/axiom_audit.py` updated.


## v0.5.1 — release-gate repair and RFC 031 completion (RFC 035)

Resolves all six release-blockers from the v0.5.0 architect review.
Zero public-surface semantic change to the model; proof additions only.

### Added (theorems)
- `receive_blocked_parks` — result-driven form of the parking theorem:
  from an observed `.blocked` result alone, reconstructs all four guards
  (running, `.running` state, owned, empty own mailbox) and the complete
  post-state (task `.waiting`, running cleared, task in `mailboxWaiters`,
  other actors' lists and mailboxes unchanged). Mirrors `receive_only_own`.
- `reachable_waiters_exact` — exact waiter characterization: in every
  reachable state, `t ∈ mailboxWaiters a ↔ taskState t = .waiting ∧
  taskOwner t = a`. Mirrors `reachable_queue_exact` (RFC 031 acceptance
  criterion, previously deferred).
- `reachable_waiter_actor_unique` — a task is in at most one waiter list;
  list membership determines the actor via ownership.
- `reachable_waiting_is_queued` — every reachable `.waiting` task is
  in its own actor's `mailboxWaiters` list (thin corollary of the WF field).

### Added (demo)
- Demo scenario 7 replaced with the full RFC 031 round trip: park →
  inject → wake head waiter → re-schedule → re-receive → consume
  (12 runtime checks). Includes Mesa-semantics check that the message
  remains in the mailbox until the re-issued receive consumes it.

### Fixed (release gates — RB-01)
- `scripts/check.sh`: removed `step_blocked_unchanged`; added
  `receive_empty_parks`, `receive_blocked_parks`, `reachable_waiters_exact`,
  `reachable_waiter_actor_unique`.
- `scripts/axiom_audit.py`: same allowlist update.

### Fixed (examples — RB-02)
- `examples/04_send_receive.lean`: replaced `receive_empty_blocked` with
  `receive_empty_parks` / `receive_blocked_parks`; added `#eval` demos
  for the parking and wake-one round trip; updated StepProjections
  reference to RFC 031 scope.
- `examples/README.md`: updated example 04 theorem list.

### Fixed (docs — RB-03, RB-04, Task 6)
- `README.md`: replaced stale no-op blocked claim with parking claim;
  updated StepProjections description to RFC 031 scope.
- `docs/proof-trust-test-matrix.md`: rows 9, 10, 42, 47, 48 rewritten.
- `docs/proof-index.md`: stale `receive_empty_blocked` /
  `step_blocked_unchanged` replaced; StepProjections description scoped.
- `docs/test-index.md`: scenario 7 row updated to park/deliver/consume.
- `docs/guided-tour.md`: new section 8 explaining `mailboxWaiters` as a
  notification queue, Mesa semantics, and the exactness theorem.

### Axiom audit
All new theorems depend only on `[propext, Quot.sound]`. No `sorryAx`.

## v0.5.0 — blocked waiting state + preservation-proof modularity (RFCs 031, 034)

Turns the transitional "blocked receive" result from v0.4.0 into real
execution-management state: a blocked receive parks the running task
(`TaskState.waiting`), and each subsequent `send`/`inject` to that actor's
mailbox wakes exactly one head waiter.

### Added
- `TaskState.waiting` — a parked task; not in the ready queue, not running.
  Distinct from `.sleeping` (timer-blocked).
- `RuntimeState.mailboxWaiters : ActorId → List TaskId` — per-actor FIFO
  wait queue, invariant-backed.
- Four new `WellFormed` fields (fields 11–14): `waiters_waiting`,
  `waiters_owned`, `waiting_queued`, `waiters_nodup`.
- `wf_init` proves all 14 WF fields for the initial state.
- `receive` (empty-mailbox, valid branch): parks the running task
  (`TaskState.waiting`), clears `running`, appends to `mailboxWaiters a`.
- `send`/`inject` (valid branch, wake-one): if the target actor has a
  non-empty wait queue, dequeues the head waiter to `.ready` and
  appends it to `readyQ`; nil branch unchanged.
- `cancel` removes the task from its owner actor's `mailboxWaiters`.
- `showState` in `Examples/Basic.lean` handles `| waiting =>`.

### Changed (proof layer)
- All three preservation files (`Lifecycle`, `Messaging`, `Time`) prove all
  14 WF fields per operation (up from 10).
- `Messaging.lean` preservation: full case-trees for nil/cons wake-one
  branches of send/inject; nil/dequeue/parking branches of receive.
- `Time.lean` preservation: four new waiter fields — time ops do not touch
  `mailboxWaiters`, so all four close by pass-through.
- `preserves_wf_cancel` extended with taskOwner-case-split waiter proofs.
- `preserves_wf_inject` added (was inadvertently dropped in v0.5.0 split).

### Axiom audit
All new theorems depend only on `[propext, Quot.sound]`. No `sorryAx`.

### Changed (RFC 034 — preservation-proof modularity)
- `Henret/Proofs/InvariantsPreservation.lean` split from 780 to 102
  lines (assembly only). Per-operation WellFormed preservation proofs
  moved to:
  - `Henret/Proofs/Preservation/Lifecycle.lean` (spawn/schedule/yield/
    complete/cancel)
  - `Henret/Proofs/Preservation/Messaging.lean` (send/receive/inject)
  - `Henret/Proofs/Preservation/Time.lean` (sleep/tick/wake)
- `step_preserves_wf` body is a dispatch table.
- Each per-op lemma is self-contained; adding an operation or invariant
  field now touches one focused file.


## v0.4.1 — public claim cleanup (RFC 030)

Resolves all five release-blockers of the v0.4.0 review; the reviewer's
prerequisite for public v0.4.x tagging.

### Fixed
- README "model in one minute" operation list includes `inject` (RB-01).
- Proof index: flagship case analysis described over the eleven-operation
  grammar (RB-02); `WellFormed` described by its current ten-field
  surface (RB-03).
- `Henret.Proofs` barrel docstring made count-free (RB-04).
- README proof summary gains the v0.4.0 headlines: schedulable
  completeness and blocked receive (RB-05).
- Example 04 separates the non-running guard demo from the ownership
  guard theorem (SF-02).

### Added
- Demo scenario 7: blocked vs invalid receive, split from scenario 6;
  test index updated (SF-03).
- Gate 6 current-surface phrases for stale operation/field counts (SF-01).
- Transitional framing for `blocked` in README and matrix: a no-op
  result, not a waiting-state transition (SF-04).


## v0.4.0 — schedulable completeness + blocked receive (RFCs 028–029)

The two semantic priorities named by the v0.3.0 review.

### Added
- `WellFormed.runnable_queued` (tenth field): every runnable task is in
  the ready queue. Headlines `reachable_runnable_is_queued` and
  `reachable_queue_exact` (queue membership ⟺ runnable) — the runtime
  provably never loses a runnable task (RFC 028).
- `StepResult.blocked`; empty own-mailbox receive now blocks instead of
  being invalid; `receive_empty_blocked`; mirror theorem
  `step_blocked_unchanged` (RFC 029).
- Demo checks distinguishing blocked (legal wait) from invalid
  (protocol violation).
- Sleep past-deadline policy made explicit in the grammar docs: legal,
  wakes at next valid tick (SF-03 resolved by documented decision).

### Changed
- `receive_empty_invalid` renamed/restated as `receive_empty_blocked`.


## v0.3.1 — public-claim repair (RFCs 026–027)

Resolves all five release-blockers of the v0.3.0 review; first release the
external reviewer's criteria would tag as public-quality.

### Fixed
- Stale pre-RFC-024 theorem references in the proof index and matrix
  replaced with the `StepProjections` lemma family (RB-01).
- Guided tour shows the eleven-operation grammar and `receive_only_own`
  (RB-02).
- `Mailbox.lean` message-ownership overclaim reworded to per-operation
  value semantics (RB-03); matrix row 7 scoped.
- `Henret.Model` documented as a light import, not definition-only (RB-04;
  decision recorded in RFC 027).
- `lakefile.lean` import comment matches RFC 025 (RB-05).
- `send` docstring: existence provenance, not message provenance (SF-04).

### Added
- Gate 7: `scripts/doc_symbol_check.py` — every backticked theorem name in
  the proof docs must `#check` (99 names verified); gate 6 phrase list
  extended (SF-05).


## v0.3.0 — actor-scoped operations (RFCs 024–025)

Breaking: the operation grammar changes. `send`/`receive` are now
task-scoped; `inject` is the new environment delivery path.

### Added
- `send t b m` (running task → actor), `receive t` (task receives from
  its **own** actor's mailbox, derived from `taskOwner`), `inject a m`
  (environment → actor). Eleven operations total (RFC 024).
- **`receive_only_own`** — actor-local receive discipline, the RFC 024
  headline, kernel-checked and audit-allowlisted.
- Guard theorems: `send_not_running_invalid`, `send_unowned_invalid`,
  `receive_unowned_invalid`.
- `Henret.Proofs.StepProjections` — messaging touches only `mailboxes`,
  21 `@[simp]` projection lemmas proved once.
- Mailbox monotonicity: `send/receive/inject_mailbox_isSome`.
- Import barrels `Henret.Model`, `Henret.Proofs`, `Henret.Refinement`;
  root `Henret` no longer imports examples (RFC 025).

### Changed
- All invariant/preservation proofs re-proved over the new grammar.
- Examples 02 (environment `inject`) and 04 (actor-scoped messaging with
  guard-failure demos) rewritten; demo mailbox scenario schedules a task
  and messages through it.


## v0.2.1 — review-hardening release (RFCs 019–023)

Resolves all five must-fixes of the v0.2.0 follow-up review.

### Added
- `WellFormed` strengthened to nine fields: `timers_sorted`,
  `spawned_has_owner`, `owned_has_mailbox`; preservation re-proved for all
  ten operations; new headlines `reachable_spawned_has_owner`,
  `reachable_owner_has_mailbox`, `reachable_timers_sorted` (RFC 019).
- `scripts/axiom_audit.py` — exact per-theorem axiom allowlist; rejects any
  unexpected project axiom; negative cases validated (RFC 020).
- `scripts/check.sh` gate 6 — documentation-consistency grep (RFC 021).
- Demo scenario 6 rebuilt: arbitrary-state stale-timer entry, asserting the
  tick filter consumes it and wakes nothing (RFC 021).
- `wakeOne_none` / `wakeMany_none` — waking never spawns.

### Changed
- `drivePopB` renamed `driveStackB` with an explicit orientation note
  relative to `DequeModel.toList`; `execDemo` framing removed (RFC 023).
- Message non-duplication claims scoped to per-operation value semantics;
  occurrence identity recorded as future work (RFC 022).
- Scenario counts and changelog history corrected (RFC 021).


## v0.2.0 — invariant discipline (review-resolution release)

Resolves all seven must-fix findings of the v0.1.0 architecture review
(`docs/reviews/v0.1.0-review-resolution.md`). Model changes: `RuntimeState`
gains `taskOwner` (RFC 014) and `now` (RFC 015); `tick` is guarded monotone
and wakes only genuinely sleeping tasks.

### Added
- `WellFormed` reachability invariant; `step/run_preserves_wf`,
  `reachable_wf`; ownership-location disjointness corollaries (RFC 013).
- `taskOwner` field; `spawn_sets_owner`, `step/run_preserves_owner`,
  `step_preserves_spawned` (RFC 014).
- `now` field; monotonic tick guard; `tick_advances_clock`,
  `tick_backwards_invalid`, `step_clock_monotone` (RFC 015).
- `step_invalid_unchanged` (RFC 016).
- `scripts/check.sh` five-gate release script + GitHub Actions CI (RFC 017).
- Documentation consistency sweep: accurate lifecycle transition tables,
  standardized native-boundary wording (RFC 018).
- Demo scenario 6: seven regression checks for the v0.2.0 model.
- Examples 02/05 extended (`taskOwner`, monotone clock).

### Changed
- `tick now` filters its woken list to tasks whose state is `.sleeping`,
  keeping the ready queue clean in arbitrary states (review must-fix 4).
- Timer theorems take a `s.now ≤ now` validity hypothesis.


## v0.1.0 — 2026-06-04

First public release: the Lean-only actor/task model.

### Added
- `Henret` Lean-only core package (Lean 4.15.0 / Lake; no native deps).
- Actor/task model: `TaskId`/`ActorId`, `TaskState` lifecycle with terminal
  `completed`/`cancelled`, `Message`/`Mailbox`/`ActorState` (RFC 004).
- Scheduler semantics: `RuntimeOp` grammar, total executable
  `step`/`run`/`runTrace`, invalid ops are guaranteed no-ops (RFC 005).
- Message/wake semantics with ownership and exactness proofs (RFC 006).
- Logical-time timers: sorted queue, `sleep`/`tick`/`wake`, no-early-wake and
  expired-wake proofs, sortedness preservation (RFC 007).
- Drivers: op-level fueled `driveOps` (tested) and model-level `drain` with
  proven liveness `drain_completes`.
- Refinement: `MailboxBackend` contract and two proven reference backends (RFC 008).
- Proof/trust/test matrix and proof/assumption/test indexes (RFC 009).
- `henret-demo` executable with five self-checking scenarios.
- Docs: README, positioning, naming/scope, prior-art, guided tour,
  refinement-contract pattern.
- RFC lifecycle directories per RFC 000 (`proposed/`, `done/`, `archive/`).

### Trust status
- 0 `sorry`, 0 custom axioms, 0 `native_decide`; `#print axioms` reports only
  `propext`/`Quot.sound` for all exported theorems.

### Added (continued — examples and full RFC closure)
- `examples/` directory with 9 self-contained educational examples
  (`01_task_lifecycle` through `09_optional_ffi_boundary`), each teaching one
  concept, all verified with `lake env lean`.
- `examples/README.md` learning-order index.
- RFC 011 (Examples and Guided Tour) → `rfcs/done/`.
- RFC 012 (Release, Docsite, and Community) → `rfcs/done/`; all 11 of 12 RFCs
  now done; RFC 010 (optional FFI boundary) landed later within v0.1.0
  (see the dedicated section below).

### Added (RFC 010 — Optional Native Backend Boundary)
- `Henret/Native/DequeModel.lean` — `DequeModel` abstract contract (6 laws,
  `toList` observation, analogous to `MailboxBackend`); `listDeque` reference
  implementation (laws by `rfl`); `qRun_tracks` (whole-program refinement,
  PROVEN, `propext` only); `drivePopB_complete` (LIFO driver liveness, PROVEN).
- `Henret/Native/Assumptions.lean` — 6 typed axioms for `NativeDeque`; 
  `nativeDequeModel : DequeModel`; `nativeDequeModel_qRun_tracks` (PROVEN given
  the 6 axioms); axiom audit: `#print axioms` lists exactly 6 named axioms.
- `lakefile.lean` — `HenretNative` lib target (`lake build HenretNative`).
- `docs/native-backend-boundary.md` — the trust discipline, audit script,
  OUTSCOPE claims, conformance testing plan.
- `docs/assumption-index.md` — updated with 6 `NativeDeque` axioms.
- `docs/proof-trust-test-matrix.md` — rows 18–28 for native layer.
- `docs/proof-index.md` — native theorem inventory.
- `examples/09_optional_ffi_boundary.lean` — updated to use real modules.
- RFC 010 → `rfcs/done/`. All 12 RFCs now done.
