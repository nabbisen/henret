# Henret Integration Contract

**Status.** Stable as of v0.12.0 (RFC 044).
**Audience.** Downstream runtimes, actor frameworks, and verification
projects that want to use Henret as a semantic reference model.

This document is the boundary contract. It tells a consumer what it may
rely on, what is experimental, and what is explicitly not proved. It is
not a tutorial — see `docs/guided-tour.md` to learn the model.

---

## 1. Project role

> **Henret is a semantic reference model, not a runtime library.**

Use Henret to *specify and check* actor/task scheduler behavior, not to
execute production workloads. The model is executable (`step`, `run`)
for testing and exploration, but its value is the machine-checked
guarantees, not throughput.

---

## 2. Stable imports

| Import | Stability | Meaning |
|---|---|---|
| `import Henret.Model` | **stable** model surface | operations, state, `step`/`run` |
| `import Henret.Proofs` | **stable** theorem surface (names may grow) | public safety theorems |
| `import Henret.Refinement` | **stable** pattern surface | backend refinement contracts |
| `import Henret.Bridge` | **stable** as of v0.12.0 | single- and multi-worker queue bridge |
| `import Henret.Native.*` | optional / **trusted** | axiom-bearing native boundary (separate Lake package) |
| `Henret.Examples.*`, `examples/*` | **unstable** | examples only — do not depend on |

A consumer that imports only `Henret.Model` and `Henret.Proofs` depends
on nothing experimental.

---

## 3. Operation mapping guide

`RuntimeOp` has **16 constructors** as of v0.12.0. Map external runtime
events as follows:

| External event | Henret op |
|---|---|
| create root task | `spawn actor` |
| running task creates child | `spawnChild task actor` |
| scheduler selects next task | `schedule` |
| task voluntarily yields | `yield task` |
| task sends message | `send task actor body` |
| external message arrives | `inject actor body` |
| task receives (FIFO head) | `receive task` |
| task receives with deadline | `receiveUntil task deadline` |
| task receives a specific occurrence | `receiveByOccurrence task occ` |
| task receives from a specific source | `receiveFrom task source` |
| task sleeps | `sleep task deadline` |
| timer advances | `tick now` |
| external direct wake | `wake task` |
| task completes | `complete task` |
| task cancels | `cancel task` |
| cancel a task and its subtree | `cancelTree root` |

---

## 4. Mesa semantics contract

Henret uses **Mesa-style** wakeups. A consumer must handle:

- a delivery (`send`/`inject`) wakes **at most one** waiter;
- wake does **not** atomically hand off the message — the woken task is
  merely made runnable;
- a woken task **must re-run** its receive;
- another task may consume the message first, so the woken task may find
  the mailbox empty and re-park;
- **no per-message delivery guarantee** is implied unless a specific
  theorem states it.

Selective receive (`receiveByOccurrence`, `receiveFrom`) is also
Mesa-style with **mailbox-level** blocking: a no-match parks the task in
the ordinary waiter list, and *any* later delivery wakes it to retry.
Spurious wakeups are possible by design.

---

## 5. Occurrence identity contract

- every delivered envelope receives a fresh `occurrence : MessageId`,
  allocated from `RuntimeState.nextMsgId`;
- in every reachable state, equal occurrence ids imply the **same
  envelope in the same mailbox** (`reachable_occurrence_unique`);
- `send` stamps the sending task's owning actor as `source = some a`
  (`send_stamps_source`);
- `inject` stamps `source = none` (environment delivery)
  (`inject_stamps_none`).

---

## 6. Supervision contract

Parenthood is modeled and acyclic: in every reachable state a parent has
a strictly smaller id than its child (`reachable_parent_lt`), so parent
chains terminate (`parent_chain_terminates`).

Cascade cancellation **is** part of the stable contract as of v0.10.0:
`cancelTree root` cancels every non-terminal spawned task in `root`'s
subtree, removes them from `readyQ`, timers, and all waiter lists, and
preserves all `WellFormed` fields. Restart policies are **not** yet
modeled (deferred to RFC 049).

---

## 7. Bridge contract

| Property | Value (v0.12.0) |
|---|---|
| Bridge levels | single-worker (exact-list) and multi-worker (membership) |
| Single-worker relation | `BridgeState` — `s.readyQ = wqs 0`, other workers empty |
| Multi-worker relation | `MultiBridgeState` — membership union, global uniqueness, per-worker nodup |
| Operations covered | all 16 `RuntimeOp`s (single-worker headline) |
| Single-worker headline | `bridge_run_tracks_single_worker` |
| Multi-worker headline | `reachable_multi_bridge` |
| Special-case lemma | `single_bridge_implies_multi_bridge` |

The multi-worker bridge preserves **membership, not order** — work
stealing does not preserve a global ready order. The bridge is a
model-level queue projection. **It does not prove native concurrency or
C race-freedom.**

---

## 8. Theorem contract

These are the **public theorem families**. A consumer may depend on
these names.

| Theorem | Guarantee |
|---|---|
| `reachable_wf` | every reachable state satisfies the 28-field `WellFormed` invariant |
| `reachable_queue_exact` | a task is in `readyQ` iff it is `.ready` |
| `reachable_waiters_exact` | a task is in `mailboxWaiters a` iff it is `.waiting` and owned by `a` |
| `reachable_waiter_actor_unique` | a waiting task waits on at most one actor |
| `receive_only_own` | a successful receive dequeues only the receiver's own actor's mailbox |
| `reachable_occurrence_unique` | occurrence ids are globally unique in reachable states |
| `reachable_parent_lt` | every parent id is strictly less than its child id |
| `parent_chain_terminates` | parent chains are finite |
| `reachable_spawned_has_owner` | every spawned task has an owning actor |
| `reachable_owner_has_mailbox` | every owning actor has a mailbox |
| `bridge_run_tracks_single_worker` | single-worker queue bridge tracks `readyQ` through any run |
| `reachable_multi_bridge` | multi-worker membership bridge holds for every reachable state |

**Do not depend on preservation helper lemmas** (e.g.
`preserves_wf_*`, `step_*`, `toQOps_*`, `bridge_*` per-op lemmas) unless
they appear in the table above. These are internal proof machinery and
their names may change.

---

## 9. Trust boundary

Henret separates claims into four honest classes:

1. **Kernel-proven** — everything under `Henret.Model`, `Henret.Proofs`,
   `Henret.Refinement`, and `Henret.Bridge`. Machine-checked by the Lean
   kernel; depends only on `propext`, `Quot.sound`, and `Classical.choice`.
   Zero project-specific axioms (verified by `scripts/axiom_audit.py`).
2. **Trusted** — the optional native FFI boundary
   (`Henret.Native.*`, a separate Lake package). A small, audited set of
   declared axioms models the C Chase–Lev deque's behavior. Not imported
   by the default model.
3. **Tested** — concurrent behavior (data-race freedom, real
   work-stealing interleavings) is exercised by harnesses, not proved.
   The genuine "cannot prove here" is concurrent race-freedom, which
   requires Iris-style concurrent separation logic.
4. **Out of scope** — fairness, liveness, native thread scheduling, OS
   worker management, and C race-freedom proofs.

---

## 10. Versioning policy

**Breaking changes** (will bump the minor/major version and be called
out in `CHANGELOG.md`):

- changing `RuntimeOp` constructor signatures;
- changing `RuntimeState` field names or types;
- changing `StepResult` constructors;
- weakening a public theorem statement;
- renaming or moving a public theorem from the table in §8.

**Non-breaking changes** (may appear in any release):

- adding new theorems;
- adding new operations (new `RuntimeOp` constructors are additive);
- adding new documentation or examples;
- adding stricter internal lemmas;
- proof refactors that preserve public theorem names.

---

## Worked example

See `examples/10_integration_contract.lean` for a consumer-style trace:
it maps a small actor scenario to Henret ops, runs it, and discharges
`reachable_wf` and `reachable_occurrence_unique` on the result.
