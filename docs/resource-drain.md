# Resource drain discipline (RFC 087 — RFC 057 Tier 2)

The first Tier-2 slice of the resource ledger, on the **safety / possibility**
axis. Two guarantees, both ordinary facts in the `step`/`run` model:

> **Not a liveness or real-time guarantee.** Nothing here says a resource *will*
> be finalized or that a stop *will* happen — only that finalization is always
> *available* and a drained stop is *possible*. Guaranteeing the scheduler
> actually drains needs a fairness policy, which (per RFC 059) Henret does not
> provide.

## Drain progress

```lean
theorem closing_finalize_releases (s) (r) (o)
    (h : s.resources r = some ⟨o, .closing⟩) :
    (step s (.finalize r)).2 = .ok ∧
    (step s (.finalize r)).1.resources r = some ⟨o, .released⟩
```

A `closing` resource is **always** finalizable in one step. Combined with the
Tier-1 results that terminal task transitions mark owned resources `closing`
(`complete/cancel/fail/cancelTree_marks_owned_resource_closing`), the drain path
is never blocked: terminal tasks produce `closing` resources, and any `closing`
resource can be finalized to `released`.

## Drain-before-stop

`stopWhenIdle` (RFC 055) transitions to `stopped` purely on quiescence
(`running = none ∧ readyQ = [] ∧ timers = []`) — it ignores the ledger, so it can
stop with resources still live. RFC 087 adds an opt-in, drain-gated stop:

```lean
| stopWhenDrained : RuntimeOp
```

It reaches `stopped` only when the runtime is quiescent **and** the ledger is
fully drained (`resourceDrained`, a decidable check bounded by `nextResourceId`).

- `Drained s := ∀ r rr, s.resources r = some rr → rr.state = .released` — no
  resource is still `allocated` or `closing`.
- `resourceDrained_drained` — under `WellFormed`, the decidable bounded check
  captures the unbounded `Drained` predicate (allocated ids are `< nextResourceId`
  by `resource_fresh`).
- `stopWhenDrained_stops_drained` — **if `stopWhenDrained` succeeds, the ledger
  was drained**: a drained stop never leaves a resource leaked.
- `stopWhenDrained_stops` / `stopWhenDrained_noop` — per-branch behaviour
  (quiescent ∧ drained ⇒ stops; otherwise a `.invalid` no-op).
- `preserves_wf_stopWhenDrained` — the operation only flips `runtimeStatus`, so
  it preserves all 33 `WellFormed` fields, exactly like `stopWhenIdle`.

`stopWhenIdle` is left untouched: the drained stop is additive and opt-in.

### Worked example

`acquire → complete` (marks the resource `closing`) `→ finalize` (drains it)
`→ stopWhenDrained` reaches `stopped`. Drop the `finalize` and `stopWhenDrained`
is refused (`.invalid`, runtime stays running) — the live resource blocks the
drained stop. Both paths are pinned as conformance scenarios
(`stopWhenDrained_drained_stops`, `stopWhenDrained_live_resource_invalid`).

## Drained-state persistence (RFC 088)

`stopWhenDrained_stops_drained` is a guarantee about the *instant* of stopping.
RFC 088 closes the one-step gap that follows: from a drained state with no
running task, **no single operation can leak a resource**.

```lean
theorem drained_step_drained (h_wf : WellFormed s)
    (h_run : s.running = none) (h_d : Drained s) (op : RuntimeOp) :
    Drained (step s op).1
```

The argument is structural rather than per-op: an already-present resource is
`released` and stays so under any operation (RFC 057's
`step_resources_eq_of_released`), and the only operation that writes a fresh
resource slot is `acquire`, which needs a running task — blocked by `h_run`
(the new lemma `step_resources_none_run_none`). Composing with the stop:

```lean
theorem stopWhenDrained_then_step_drained (h_wf : WellFormed s)
    (h : (step s .stopWhenDrained).2 = .ok) (op : RuntimeOp) :
    Drained (step (step s .stopWhenDrained).1 op).1
```

A successful `stopWhenDrained` keeps `running = none` and the ledger unchanged,
so the next operation cannot leak. Pinned by the conformance scenario
`stopWhenDrained_then_acquire_stays_drained` (a post-stop `acquire` is
`.invalid` and the ledger stays drained).

> **Multi-step permanence (RFC 090).** RFC 089's `quiescent_no_sleeping` closed
> the gap, and RFC 090 now proves the full result: from any reachable state,
> after a successful `stopWhenDrained`, the runtime stays drained *and* quiescent
> across every subsequent operation sequence
> (`reachable_stopWhenDrained_stays_drained`,
> `reachable_stopWhenDrained_stays_quiescent`). A drained stop is permanent.

## Scope (deferred to later Tier-2 slices)

- A **breaking** global `stopped → Drained` invariant (would require
  strengthening `stopWhenIdle` and entangle every op that can fire after
  `stopped`).
- **Actor-owned** (longer-lived) resources — resources remain task-owned.
- Any **wall-clock liveness / timeliness** guarantee.

## Unified drain over actor-owned resources (RFC 091)

`Drained` quantifies **all** resources regardless of owner kind, so the
drain-before-stop guarantee extends to actor-owned resources (RFC 091): a live
(`allocated`) or in-flight (`closing`) actor-owned resource blocks
`stopWhenDrained` exactly as a task-owned one does, and the stop succeeds only
once it is `finalize`d. The single-step and `Frozen` permanence results
(`drained_step_drained`, `step_preserves_frozen`) carry the extra hypothesis
`runtimeStatus ≠ .running`, which holds after any successful `stopWhenDrained`
(the runtime is `.stopped`); this blocks the new `acquireActor` allocation
surface — a control-plane op gated on `runtimeStatus = .running` — from
re-leaking a resource after a drained stop. Under `Drained`, `closeActor` is
inert on the ledger (`markActorResourcesClosing_eq_of_drained`), so the
permanence spine is unaffected.
