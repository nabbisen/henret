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

## Scope (deferred to later Tier-2 slices)

- A **breaking** global `stopped → Drained` invariant (would require
  strengthening `stopWhenIdle` and entangle every op that can fire after
  `stopped`).
- **Actor-owned** (longer-lived) resources — resources remain task-owned.
- Any **wall-clock liveness / timeliness** guarantee.
