---
rfc: 90
title: Drained Permanence (Frozen invariant, RFC 057 Tier 2 payoff)
status: Implemented
implemented_in: v0.26.0
supersedes: []
superseded_by: []
depends_on: [57, 88, 89]
blocks: []
category: model-semantics
---

# RFC 090 — Drained Permanence (Frozen invariant)

## Status

Implemented (v0.26.0). Completes the safety/possibility spine of RFC 057
Tier 2 for `stopWhenDrained`. Actor-owned resources, the breaking global
`stopped → Drained` invariant, and wall-clock liveness remain deferred.

## Motivation

This is the end-to-end payoff of the drain/stop thread (RFCs 087–089). RFC 088
proved a drained stop survives **one** further operation; RFC 089 supplied the
missing coherence fact (a quiescent runtime has no sleeping tasks). Together
they make the full result reachable: a runtime stopped via `stopWhenDrained`
stays drained — and quiescent — for the rest of *any* operation sequence.

## The bundle

```lean
def Frozen (s : RuntimeState) : Prop :=
  s.running = none ∧ s.readyQ = [] ∧ s.timers = [] ∧
  s.runtimeStatus ≠ .running ∧ Drained s
```

`runtimeStatus ≠ .running` (not `= .stopped`) is deliberate: `shutdown` sends
`stopped → shuttingDown`, and both are `≠ running`; no operation ever returns
the runtime to `running`, so the predicate is stable under `shutdown`.

```lean
theorem step_preserves_frozen (h_wf : WellFormed s) (h_st : SleepingHasTimer s)
    (h_f : Frozen s) (op : RuntimeOp) : Frozen (step s op).1
```

Why each component survives any operation:

- **Drained** — directly RFC 088's `drained_step_drained` (running = none blocks
  the only allocator, `acquire`).
- **running = none / readyQ = [] / timers = []** — every operation that could
  set `running` or push to `readyQ`/`timers` is rejected: it needs a running
  task, a non-empty ready queue, or `runtimeStatus = running`, none of which
  hold. The one operation RFC 088 could not rule out — `wake` — is blocked by
  RFC 089's `quiescent_no_sleeping` (no sleeping task to wake).
- **runtimeStatus ≠ running** — no operation sets the status back to `running`;
  `shutdown`/`stopWhenIdle`/`stopWhenDrained` only move it further from it.

## The headlines

```lean
theorem reachable_stopWhenDrained_stays_drained (ops : List RuntimeOp)
    (h : (step (run RuntimeState.init ops) .stopWhenDrained).2 = .ok)
    (ops' : List RuntimeOp) :
    Drained (run (step (run RuntimeState.init ops) .stopWhenDrained).1 ops')

theorem reachable_stopWhenDrained_stays_quiescent (ops : List RuntimeOp)
    (h : (step (run RuntimeState.init ops) .stopWhenDrained).2 = .ok)
    (ops' : List RuntimeOp) :
    RuntimeQuiescent (run (step (run RuntimeState.init ops) .stopWhenDrained).1 ops')
```

From any reachable state, after a successful `stopWhenDrained`, the runtime
remains drained and quiescent across every subsequent operation sequence. A
drained stop is **permanent**, not merely momentary.

`stopWhenDrained_enters_frozen` establishes that the stop lands in `Frozen`;
`frozen_run_drained` carries `Frozen` across a whole run (also re-establishing
`WellFormed` and `SleepingHasTimer` at each step).

## Scope and non-goals

This completes the *safety/possibility* spine of RFC 057 Tier 2 for the
`stopWhenDrained` discipline. Still deferred (from RFC 087): actor-owned
resources, the breaking global `stopped → Drained` invariant (any stopped state,
including those reached by the non-draining `stopWhenIdle`), and wall-clock
liveness/timeliness.

## Proof obligations

| Obligation | Theorem |
|---|---|
| Every operation preserves `Frozen` | `step_preserves_frozen` |
| A successful `stopWhenDrained` lands in `Frozen` | `stopWhenDrained_enters_frozen` |
| `Frozen` is carried across a run | `frozen_run_drained` |
| Drained stop stays drained, permanently | `reachable_stopWhenDrained_stays_drained` |
| Drained stop stays quiescent, permanently | `reachable_stopWhenDrained_stays_quiescent` |
