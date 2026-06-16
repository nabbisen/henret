---
rfc: 88
title: Drained-State Persistence (RFC 057 Tier 2)
status: Implemented
implemented_in: v0.24.0
supersedes: []
superseded_by: []
depends_on: [57, 87]
blocks: []
category: model-semantics
---

# RFC 088 — Drained-State Persistence (RFC 057 Tier 2)

## Status

Implemented (v0.24.0). Single-step persistence; multi-step permanence (needs a
`sleeping → timer` invariant), the breaking global `stopped → Drained`
invariant, actor-owned resources, and wall-clock liveness remain deferred.

## Motivation

RFC 087 established *drain-before-stop*: the additive `stopWhenDrained`
operation reaches `.stopped` only from a quiescent, fully-drained state
(`stopWhenDrained_stops_drained`). That is a guarantee about the *instant* of
stopping. It says nothing about what happens **after**: could a subsequent
operation re-introduce a live resource, silently undoing the no-leak property a
drained stop just established?

This RFC closes that one-step gap on the safety axis: from a drained state with
no running task, **no single operation can leak a resource**.

## The guarantee

```lean
theorem drained_step_drained (h_wf : WellFormed s)
    (h_run : s.running = none) (h_d : Drained s) (op : RuntimeOp) :
    Drained (step s op).1
```

The argument is structural, not enumerative:

- A resource that already exists is `released` (`h_d`) and stays `released`
  under *any* operation — this is exactly RFC 057's
  `step_resources_eq_of_released` (released records are immutable, including
  under `acquire`, which only ever writes a *fresh* id).
- The only operation that introduces a resource at a previously-empty slot is
  `acquire`, and `acquire` requires a running task. With `s.running = none` it
  is rejected, so no new (necessarily `allocated`) resource appears. This is
  the new lemma `step_resources_none_run_none`.

Together: every resource present after the step was present before, hence
`released`. No appeal to `cancel`/`fail`/`finalize` internals is needed beyond
the fact that they never write a fresh slot.

### Composition with RFC 087

A successful `stopWhenDrained` leaves `runtimeStatus = .stopped` while keeping
`running = none` (the guard) and the resource ledger unchanged (the op only
flips status). So the post-stop state satisfies the `drained_step_drained`
hypotheses, giving the payoff:

```lean
theorem stopWhenDrained_then_step_drained (h_wf : WellFormed s)
    (h : (step s .stopWhenDrained).2 = .ok) (op : RuntimeOp) :
    Drained (step (step s .stopWhenDrained).1 op).1
```

Immediately after a drained stop, the next operation cannot leak: the no-leak
property is robust to one further step.

## Scope and non-goals

This is deliberately a **single-step** result. Full *multi-step* permanence —
"a drained, stopped runtime stays drained for an arbitrary op sequence" — is
**not** proven here and is **deferred**. Multi-step permanence needs
`running = none` to be preserved across the whole run, which in turn requires
ruling out a `wake` re-populating `readyQ`. That depends on a `sleeping → timer`
invariant (the converse of the existing `timers_sleep`), which Henret's
`WellFormed` does not currently carry. Adding it is a separate, self-contained
piece of work tracked for a later Tier-2 slice.

Also still deferred (from RFC 087): the breaking global `stopped → Drained`
invariant, actor-owned resources, and wall-clock liveness/timeliness.

## Proof obligations

| Obligation | Theorem |
|---|---|
| No op allocates at an empty slot without a running task | `step_resources_none_run_none` |
| One step from drained + non-running stays drained | `drained_step_drained` |
| Post-`stopWhenDrained`, the next op stays drained | `stopWhenDrained_then_step_drained` |
