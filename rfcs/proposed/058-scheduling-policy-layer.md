---
rfc: 58
title: Scheduling Policy Layer
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC 058 — Scheduling Policy Layer

## Status

Proposed.

## Summary

Introduce a policy-parametric scheduling layer while preserving the core ready-queue exactness invariant.

## Motivation

Henret currently models readyQ membership exactly, but not a sophisticated scheduling policy. As advanced features arrive, the project should distinguish safety of queue membership from policy-specific ordering such as FIFO, priority, deadline, or actor fairness.

## Non-goals

- Do not replace the current core scheduler.
- Do not prove fairness in this RFC.
- Do not make policy semantics depend on native thread behavior.
- Do not encode every future policy now.

## Design

Define a policy interface over ready tasks:

```lean
structure SchedulingPolicy where
  choose : RuntimeState → Option TaskId
  choose_sound : ∀ s t, choose s = some t → t ∈ s.readyQ
```

Then define a policy-aware schedule operation or derived runner:

```lean
def policyStep (p : SchedulingPolicy) (s : RuntimeState) : RuntimeState × StepResult
```

Core `RuntimeOp.schedule` may remain as the default queue-pop schedule.

## Formal model changes

- Add `PolicyTrace` if schedule decisions need to be recorded.
- Keep `WellFormed.runnable_queued` independent of policy.

## Proof obligations

- `policy_choose_sound` for built-in policies.
- `policyStep_preserves_wf`.
- `fifo_policy_equiv_schedule` if default schedule is FIFO.
- `policy_does_not_create_task`.

## Tests and examples

- Demo: FIFO policy.
- Demo: actor-round-robin policy if simple enough.
- Trace comparison showing same safety invariants under two policies.

## Documentation updates

- Add policy layer to profile index.
- Explain that policy changes order, not core safety.

## Acceptance criteria

- At least one built-in policy implemented and proved sound.
- Policy scheduling preserves `WellFormed`.
- Core model remains unchanged or compatibility-preserved.

## Risks and review questions

- Should policies return one task or a list/batch?
- Should policies be pure functions or structures with internal policy state?
- How should actor fairness be represented?
