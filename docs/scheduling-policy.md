# Scheduling policy layer (RFC 058)

Henret models *which ready task runs next* as a replaceable **policy**, layered
on top of the core scheduler without changing it. The separation is deliberate:
queue-membership safety (a task is runnable iff it is in `readyQ`) is a core
invariant; the *order* tasks run in is policy.

## Interface

```lean
structure SchedulingPolicy where
  choose       : RuntimeState → Option TaskId
  choose_sound : ∀ s t, choose s = some t → t ∈ s.readyQ
```

A policy is a **sound chooser**: it may pick any ready task (or abstain with
`none`), but it can never pick a task that is not ready. That single proof
obligation is all a policy must discharge.

## The derived runner

```lean
def policyStep (p : SchedulingPolicy) (s : RuntimeState) : RuntimeState × StepResult :=
  step (p.reorder s) .schedule
```

`reorder` moves the chosen task to the head of `readyQ` — a *permutation* of the
queue — and then the **unchanged** core `schedule` runs the head. Because the
reorder is a permutation, it preserves every `WellFormed` field
(`reorder_preserves_wf`), and so:

- `policyStep_preserves_wf` — **every** policy preserves all 33 invariant
  fields. This is parametric in the policy, so FIFO, LIFO, and any future sound
  policy inherit the full safety contract for free.
- `policy_does_not_create_task` — a policy step only chooses among existing
  ready tasks; it never allocates a task id.

## Built-in policies

- `fifoPolicy` chooses the queue head. `fifo_policy_equiv_schedule` proves it is
  exactly the core `schedule` (the head-to-head reorder is a no-op), so the
  default behaviour is unchanged.
- `lifoPolicy` chooses the queue tail — a genuinely different order
  (`fifo_picks_head` vs `lifo_picks_last`) that nonetheless preserves the same
  safety invariants, demonstrating that **policy changes order, not core
  safety**.

## Scope (RFC 058 non-goals)

The core scheduler is not replaced; there is no new `RuntimeOp`; **no fairness
claim** is made (a policy may starve a task — fairness is future work); and
policy semantics do not depend on native thread behaviour. Priority/deadline
metadata is RFC 059; stateful policies (round-robin with memory) and a
batch-choosing interface are open design questions recorded in the RFC.
