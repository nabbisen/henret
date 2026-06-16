---
rfc: 28
title: Schedulable Completeness Invariant
status: Implemented
implemented_in: v0.4.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: proofs
---

# RFC-HENRET-028: Schedulable Completeness Invariant

## Motivation

Through v0.3.1, `WellFormed` was safety-focused: `readyQ_queued` proved the
queue contains only runnable tasks ("the queue is clean"), but nothing
proved the converse. A model state could, in principle, hold a runnable
task that the scheduler had lost — for an execution-management model, the
v0.3.0 review called this the most important remaining invariant gap
(SF-01): "Henret can prove the queue is clean, but not that the runtime
never loses a runnable task."

## Design

A tenth `WellFormed` field, the exact converse of `readyQ_queued`:

```lean
  runnable_queued :
    ∀ t st, s.taskState t = some st → st.isRunnable = true → t ∈ s.readyQ
```

Together the pair characterizes the ready queue exactly: membership is
equivalent to being spawned in a runnable state.

## Theorems

- `step_preserves_wf` extended through all eleven operations. The
  interesting cases: `schedule` (the popped task leaves the queue but also
  leaves runnability — no obligation), `cancel` (others survive the queue
  filter because they differ from the cancelled task), `tick` (woken tasks
  are appended; unwoken runnables keep state by `wakeMany_preserves_other`
  and queue membership by append).
- **`reachable_runnable_is_queued`** — in every reachable state, every
  runnable task is in the ready queue.
- **`reachable_queue_exact`** — `t ∈ readyQ ↔ ∃ st, taskState t = some st ∧
  st.isRunnable` in every reachable state: the ready queue contains
  *exactly* the runnable tasks.

## Acceptance criteria

- [x] `reachable_runnable_is_queued` kernel-checked, audit-allowlisted.
- [x] Exact characterization (`reachable_queue_exact`) proved.
- [x] No task is silently lost from scheduler ownership: a runnable task
      is queued; a running task is in the slot (`running_runs`); a
      sleeping task has a timer entry — wait, the timer direction is
      `timers_sleep` (timer ⇒ sleeping); the converse (sleeping ⇒ has a
      timer) is intentionally NOT claimed, since `wake` exists precisely
      to handle direct wakes; the *scheduler-loss* concern is the runnable
      case, which is what this RFC closes.
