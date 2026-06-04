---
title: Blocked Receive Semantics
rfc: RFC-HENRET-029
status: Implemented (v0.4.0)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-029: Blocked Receive Semantics

## Motivation

Through v0.3.1, receive from an empty own mailbox returned `.invalid` —
conflating a normal actor condition (no message yet; the task would wait)
with a protocol violation (an unscheduled or unowned task attempting to
receive). The v0.3.0 review (SF-02) noted this distinction becomes load-
bearing once Henret grows toward waits, selective receive, or fairness
claims.

## Design

`StepResult` gains a constructor:

```lean
  | blocked : StepResult
```

`receive t` with all guards satisfied but an empty own mailbox returns
`(s, .blocked)` — state unchanged. The illegal paths are untouched:
non-running, non-`running`-state, and unowned receives remain `.invalid`.
`blocked` is currently produced only by `receive`; no task state changes
(a future RFC may park the task in a `waiting` state once selective
receive or supervision needs it — recorded here as the natural extension).

## Theorems

- `receive_empty_blocked` — guards + empty own mailbox ⇒ `(s, .blocked)`
  (renames and restates `receive_empty_invalid`).
- **`step_blocked_unchanged`** — a blocked operation never mutates state:
  the mirror of `step_invalid_unchanged`, full eleven-operation case
  analysis (all non-receive branches discharge by constructor
  contradiction).
- `receive_only_own`, the projections, and the mailbox-monotonicity lemmas
  are unaffected (the blocked branch returns `s`).

## Sleep past-deadline policy (SF-03, resolved by documentation)

The review asked for the `sleep t deadline` policy on `deadline < now` to
be explicit. Decision: **past deadlines are legal**; the task wakes at the
next valid tick (any tick time `≥ now` satisfies an expired deadline).
This keeps `sleep` total over deadlines and concentrates all time
reasoning in `tick`'s monotone guard. Rejection (`invalid`) and
normalization (`deadline := now`) were considered; both add a guard and
proof churn without strengthening any current theorem. The policy is now
stated in the `RuntimeOp.sleep` docstring. Revisit if fairness or
wall-clock refinement work needs a different policy.

## Acceptance criteria

- [x] Empty own-mailbox receive is not conflated with invalid operation
      (demo checks: `.blocked` vs `.invalid` distinguished live).
- [x] Non-running/unowned receive remains invalid.
- [x] `step_blocked_unchanged` kernel-checked, audit-allowlisted.
- [x] Sleep deadline policy explicit in the operation grammar docs.
