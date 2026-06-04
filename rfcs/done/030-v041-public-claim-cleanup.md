---
title: v0.4.1 Public Claim Cleanup
rfc: RFC-HENRET-030
status: Implemented (v0.4.1)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-030: v0.4.1 Public Claim Cleanup

## Motivation

The v0.4.0 review approved the core semantics of RFC 028–029 ("the most
important achievement is `reachable_queue_exact`") and required a short
documentation pass before public tagging: five claim drifts (RB-01..05)
and four should-fixes. As with RFC 026, these matter disproportionately
for a project whose identity is proof/trust/test accuracy.

## Changes

- **RB-01** — README "model in one minute" operation list now includes
  `inject` (eleven operations, matching the opening paragraph).
- **RB-02** — proof index: `step_preserves_terminal` described as the
  full case analysis over the eleven-operation grammar (was
  "10-operation").
- **RB-03** — proof index: `WellFormed` described by its current
  ten-field surface (soundness *and* completeness of the ready queue,
  running-slot consistency, timer discipline, fresh-id discipline,
  ownership and mailbox existence) instead of "six-field".
- **RB-04** — `Henret/Proofs.lean` barrel docstring made count-free
  ("the reachability invariant and its preservation theorem") per the
  reviewer's fragility note.
- **RB-05** — README proof summary gains the two v0.4.0 headline
  bullets: schedulable completeness and blocked receive semantics.
- **SF-01** — gate 6 current-surface phrases added: "10-operation",
  "six-field reachability", "nine-field reachability" (deliberately not
  overfit).
- **SF-02** — example 04 separates the two facts: the live `#eval`
  demonstrates the NON-RUNNING guard (task 1 is owned); the ownership
  guard is presented separately with a pointer to
  `reachable_spawned_has_owner` for why it is an arbitrary-state fact.
- **SF-03** — demo scenario 6 split: scenario 6 (ownership / clock /
  timer hardening) and scenario 7 (blocked vs invalid receive);
  `docs/test-index.md` and the README scenario count updated.
- **SF-04** — README and matrix row 47 frame `blocked` as transitional:
  a no-op *result*, not a waiting-state transition; wait queues are
  future work.

## Acceptance criteria

- [x] All five RB items fixed; seven gates green.
- [x] No "10-operation" / stale field-count phrases in live docs
      (gate-enforced).
- [x] Demo runs seven labeled scenarios; test index matches.
