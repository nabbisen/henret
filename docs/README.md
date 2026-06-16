# Henret Documentation

Executable actor/task runtime models for Lean 4 — a verified
execution-semantics kernel, not a runtime library. Start here and follow
the path that matches you.

## New users

- [Quickstart](../README.md#quickstart) — build and run the demo.
- [Guided tour](guided-tour.md) — a developer walkthrough of the model.
- [Trace ledger](trace-ledger.md) — first-class execution traces (RFC 045).
- [Observability](observability.md) — render states, traces, and
  actor/task relations (RFC 050).

## Intermediate users (API / specifications)

- [Proof index](proof-index.md) — every public theorem with its file
  location.
- [Proof / trust / test matrix](proof-trust-test-matrix.md) — every
  correctness claim, classified PROVEN / ASSUMED / TESTED / OUTSCOPE.
- [Fault & outcome taxonomy](fault-taxonomy.md) — the precise vocabulary for
- [Scheduling policy layer](scheduling-policy.md) — policy-parametric
  scheduling (FIFO/LIFO) that preserves the core safety invariant.
  invalidity, waiting, cancellation, timeout, and the reserved fault classes.
- [Assumption index](assumption-index.md) — the complete axiom budget.
- [Conformance suite](conformance-suite.md) — golden-trace conformance
  (RFC 047).
- [Progress policy](progress-policy.md) — conditional liveness / fairness
  (RFC 046).
- [Supervision restart](supervision-restart.md) — failure and one-for-one
  restart (RFC 049).
- [Shutdown semantics](shutdown-semantics.md) — actor closing, runtime
  shutdown, quiescence (RFC 055, safety-only).
- [Profile index](profile-index.md) — semantic profiles (core / actor /
  full) and the theorem-to-profile mapping (RFC 054).

## Maintainers / contributors

- [Project positioning](project-positioning.md) — what Henret is and is
  not.
- [Assurance case](assurance-case.md) — the reviewer's entry point: every
  top-level claim, its evidence, and known limits.
- [Review playbook](review-playbook.md) — the external reviewer's
  checklist.
- [Risk register](risk-register.md) — known residual risks and their
  mitigations.
- [Semantic extension governance](semantic-extension-governance.md) — the
  Semantic Impact Checklist and bridge-claim rule.
- [Naming and scope](naming-and-scope.md) — module and identifier scope.
- [Theorem naming style](theorem-naming.md) — naming conventions for new
  theorems.
- [Proof engineering](proof-engineering.md) — hard-won tactic facts and
  patterns.
- [Bridge architecture](bridge-architecture.md) — the lean-runtime bridge
  (RFC 035/036).
- [Native backend boundary](native-backend-boundary.md) — the C FFI trust
  boundary.
- [Model explorer](model-explorer.md) — the bounded model checker
  (RFC 048).
- [Release policy](release-policy.md) — versioning and changelog policy.
- [Release checklist](release-checklist.md) — the gates that must pass
  before an archive is cut.
- [Migration notes](migration/) — grammar-change migration guides.
- [Roadmap](roadmap.md) — the RFC queue and direction.

## Import tiers

```lean
import Henret.Model       -- executable model (step / run)
import Henret.Proofs      -- all proof modules
import Henret.Refinement  -- backend contracts
import Henret.Bridge      -- lean-runtime bridge
import Henret.Trace       -- trace / event layer (RFC 045)
import Henret             -- full public barrel (Model + Proofs +
                          --   Refinement + Bridge + Trace + Conformance +
                          --   Progress + Render)
```

Optional, opt-in (outside the default barrel):

```lean
import Henret.Native.DequeModel   -- C FFI trust layer (RFC 010)
-- HenretExplore lean_lib            bounded model checker (RFC 048)
```

Examples under `examples/` are standalone and never imported by the
package.
