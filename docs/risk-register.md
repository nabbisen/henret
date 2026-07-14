# Residual Risk Register

Known residual risks in Henret, each with its current mitigation and
status. Reviewed at every release (see the sign-off template in
[`docs/src/assurance-case.md`](src/assurance-case.md) §10). Risks are not
defects — they are honestly-acknowledged limits and pressures.

| ID | Risk | Likelihood | Impact | Mitigation | Status |
|---|---|---|---|---|---|
| R1 | **Proof-maintenance cost as `WellFormed` grows.** Each new field multiplies preservation obligations across operations. | Medium | Medium | Reduction lemmas (e.g. `WellFormed.restartOf_irrel`) and separate invariant structures (`RestartWellFormed`) keep the base contract bounded; preservation files are split by operation family. | Managed |
| R2 | **Bridge incompleteness.** The bridge is a single-worker projection; multi-worker scheduling is not simulated. | High (by design) | Low | The single-worker qualifier is mandatory in all bridge claims (RFC 052 rule, gated); `MultiBridgeState` is explicit groundwork, not a claim. | Accepted / scoped |
| R3 | **Native C concurrency outside Lean's logic.** C11-atomic data-race freedom of the Chase-Lev deque is trusted, not proven. | Known | High if false | Confined to opt-in `import Henret.Native.*`; sequential spec is axiom-budgeted; concurrent behavior is covered by differential/linearizability/stress harnesses (TESTED, not PROVEN). | Accepted / trusted |
| R4 | **Future liveness claims needing policy assumptions.** Unconditional liveness is not provable for a cooperative scheduler. | Medium | Medium | Only *conditional* progress is claimed (`ready_eventually_scheduled_under_bounded_fairness`), with the fairness assumption explicit; the FIFO `readyQ` makes `schedule_schedules_head` unconditionally true. | Managed |
| R5 | **Over-strict trace equality for multi-worker runtimes.** Conformance uses exact trace equality, which a multi-worker runtime's interleavings may not satisfy. | Medium (future) | Medium | Conformance is single-worker / deterministic today; a membership- or permutation-based refinement is the planned relaxation when multi-worker lands. | Watch |
| R6 | **Doc/claim drift.** Docs lagging grammar or theorem changes (historically recurrent). | Medium | Low–Medium | Existing stale-phrase, symbol, count, and generated-doc gates missed live roadmap/index contradictions in the v0.34.5 review. RFC 101 adds generated root indexing, repository-link coverage, and regression fixtures. | Open — release-blocking |
| R7 | **Sandbox/CI demo-codegen cost.** The `henret-demo` executable's C code generation is memory-heavy and can dominate a constrained runner. | Low | Low | Documented in the release checklist; the library proofs and conformance executable verify independently of the demo's codegen. | Documented |
| R8 | **GitHub-hosted runner base is mutable.** Hashing Actions and downloaded tools does not pin the kernel, image packages, Python, Git, TLS roots, Actions service, or runner-provided `gh`. | Medium | High if compromised | RFC 104 records exact hosted run/workflow/commit plus runner image identity, accepts only hosted-CI v4 evidence, and requires runner-image changes to be reviewed before publication. These fields identify the base TCB; they do not reproduce it. | Managed / release-disclosed |

## How to use this register

When a release introduces a new pressure or limit, add a row rather than
silently absorbing it. When a risk is fully retired (e.g. multi-worker
bridge proven), move its row to a "Retired risks" section with the
release that closed it — do not delete it, so the history of what was
once at risk is preserved.

## Retired risks

*(none yet)*
