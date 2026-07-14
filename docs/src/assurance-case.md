# Henret Assurance Case

A structured argument connecting Henret's claims to their evidence,
assumptions, tests, and exclusions. It is the entry point for an external
reviewer — an architect, formal-methods engineer, or runtime implementer.

This document **links** to the proof index, the proof/trust/test matrix,
and the assumption index rather than copying them; those remain the
authoritative tables.

## 1. System scope

Henret is a pure-Lean 4 *semantic reference* for an actor/task scheduler:
spawn, schedule, yield, send, receive, inject, sleep, tick, wake, cancel,
complete, fail, and restart, modeled as total executable state
transitions (`step` / `run`). It is **not** a runtime library, and it
does not verify C-level concurrency. See
[`docs/project-positioning.md`](project-positioning.md).

The assurance boundary has three layers, never conflated:

- **Kernel-proven** — Lean 4 proofs, zero `sorry`, no project axioms.
- **Trusted** — named axioms at the C FFI boundary.
- **Tested** — harnesses giving empirical confidence, not proof.

## 2. Claim hierarchy

**Top-level claim.** *Henret is a kernel-checked semantic reference for
actor/task scheduler states: every transition is executable, every safety
claim is named, and every trust boundary is explicit.*

The top-level claim decomposes into the subclaims below. Each links to
its headline theorem, file, class, and caveats.

## 3. Kernel-proven claims

| ID | Claim | Headline theorem | File | Axioms |
|---|---|---|---|---|
| C1 | Reachable states satisfy the 33-field `WellFormed` invariant | `reachable_wf` | `Henret/Proofs/InvariantsPreservation.lean` | STD+choice |
| C2 | Message occurrence ids are globally unique in reachable states | `reachable_occurrence_unique` | `Henret/Proofs/Occurrence.lean` | STD+choice |
| C3 | Parent chains are acyclic (strictly decreasing) in reachable states | `reachable_parent_lt`, `parent_chain_terminates` | `Henret/Proofs/Parenthood.lean` | STD+choice |
| C4 | Actor-local receive touches only the owning actor's mailbox | `receive_only_own` | `Henret/Proofs/Messaging.lean` | STD+choice |
| C5 | The bridge relation holds for every operation under the **single-worker** projection | `bridge_step_single_worker` | `Henret/Bridge/Preservation.lean` | STD+choice |
| C7 | Supervision restart is well-formed: replacement id is fresh, the replaced task is failed, parent is shared, acyclicity preserved | `reachable_restart_fresh`, `reachable_restart_old_failed`, `reachable_restart_parent_consistent`, `restart_preserves_parent_acyclicity`, `restarted_task_has_owner` | `Henret/Proofs/Restart.lean` | STD+choice |
| C9 | The trace ledger is sound: each event corresponds to the transition that produced it, and the traced run tracks `run` | `event_*_sound`, `runTraceLedger_state_eq_run` | `Henret/Trace/Theorems.lean` | STD(+choice) |

"STD" = `propext`, `Quot.sound`; "+choice" adds `Classical.choice`
(present in reachability theorems via `by_cases`/`obtain`). The full
per-theorem axiom set is verified by `scripts/axiom_audit.py` (gate 7 of
`scripts/check.sh`) against the allowlist. No project-specific axiom
appears anywhere in `import Henret`.

For the complete theorem list see
[`docs/proof-index.md`](proof-index.md) and its
[stability classification](proof-index.md#theorem-stability); for every
claim's class see [`docs/proof-trust-test-matrix.md`](proof-trust-test-matrix.md).

## 4. Trusted assumptions

| ID | Claim | Evidence | What is trusted |
|---|---|---|---|
| C6 | The native Chase-Lev deque meets its sequential specification | 6 axioms in `Henret/Native/Assumptions.lean`; 4 in the lean-runtime `FFISpec.lean` | sequential push/steal/pop/snapshot behavior of the C implementation |

These axioms are **opt-in**: they enter the budget only via
`import Henret.Native.*`, never through the default `import Henret`. They
trust the C implementation on the *sequential-specification* axis only.
See [`docs/assumption-index.md`](assumption-index.md) and
[`docs/native-backend-boundary.md`](native-backend-boundary.md).

## 5. Tested claims

| ID | Claim | Harness | Status |
|---|---|---|---|
| C8 | Observable behavior matches the golden traces | `lake exe henret-conformance` (`conformance_suite_passes`, kernel `decide`) | 10/10 scenarios pass |
| C10 | A ready task is eventually scheduled *under bounded fairness* | `ready_eventually_scheduled_under_bounded_fairness` (conditional theorem) + witnesses | proven conditional on an explicit fairness assumption |
| T1 | The concrete machine tracks the pure model under concurrent scheduling | lean-runtime differential / linearizability / stress harness | empirical confidence, not a proof |

Note that C8's conformance check is itself kernel-`decide`d, and C10 is a
genuine theorem *conditioned* on a stated assumption — neither is an
unconditional liveness claim. See
[`docs/conformance-suite.md`](conformance-suite.md) and
[`docs/progress-policy.md`](progress-policy.md).

## 6. Out-of-scope claims

Henret does **not** claim, and its proofs do not cover:

- C11-atomic data-race freedom of the C deque (requires concurrent
  separation logic; outside Lean's reach here);
- multi-worker scheduling correctness (the bridge is single-worker;
  `MultiBridgeState` is groundwork, not a multi-worker simulation proof);
- unconditional liveness or fairness (only conditional progress is
  claimed);
- per-message delivery guarantees beyond Mesa wake semantics;
- performance, real-time, or memory behavior.

## 7. Evidence map

```
Top-level claim
├── C1 reachable_wf ─────────────── Proofs/InvariantsPreservation.lean
├── C2 reachable_occurrence_unique ─ Proofs/Occurrence.lean
├── C3 reachable_parent_lt ───────── Proofs/Parenthood.lean
├── C4 receive_only_own ──────────── Proofs/Messaging.lean
├── C5 bridge_step_single_worker ─── Bridge/Preservation.lean   [single-worker]
├── C6 native axioms ─────────────── Native/Assumptions.lean     [TRUSTED, opt-in]
├── C7 reachable_restart_* ───────── Proofs/Restart.lean
├── C8 conformance_suite_passes ──── Conformance/Golden.lean     [TESTED, decide]
├── C9 event_*_sound ─────────────── Trace/Theorems.lean
└── C10 ready_eventually_scheduled ─ Progress/Policy.lean        [CONDITIONAL]
```

## 8. Review checklist

See [`docs/review-playbook.md`](review-playbook.md) for the external
reviewer's checklist.

## 9. Known residual risks

See [`docs/risk-register.md`](../risk-register.md).

## 10. Release sign-off template

Copy into the release PR / notes:

```text
Henret vX.Y.Z assurance sign-off
- [ ] scripts/check.sh green (build, demo, examples, conformance,
      axiom audit, stale-phrase, doc-symbol)
- [ ] zero sorry in Henret/
- [ ] axiom budget unchanged (import Henret: propext, Classical.choice,
      Quot.sound only); any new headline theorem added to the audit
      allowlist
- [ ] proof/trust/test matrix updated; new claims classified
- [ ] no kernel-proven claim presented as merely tested, and vice versa
- [ ] bridge claims qualified "single-worker" (RFC 052 rule)
- [ ] migration note present if grammar changed
- [ ] assurance case C-table updated if a top-level claim was added
- [ ] risk register reviewed; new residual risks recorded
Signed-off-by: <name>
```
