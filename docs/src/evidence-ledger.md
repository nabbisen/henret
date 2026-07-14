# Evidence Ledger

<!-- GENERATED from docs/evidence-ledger.yaml by scripts/forbidden_claim_check.py. Do not edit by hand (RFC 081). -->

Each claim records its assurance tier and *where* its evidence lives. The model-package tarball verifies only `in_tree_*` claims; `sibling_runtime_package` claims live in the separately versioned runtime package and are **not** verified by this tarball (see [`package-boundary.md`](package-boundary.md)).

| claim_id | tier | location | verified here | CI binding | claim |
|---|---|---|:---:|---|---|
| `model.reachable_wf` | PROVEN | in_tree_model_proof | yes | `release-core-v4 / build.lean` | Every reachable scheduler state satisfies the 33-field WellFormed invariant |
| `model.occurrence_unique` | PROVEN | in_tree_model_proof | yes | `release-core-v4 / build.lean` | Equal message occurrence ids across any two reachable mailboxes imply the same envelope in the same mailbox |
| `model.parent_acyclic` | PROVEN | in_tree_model_proof | yes | `release-core-v4 / build.lean` | Parent chains are strictly decreasing and therefore terminate |
| `model.owner_exactness` | PROVEN | in_tree_model_proof | yes | `release-core-v4 / build.lean` | Every spawned task has an immutable owner and every owned task is spawned |
| `model.bridge_single_worker` | PROVEN | in_tree_model_proof | yes | `release-core-v4 / build.lean` | The single-worker queue projection is preserved by every RuntimeOp |
| `model.bridge_multi` | PROVEN | in_tree_model_proof | yes | `release-core-v4 / build.lean` | Every reachable state admits a multi-worker BridgeState witness |
| `model.profile_chain` | PROVEN | in_tree_model_proof | yes | `release-core-v4 / build.lean` | The semantic profiles form an inclusion chain core <= actor <= full |
| `model.restart_safety` | PROVEN | in_tree_model_proof | yes | `release-core-v4 / build.lean` | Supervision restart preserves parent acyclicity and owner consistency |
| `model.shutdown_safety` | PROVEN | in_tree_model_proof | yes | `release-core-v4 / build.lean` | Closed actors reject send/inject and a shutdown runtime rejects spawn |
| `model.fairness_liveness` | PROVEN | in_tree_model_proof | yes | `release-core-v4 / build.lean` | Under bounded fairness every ready task is eventually scheduled |
| `model.trace_sound` | PROVEN | in_tree_model_proof | yes | `release-core-v4 / build.lean` | The execution-trace ledger reproduces step state and result exactly |
| `native.deque_axioms` | TRUSTED | in_tree_model_proof | yes | `release-core-v4 / proof.axiom-audit` | The Chase-Lev deque satisfies its six sequential-specification axioms |
| `native.race_freedom` | OUTSCOPE | planned | no | — | C11-atomic data-race freedom and RC discipline of the native deque |
| `test.demo_scenarios` | TESTED | in_tree_model_test | yes | `release-core-v4 / test.demo` | The demo regression scenarios run to the expected outcomes |
| `test.conformance` | TESTED | in_tree_model_test | yes | `release-core-v4 / test.conformance` | The golden-trace conformance suite passes and reports first mismatch on failure |
| `test.explorer` | TESTED | in_tree_model_test | yes | `release-core-v4 / test.explorer` | The bounded model checker enumerates op sequences and shrinks counterexamples |
| `runtime.differential` | TESTED | sibling_runtime_package | no | — | The concrete machine matches the pure model on identical op sequences |
| `runtime.linearizability` | TESTED | sibling_runtime_package | no | — | Concurrent histories pass the Wing-Gong linearizability checker |
| `runtime.stress_partition` | TESTED | sibling_runtime_package | no | — | Stress rounds preserve the partition invariant pushed = popped + stolen |
| `runtime.executor` | TESTED | sibling_runtime_package | no | — | Cooperative executor futures run to completion in the expected order |

