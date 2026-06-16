# Henret RFC Index

Lifecycle policy: see [`000-rfc-lifecycle-policy.md`](done/000-rfc-lifecycle-policy.md).
New RFCs start from [`TEMPLATE.md`](TEMPLATE.md). Semantic-core changes
follow [`docs/semantic-extension-governance.md`](../docs/semantic-extension-governance.md).

## Done

| RFC | Title | Shipped |
|---|---|---|
| [000](done/000-rfc-lifecycle-policy.md) | RFC Lifecycle Policy | v0.1.0 |
| [001](done/001-project-positioning-and-scope.md) | Project Positioning and Scope | v0.1.0 |
| [002](done/002-package-identity-and-naming.md) | Package Identity and Naming | v0.1.0 |
| [003](done/003-lean-only-core-package.md) | Lean-Only Core Package | v0.1.0 |
| [004](done/004-actor-task-model-core.md) | Actor/Task Model Core | v0.1.0 |
| [005](done/005-scheduler-semantics-model.md) | Scheduler Semantics Model | v0.1.0 |
| [006](done/006-message-and-wake-semantics.md) | Message and Wake Semantics | v0.1.0 |
| [007](done/007-timer-and-sleep-semantics.md) | Timer and Sleep Semantics | v0.1.0 |
| [008](done/008-refinement-patterns.md) | Refinement Patterns | v0.1.0 |
| [009](done/009-proof-trust-test-matrix.md) | Proof/Trust/Test Matrix | v0.1.0 |
| [010](done/010-optional-ffi-backend-boundary.md) | Optional FFI Backend Boundary | v0.1.0 |
| [011](done/011-examples-and-guided-tour.md) | Examples and Guided Tour | v0.1.0 |
| [012](done/012-release-docsite-and-community.md) | Release, Docsite, and Community | v0.1.0 |
| [013](done/013-runtime-invariants-and-reachability.md) | Runtime Invariants and Reachability | v0.2.0 |
| [014](done/014-actor-ownership-model.md) | Actor Ownership Model | v0.2.0 |
| [015](done/015-logical-time-state.md) | Logical Time State | v0.2.0 |
| [016](done/016-invalid-operation-theorem.md) | Invalid Operation Theorem | v0.2.0 |
| [017](done/017-release-gate-and-ci.md) | Release Gate and CI | v0.2.0 |
| [018](done/018-documentation-consistency-sweep.md) | Documentation Consistency Sweep | v0.2.0 |
| [019](done/019-strengthened-wellformed-invariant.md) | Strengthened WellFormed Invariant | v0.2.1 |
| [020](done/020-strict-axiom-audit-gate.md) | Strict Axiom Audit Gate | v0.2.1 |
| [021](done/021-documentation-test-index-repair.md) | Documentation/Test Index Repair | v0.2.1 |
| [022](done/022-message-occurrence-semantics.md) | Message Occurrence Semantics | v0.2.1 |
| [023](done/023-deque-driver-orientation-cleanup.md) | Deque Driver Orientation Cleanup | v0.2.1 |
| [024](done/024-actor-scoped-operations.md) | Actor-Scoped Operations | v0.3.0 |
| [025](done/025-import-granularity.md) | Import Granularity | v0.3.0 |
| [026](done/026-documentation-and-public-claim-repair.md) | Documentation and Public Claim Repair | v0.3.1 |
| [027](done/027-model-import-boundary-clarification.md) | Model Import Boundary Clarification | v0.3.1 |
| [028](done/028-schedulable-completeness-invariant.md) | Schedulable Completeness Invariant | v0.4.0 |
| [029](done/029-blocked-receive-semantics.md) | Blocked Receive Semantics | v0.4.0 |
| [030](done/030-v041-public-claim-cleanup.md) | v0.4.1 Public Claim Cleanup | v0.4.1 |
| [034](done/034-preservation-proof-modularity.md) | Preservation-Proof Modularity | v0.5.0 |
| [031](done/031-blocked-waiting-state.md) | Blocked Waiting State and Mailbox Wait Queue | v0.5.0/v0.5.1 |
| [032](done/032-actor-scoped-spawn-supervision-groundwork.md) | Actor-Scoped Spawn and Supervision Groundwork | v0.6.0 |
| [033](done/033-message-envelope-occurrence-identity.md) | Message Envelope and Occurrence Identity | v0.7.0 |
| [035](done/035-lean-runtime-bridge.md) | Single-Worker Lean-Runtime Bridge Skeleton | v0.8.0 |
| [036](done/036-single-worker-bridge-completion.md) | Bridge Claim Repair and Single-Worker Bridge Completion | v0.9.0 |
| [037](done/037-v081-public-claim-repair.md) | Public Claim Repair (v0.9.0) | v0.9.0 |
| [038](done/038-parent-owner-exactness.md) | Parent and Owner Exactness Invariants | v0.9.1 |
| [039](done/039-supervision-cascade-cancel.md) | Supervision Semantics: Cascade Cancel | v0.10.0 |

## Archive

| RFC | Title | Reason |
|---|---|---|
| [042](archive/042-preservation-proof-automation.md) | Preservation Proof Automation | Superseded by RFC 082 |

## Proposed

| RFC | Title | Target | Priority |
|---|---|---|---|
| [040](done/040-receive-timeout-multi-wait.md) | Receive Timeout and Multi-Wait Semantics | Implemented (v0.11.0) | — |
| [041](done/041-selective-receive.md) | Selective Receive | Implemented (v0.11.1) | — |

| [043](done/043-multi-worker-bridge-extension.md) | Multi-Worker Bridge Model Extension | Implemented (v0.12.0) | — |
| [044](done/044-runtime-integration-contract.md) | Runtime Integration Contract for External Consumers | Implemented (v0.12.1) | — |
| [045](done/045-execution-trace-ledger.md) | Execution Trace Ledger | Implemented (v0.13.0) | — |
| [046](done/046-fairness-liveness-policy-layer.md) | Fairness and Conditional Liveness Layer | Implemented (v0.14.0) | — |
| [047](done/047-golden-trace-conformance-suite.md) | Golden Trace Conformance Suite | Implemented (v0.13.1) | — |
| [048](done/048-bounded-model-explorer.md) | Bounded Model Explorer and Shrinker | Implemented (v0.14.1) | — |
| [049](done/049-supervision-restart-policies.md) | Supervision Restart Policies | Implemented (v0.15.0) | — |
| [050](done/050-observability-and-pedagogical-visualization.md) | Observability and Pedagogical Visualization | Implemented (v0.15.1) | — |
| [051](done/051-package-documentation-release-maturity.md) | Package, Documentation, and Release Maturity | Implemented (v0.15.2) | — |
| [052](done/052-semantic-extension-governance.md) | Semantic Extension Governance | Implemented (v0.15.3) | — |
| [053](done/053-assurance-case-and-external-review-playbook.md) | Assurance Case and External Review Playbook | Implemented (v0.15.4) | — |
| [054](done/054-semantic-profiles-and-capability-sets.md) | Semantic Profiles and Capability Sets | Implemented (v0.16.0) | — |
| [055](done/055-structured-cancellation-and-shutdown.md) | Structured Cancellation and Shutdown | Implemented (v0.17.0) | — |
| [056](done/056-bounded-mailboxes-and-backpressure.md) | Bounded Mailboxes and Backpressure | Implemented (v0.18.0) | — |
| [057](proposed/057-resource-lifetime-and-finalization-ledger.md) | Resource Lifetime and Finalization Ledger | — | — |
| [058](proposed/058-scheduling-policy-layer.md) | Scheduling Policy Layer | — | — |
| [059](proposed/059-deadline-and-priority-semantics.md) | Deadline and Priority Semantics | — | — |
| [060](proposed/060-trace-based-refinement-certification.md) | Trace-Based Refinement Certification | — | — |
| [061](proposed/061-runtime-adapter-contract.md) | Runtime Adapter Contract | — | — |
| [062](proposed/062-proof-ergonomics-library.md) | Proof Ergonomics Library | — | — |
| [063](proposed/063-long-term-module-architecture.md) | Long-Term Module Architecture | — | — |
| [064](proposed/064-fault-model-and-failure-taxonomy.md) | Fault Model and Failure Taxonomy | — | — |
| [065](proposed/065-semantic-equivalence-and-bisimulation.md) | Semantic Equivalence and Bisimulation | — | — |
| [066](proposed/066-deterministic-replay-format.md) | Deterministic Replay Format | — | — |
| [067](proposed/067-state-snapshot-and-semantic-diff.md) | State Snapshot and Semantic Diff | — | — |
| [068](proposed/068-invariant-dependency-graph.md) | Invariant Dependency Graph | — | — |
| [069](proposed/069-proof-dependency-budget.md) | Proof Dependency Budget | — | — |
| [070](proposed/070-public-theorem-api-stability.md) | Public Theorem API Stability | — | — |
| [071](proposed/071-semantic-profiles-for-actor-models.md) | Semantic Profiles for Actor Models | — | — |
| [072](proposed/072-error-and-result-observability-contract.md) | Error and Result Observability Contract | — | — |
| [073](proposed/073-runtime-adapter-negative-tests.md) | Runtime Adapter Negative Tests | — | — |
| [074](proposed/074-bridge-completeness-certificate.md) | Bridge Completeness Certificate | — | — |
| [075](done/075-model-to-documentation-extraction.md) | Model-to-Documentation Extraction | Implemented (v0.17.7) | — |
| [076](proposed/076-counterexample-catalog.md) | Counterexample Catalog | — | — |
| [077](proposed/077-minimal-verified-actor-patterns.md) | Minimal Verified Actor Patterns | — | — |
| [078](proposed/078-security-and-robustness-interpretation.md) | Security and Robustness Interpretation | — | — |
| [079](proposed/079-publication-and-community-review-plan.md) | Publication and Community Review Plan | — | — |
| [080](done/080-release-gate-integrity-and-evidence-manifest.md) | Release Gate Integrity and Evidence Manifest | Implemented (v0.17.2) | — |
| [081](done/081-package-boundary-and-evidence-ledger.md) | Package Boundary and Evidence Ledger | Implemented (v0.17.3) | — |
| [082](done/082-preservation-proof-ergonomics-v2.md) | Preservation Proof Ergonomics v2 (supersedes 042) | Implemented (v0.17.6) | — |
| [083](done/083-golden-conformance-coverage-expansion.md) | Golden Conformance Coverage Expansion | Implemented (v0.17.5) | — |
| [084](done/084-model-to-documentation-extraction-implementation.md) | Model-to-Documentation Extraction Implementation | Implemented (v0.17.7) | — |
| [085](done/085-rfc-metadata-normalization.md) | RFC Metadata Normalization | Implemented (v0.17.1) | — |
| [086](done/086-warning-hygiene-and-public-lemma-tightening.md) | Warning Hygiene and Public Lemma Tightening | Implemented (v0.17.4) | — |

## Archive

(empty)

---

*Shipped: 001–012 in v0.1.0; 013–018 in v0.2.0; 019–023 in v0.2.1; 024–025 in v0.3.0;
026–027 in v0.3.1; 028–029 in v0.4.0; 030 in v0.4.1; 034 in v0.5.0; 031 core in v0.5.0,
acceptance criteria in v0.5.1; 033 in v0.7.0; 035 skeleton in v0.8.0;
036 + 037 in v0.9.0; 038 in v0.9.1; 039 in v0.10.0; 042 in v0.10.1.*
