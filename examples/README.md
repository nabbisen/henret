# Henret Examples

Sixteen self-contained examples, one concept each. The count and numbered-file
inventory are checked directly from `examples/[0-9][0-9]_*.lean`.
Run any file with:

```bash
lake env lean examples/NN_name.lean
```

| # | File | Concept | Key theorem(s) |
|---|---|---|---|
| 01 | `01_task_lifecycle.lean` | The task lifecycle state machine | `step_preserves_completed` |
| 02 | `02_actor_mailbox.lean` | Actor identity and mailbox ownership | `send_preserves_other` |
| 03 | `03_spawn_and_schedule.lean` | Ready queue and `schedule` | — |
| 04 | `04_send_receive.lean` | Message send/receive, blocked-receive parking (RFC 031) | `receive_consumes_one`, `receive_empty_parks`, `receive_blocked_parks` |
| 05 | `05_sleep_and_tick.lean` | Logical timers, sleep, tick | `tick_no_early_wake`, `tick_wakes_expired` |
| 06 | `06_cancel_task.lean` | `cancelled` is terminal | `step_preserves_cancelled`, `run_preserves_cancelled` |
| 07 | `07_refinement_contract.lean` | The `MailboxBackend` contract pattern | `listBackend`, `mailboxBackend` |
| 08 | `08_proof_trust_test_matrix.lean` | PROVEN / ASSUMED / TESTED / OUTSCOPE | matrix, `#print axioms` |
| 09 | `09_optional_ffi_boundary.lean` | Optional native backend boundary (RFC 010) | — |
| 10 | `10_integration_contract.lean` | External-consumer integration contract (RFC 044) | `run_preserves_wf` |
| 11 | `11_trace_ledger.lean` | Execution trace ledger (RFC 045) | `runTraceLedger_state_eq_run` |
| 12 | `12_supervision_restart.lean` | Failure and supervision restart (RFC 049) | `reachable_restart_fresh` |
| 13 | `13_trace_rendering.lean` | Human-readable trace rendering (RFC 050) | — |
| 14 | `14_state_diagrams.lean` | State and bridge diagram rendering (RFC 050) | — |
| 15 | `15_semantic_profiles.lean` | Semantic capability profiles (RFC 054) | `core_le_actor`, `actor_le_full` |
| 16 | `16_structured_shutdown.lean` | Structured cancellation and shutdown (RFC 055) | `shutdown_rejects_spawn` |

## What to read before the examples

The [`docs/src/guided-tour.md`](../docs/src/guided-tour.md) gives context for
each step. The full theorem inventory is in
[`docs/src/proof-index.md`](../docs/src/proof-index.md), and claim
classifications are in
[`docs/src/proof-trust-test-matrix.md`](../docs/src/proof-trust-test-matrix.md).
