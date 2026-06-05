# Henret Examples

Nine self-contained examples, one concept each.
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

## What to read before the examples

The `docs/guided-tour.md` gives context for each step.  The full theorem
inventory is in `docs/proof-index.md`.  The claim classifications are in
`docs/proof-trust-test-matrix.md`.
