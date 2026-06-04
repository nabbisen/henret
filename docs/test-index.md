# Test Index

Executable evidence lives in `lake exe henret-demo` (`Main.lean`). The demo
exits non-zero if any check fails, so it doubles as a regression gate.

| Scenario | Checks | Backing proofs |
|---|---|---|
| 1. Task lifecycle | spawn → schedule → yield → schedule → complete leaves task 0 `completed`; ready queue empty | `step_preserves_completed` |
| 2. Mailbox | running task 0 (actor 7) sends twice to its own actor and receives once; receive returns message 1; mailbox then holds exactly message 2 | `receive_consumes_one`, `send_appends`, `receive_only_own` |
| 3. Sleep/tick | at t=7, deadline-10 task still sleeping; deadline-5 task woken | `tick_no_early_wake`, `tick_wakes_expired` |
| 4. Cancel | cancelled task stays cancelled and is not re-queued | `step_preserves_cancelled` |
| 5. Drivers | `driveOps` (TESTED) and `drain` (PROVEN: `drain_completes`) complete tasks 0..4 |  |
| 6. v0.2 model | ownership set at spawn and stable across the lifecycle; clock advances; backwards tick is rejected and is a no-op; tick on an *arbitrary* state with a stale (cancelled-task) timer entry consumes the entry, wakes nothing (`.woke []`), re-queues nothing; cancel drops pending timers in reachable states | `spawn_sets_owner`, `run_preserves_owner`, `tick_advances_clock`, `tick_backwards_invalid`, `step_invalid_unchanged`, `WellFormed.timers_sleep` |
| 7. Blocked vs invalid (RFC 029) | empty own-mailbox receive by the running task is `blocked` and changes nothing; receive by a non-running task is `invalid`, not blocked | `receive_empty_blocked`, `step_blocked_unchanged`, `receive_unowned_invalid` |

Where a behavior is also proven, the test is a sanity check on the executable
semantics; where it is not (e.g. `driveOps`), the test is the primary evidence
and the matrix classifies the claim as TESTED.
