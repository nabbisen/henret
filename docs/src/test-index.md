# Test Index

Executable evidence lives in `lake exe henret-demo` (`Main.lean`). The demo
exits non-zero if any check fails, so it doubles as a regression gate.

Ten scenarios; exit 0 means all passed. The count is checked against the
numbered scenario declarations in `Main.lean`.

| Scenario | Checks | Backing proofs |
|---|---|---|
| 1. Task lifecycle | spawn → schedule → yield → schedule → complete leaves task 0 `completed`; ready queue empty | `step_preserves_completed` |
| 2. Mailbox | running task 0 (actor 7) sends twice to its own actor and receives once; receive returns message 1; mailbox then holds exactly message 2 | `receive_consumes_one`, `send_appends`, `receive_only_own` |
| 3. Sleep/tick | at t=7, deadline-10 task still sleeping; deadline-5 task woken | `tick_no_early_wake`, `tick_wakes_expired` |
| 4. Cancel | cancelled task stays cancelled and is not re-queued | `step_preserves_cancelled` |
| 5. Drivers | `driveOps` (TESTED) and `drain` (PROVEN: `drain_completes`) complete tasks 0..4 |  |
| 6. v0.2 model | ownership set at spawn and stable across the lifecycle; clock advances; backwards tick is rejected and is a no-op; tick on an *arbitrary* state with a stale (cancelled-task) timer entry consumes the entry, wakes nothing (`.woke []`), re-queues nothing; cancel drops pending timers in reachable states | `reachable_spawned_has_owner`, `tick_advances_clock`, `tick_backwards_invalid`, `step_invalid_unchanged`, `WellFormed.timers_sleep` |
| 7. Park → deliver → wake → re-receive → consume (RFC 031) | empty own-mailbox receive parks the task (`.waiting`, running cleared, queued in `mailboxWaiters`); inject wakes head waiter; woken task re-issues receive and consumes the message (Mesa semantics) | `receive_empty_parks`, `receive_blocked_parks`, `receive_unowned_invalid` |
| 8. spawnChild parent chain (RFC 032) | running task 0 spawns child task 1; child records task 0 as parent; task 0 completes; child still queued as `.new` | `spawnChild_sets_parent`, `spawnChild_queues_child`, `reachable_parent_lt` |
| 9. Bridge queue projection (RFC 036) | the single-worker queue-operation trace produces the same final queue as semantic `readyQ`; other worker queues remain empty | `bridge_run_tracks_single_worker` |
| 10. Cascade cancel (RFC 039) | cancelling a root cancels its descendant, preserves an unrelated task, and removes cancelled tasks from `readyQ` | `cancelTree_cancels_task`, `cancelTree_preserves_task_state`, `preserves_wf_cancelTree` |

Where a behavior is also proven, the test is a sanity check on the executable
semantics; where it is not (e.g. `driveOps`), the test is the primary evidence
and the matrix classifies the claim as TESTED.
