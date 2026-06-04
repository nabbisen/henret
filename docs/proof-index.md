# Proof Index

All theorems are kernel-checked; none uses `sorry` or `native_decide`.
Axiom audit: only `propext` and `Quot.sound` (Lean standard).

## Core primitives — `Henret/Core/Id.lean`
- `upd_self`, `upd_ne` — the single map-update primitive behaves pointwise.

## Mailbox — `Henret/Actor/Mailbox.lean`
- `Mailbox.enqueue_messages` — enqueue appends at the tail.
- `Mailbox.dequeue_spec` — dequeue is exactly head removal.

## Task states — `Henret/Actor/Task.lean`
- `TaskState.isTerminal_completed`, `TaskState.isTerminal_cancelled`.

## Timer queue — `Henret/Scheduler/Timer.lean`
- `Timer.mem_insertSorted`, `Timer.insertSorted_sorted` — sorted insertion.
- `Timer.mem_expired`, `Timer.mem_remaining` — exact split by `now`.
- `Timer.sorted_filter`, `Timer.remaining_sorted` — sortedness closure.

## Scheduler model — `Henret/Scheduler/Model.lean`
- `run_nil`, `run_cons` — program execution unfolding.

## Lifecycle — `Henret/Proofs/Lifecycle.lean`
- `wakeOne_preserves_of_ne_sleeping`, `wakeMany_preserves_of_ne_sleeping`,
  `wakeOne_other`, `wakeMany_preserves_other`, `wakeMany_wakes` — wake helper laws.
- `step_preserves_terminal` — flagship: 10-operation case analysis.
- `step_preserves_completed`, `step_preserves_cancelled` — corollaries.
- `run_preserves_terminal`, `run_preserves_completed`, `run_preserves_cancelled`.
- `wake_exact`, `wake_sets_ready`, `wake_twice_invalid` — RFC 006 wake laws.

## Messaging — `Henret/Proofs/Messaging.lean`
- `send_appends`, `send_preserves_other`, `send_preserves_tasks`.
- `receive_consumes_one`, `receive_length`, `receive_preserves_other`,
  `receive_empty_invalid`, `receive_preserves_tasks`.

## Timers — `Henret/Proofs/Timers.lean`
- `tick_keeps_future`, `tick_no_early_wake`, `tick_wakes_expired`,
  `tick_enqueues_woken`, `step_preserves_sorted`, `run_preserves_sorted`.

## Drivers — `Henret/Scheduler/Driver.lean`
- `drain_empties`, `completeOne_completed`, `completeAll_preserves_completed`,
  `completeOne_drainable`, `completeAll_completes`, `drain_completes`.

## Refinement — `Henret/Refinement/*.lean`
- `MailboxBackend.dequeue_length` — derived from the contract laws.
- `listBackend`, `mailboxBackend` — reference backends; the contract laws
  (`toList_empty`, `toList_enqueue`, `toList_dequeue`) are proof fields.

## Native layer — `Henret/Native/DequeModel.lean`

All kernel-checked; no custom axioms.  `#print axioms` → only `propext`/`Quot.sound`.

- `stealHead`, `popLast` — FIFO and LIFO list dequeue helpers.
- `DequeModel` — abstract 6-law contract.
- `listDeque` — reference implementation; laws by `rfl`.
- `qStep_tracks` — one-step tracking lemma.
- `qRun_tracks` — whole-program refinement (PROVEN, `propext` only).
- `totalFuel_nil`, `totalFuel_cons`, `totalFuel_append_single` — fuel arithmetic.
- `drivePopB_complete` — LIFO driver liveness (PROVEN, `propext`, `Quot.sound`).

## Native assumptions — `Henret/Native/Assumptions.lean`

Six typed axioms (ASSUMED) + derived PROVEN results:
- `NativeDeque.toList_empty/push/steal_val/steal_rest/pop_val/pop_rest`
- `nativeDequeModel : DequeModel` — definitional, no proof burden beyond axioms.
- `nativeDequeModel_qRun_tracks` — PROVEN; depends on exactly the 6 axioms.
- `nativeDequeModel_driveComplete` — PROVEN; no native axioms.
