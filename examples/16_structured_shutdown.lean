import Henret
/-!
# Example 16 — Structured Cancellation & Shutdown (RFC 055)

Demonstrates the safety-only shutdown layer: closing an actor to new
messages (without losing queued ones), subtree cancellation via the
existing `cancelTree`, and runtime shutdown rejecting new admission.

Run with:  `lake env lean examples/16_structured_shutdown.lean`
-/
open Henret

/-! ## Closing an actor rejects new sends/injects but keeps the mailbox -/

-- Build a state with one actor (id 0) that has a mailbox, then close it.
def s0 : RuntimeState := run RuntimeState.init [.spawn 0]

-- Actor 0 has a mailbox after spawn.
#eval (s0.mailboxes 0).isSome   -- true

-- Close actor 0.
def s1 : RuntimeState := (step s0 (.closeActor 0)).1

-- It is now closed, but the mailbox still exists (closing ≠ deletion).
#eval (s1.actorStatus 0 == .closed)    -- true
#eval (s1.mailboxes 0).isSome          -- true

-- A send / inject to the closed actor is rejected.
example : (step s1 (.send 0 0 ((⟨0, 7⟩ : Message)))).2 = .invalid :=
  closed_actor_rejects_send (by decide)
example : (step s1 (.inject 0 ((⟨0, 7⟩ : Message)))).2 = .invalid :=
  closed_actor_rejects_inject (by decide)

-- Closing does not delete or alter any mailbox.
example : ((step s0 (.closeActor 0)).1).mailboxes = s0.mailboxes :=
  @closeActor_preserves_mailboxes s0 0

/-! ## Subtree cancellation is `cancelTree` (RFC 039) -/

-- spawn parent (0), child (1) under it, grandchild (2) under the child,
-- then cancel the whole subtree rooted at the parent.
def tree : RuntimeState :=
  run RuntimeState.init
    [.spawn 0, .schedule, .spawnChild 0 0, .schedule, .spawnChild 1 0]

-- cancelTree on the root cancels the root task itself.
example : ((step tree (.cancelTree 0)).1).taskState 0 = some .cancelled :=
  cancelTree_cancels_root (s := tree) (root := 0) (st := .running)
    (by decide) (by decide) (by decide)

/-! ## Runtime shutdown rejects new root spawns and injects -/

def downed : RuntimeState := (step RuntimeState.init .shutdown).1

#eval (downed.runtimeStatus == .shuttingDown)   -- true

example : (step downed (.spawn 5)).2 = .invalid :=
  shutdown_rejects_spawn (by decide)
example : (step downed (.inject 5 ((⟨0, 1⟩ : Message)))).2 = .invalid :=
  shutdown_rejects_inject (by decide)

/-! ## stopWhenIdle reaches `stopped` only from a quiescent state -/

-- The initial runtime is quiescent (no running task, empty queue, no timers).
example : RuntimeQuiescent RuntimeState.init := by decide

-- From quiescent, stopWhenIdle stops the runtime.
example : ((step RuntimeState.init .stopWhenIdle).1).runtimeStatus = .stopped :=
  stopWhenIdle_sets_stopped (by decide)

-- A runtime with a ready task is NOT quiescent, so stopWhenIdle is invalid.
def busy : RuntimeState := run RuntimeState.init [.spawn 0]
example : (step busy .stopWhenIdle).2 = .invalid := by decide

#eval "example 16 ok"
