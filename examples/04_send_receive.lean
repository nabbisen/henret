import Henret
/-!
# Example 04 — Actor-Scoped Send and Receive (RFC 024)

Concept: message passing is performed **by tasks on behalf of their
actors**. `send t b m`: the running task `t` sends `m` to actor `b`.
`receive t`: the running task `t` dequeues from its **own** actor's
mailbox — the actor is derived from `taskOwner t`, never named by the
caller. `inject a m` is the task-free environment delivery path.
All three are purely structural: no task lifecycle state changes
(`Henret.Proofs.StepProjections`).

Run with:  `lake env lean examples/04_send_receive.lean`
-/
open Henret

-- Set up: actor 7's task 0 and actor 9's task 1; schedule task 0.
def s0 := run RuntimeState.init [.spawn 7, .spawn 9, .schedule]
#eval s0.running
-- some 0   (task 0, owned by actor 7, is running)

-- The running task sends to another actor and to its own.
def s1 := run s0 [
  .send 0 9 ⟨1, 100⟩,   -- task 0 → actor 9
  .send 0 7 ⟨2, 200⟩,   -- task 0 → its own actor 7
  .inject 7 ⟨3, 300⟩    -- environment → actor 7
]
#eval (s1.mailboxes 9).map (·.messages)
-- some [{ id := 1, payload := 100 }]
#eval (s1.mailboxes 7).map (·.messages)
-- some [{ id := 2, payload := 200 }, { id := 3, payload := 300 }]

-- Receive names only the task; the mailbox is the OWNER's.
def sr2 := step s1 (.receive 0)
#eval sr2.2
-- received { id := 2, payload := 200 }   (head of actor 7's mailbox)
#eval (sr2.1.mailboxes 7).map (·.messages)
-- some [{ id := 3, payload := 300 }]
#eval (sr2.1.mailboxes 9).map (·.messages)
-- some [{ id := 1, payload := 100 }]   — untouched

-- PROVEN — the actor-local receive discipline (RFC 024 headline):
-- any successful receive dequeues from the receiver's own actor's
-- mailbox and touches no other mailbox.
#check @Henret.receive_only_own

-- The guards are theorems, not conventions:
#eval (step s1 (.send 1 7 ⟨4, 400⟩)).2
-- invalid   — task 1 is not running
#check @Henret.send_not_running_invalid
#eval (step s1 (.receive 1)).2
-- invalid   — task 1 is not running either
#check @Henret.receive_unowned_invalid
-- a task with no owning actor can never receive

-- Receive from an empty (own) mailbox is BLOCKED, not invalid
-- (RFC 029) — a legal waiting condition, distinct from a violation.
#check @Henret.receive_empty_blocked

-- Messaging never changes any task's lifecycle state — proved once,
-- per projection:
#check @Henret.send_taskState
#check @Henret.receive_taskState
#check @Henret.inject_taskState
