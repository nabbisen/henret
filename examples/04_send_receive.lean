import Henret
/-!
# Example 04 — Actor-Scoped Send and Receive (RFC 024 / RFC 031)

Concept: message passing is performed **by tasks on behalf of their
actors**. `send t b m`: the running task `t` sends `m` to actor `b`.
`receive t`: the running task `t` dequeues from its **own** actor's
mailbox — the actor is derived from `taskOwner t`, never named by the
caller. `inject a m` is the task-free environment delivery path.

After RFC 031, `send`/`inject` may change `taskState` and `readyQ` when
waking a head waiter; `receive` may change `taskState`, `running`, and
`mailboxWaiters` when parking on an empty mailbox. The `StepProjections`
lemmas cover the fields that remain unconditionally unchanged.

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
-- invalid   — task 1 IS owned (by actor 9) but is not running:
-- this evaluation demonstrates the NON-RUNNING guard.
-- Separately, ownership is also a guard — a task with no owning actor
-- can never receive:
#check @Henret.receive_unowned_invalid

-- Empty own-mailbox receive now PARKS the task (RFC 031).
-- Set up an empty-mailbox scenario: actor 7's task 0 running, no messages.
def sp0 := run RuntimeState.init [.spawn 7, .schedule]
def sp1 := step sp0 (.receive 0)
#eval sp1.2
-- blocked   (legal wait, not a protocol error)
#eval sp1.1.taskState 0
-- some waiting   (task 0 is parked — not running, not in readyQ)
#eval sp1.1.running
-- none           (running slot is cleared)
#eval sp1.1.mailboxWaiters 7
-- [0]            (task 0 queued on actor 7's waiter list)

-- PROVEN — `receive_empty_parks`: precise step-reduction theorem
-- characterizing the parking transition (guard-driven form):
#check @Henret.receive_empty_parks

-- PROVEN — `receive_blocked_parks`: result-driven form
-- (derives all guards and post-state from the observed .blocked result):
#check @Henret.receive_blocked_parks

-- A later inject wakes the head waiter (Mesa: notification, not handoff).
-- The message goes to the mailbox; the head waiter becomes .ready.
-- The woken task must be rescheduled and re-issue receive to consume it.
def sp2 := step sp1.1 (.inject 7 ⟨5, 500⟩)
#eval sp2.2
-- ok
#eval sp2.1.taskState 0
-- some ready   (task 0 woken)
#eval sp2.1.mailboxWaiters 7
-- []            (waiter list drained)
#eval (sp2.1.mailboxes 7).map (·.messages)
-- some [{ id := 5, payload := 500 }]   (message sits until re-receive)

-- Unconditionally-unchanged fields per operation (RFC 034 doc note):
--   send:    taskOwner, running, timers, now, nextId
--   inject:  taskOwner, running, timers, now, nextId
--   receive: taskOwner, readyQ, timers, now, nextId
#check @Henret.send_taskOwner
#check @Henret.receive_readyQ
#check @Henret.inject_taskOwner
