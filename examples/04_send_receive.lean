import Henret
/-!
# Example 04 — Send and Receive

Concept: message passing between actors.

`send a m` appends message `m` to actor `a`'s mailbox (FIFO queue).
`receive a` removes and returns the *head* message, leaving the rest.
Both operations are **purely structural** — they do not change any task's
lifecycle state.

Run with:  `lake env lean examples/04_send_receive.lean`
-/
open Henret

-- Set up: spawn a task for actor 7 so actor 7 gets a mailbox.
def s0 := (step RuntimeState.init (.spawn 7)).1

-- Send three messages to actor 7.
def s1 := run s0 [
  .send 7 ⟨1, 100⟩,
  .send 7 ⟨2, 200⟩,
  .send 7 ⟨3, 300⟩
]

#eval (s1.mailboxes 7).map (·.messages.length)
-- some 3

-- Receive the first message (head = message id 1).
def sr2 := step s1 (.receive 7)
def s2  := sr2.1
def r   := sr2.2
#eval r
-- received { id := 1, payload := 100 }
#eval (s2.mailboxes 7).map (·.messages)
-- some [{ id := 2, payload := 200 }, { id := 3, payload := 300 }]

-- Proven: receive removes exactly one message (the head).
#check @Henret.receive_consumes_one
-- s.mailboxes a = some mb → mb.messages = m :: rest →
--   ((step s (.receive a)).1).mailboxes a = some { messages := rest }

-- Receive from an empty mailbox is always invalid.
def s3 := run RuntimeState.init [.spawn 99]   -- actor 99, empty mailbox
#eval (step s3 (.receive 99)).2
-- invalid

-- Proven: empty mailbox → receive is always invalid.
#check @Henret.receive_empty_invalid

-- Send never changes any task's lifecycle state.
#check @Henret.send_preserves_tasks
-- ∀ (s : RuntimeState) (a : ActorId) (m : Message) (t : TaskId),
--   ((step s (.send a m)).1).taskState t = s.taskState t
