import Henret.Scheduler.Model

namespace Henret

/-- Send appends exactly `m` to the target mailbox (identity
preserved, FIFO order preserved). -/
theorem send_appends {s : RuntimeState} {a : ActorId} {mb : Mailbox}
    (h : s.mailboxes a = some mb) (m : Message) :
    ((step s (.send a m)).1).mailboxes a =
      some ⟨mb.messages ++ [m]⟩ := by
  simp only [step, h]
  simp [upd, Mailbox.enqueue]

/-- Send does not touch any other actor's mailbox. -/
theorem send_preserves_other {s : RuntimeState} {a b : ActorId}
    (h : b ≠ a) (m : Message) :
    ((step s (.send a m)).1).mailboxes b = s.mailboxes b := by
  simp only [step]
  split
  · simp [upd, h]
  · rfl

/-- A successful receive consumes exactly one message — the head —
and leaves the rest in order. -/
theorem receive_consumes_one {s : RuntimeState} {a : ActorId}
    {m : Message} {ms : List Message}
    (h : s.mailboxes a = some ⟨m :: ms⟩) :
    step s (.receive a) =
      ({ s with mailboxes := upd s.mailboxes a (some ⟨ms⟩) },
        .received m) := by
  simp only [step, h, Mailbox.dequeue]

/-- Corollary: the mailbox length decreases by exactly one. -/
theorem receive_length {s : RuntimeState} {a : ActorId}
    {m : Message} {ms : List Message}
    (h : s.mailboxes a = some ⟨m :: ms⟩) :
    ∃ mb' : Mailbox,
      ((step s (.receive a)).1).mailboxes a = some mb' ∧
      mb'.messages.length + 1 = (m :: ms).length := by
  refine ⟨⟨ms⟩, ?_, by simp⟩
  rw [receive_consumes_one h]
  simp [upd]

/-- Receive does not touch any other actor's mailbox. -/
theorem receive_preserves_other {s : RuntimeState} {a b : ActorId}
    (h : b ≠ a) :
    ((step s (.receive a)).1).mailboxes b = s.mailboxes b := by
  simp only [step]
  split
  · split
    · simp [upd, h]
    · rfl
  · rfl

/-- Receive from an empty mailbox is defined: invalid, state
unchanged (RFC 006 "receive from empty mailbox is defined"). -/
theorem receive_empty_invalid {s : RuntimeState} {a : ActorId}
    (h : s.mailboxes a = some ⟨[]⟩) :
    step s (.receive a) = (s, .invalid) := by
  simp only [step, h, Mailbox.dequeue]

/-- Messaging never touches task lifecycle state. -/
theorem send_preserves_tasks (s : RuntimeState) (a : ActorId)
    (m : Message) (u : TaskId) :
    ((step s (.send a m)).1).taskState u = s.taskState u := by
  simp only [step]
  split <;> rfl

theorem receive_preserves_tasks (s : RuntimeState) (a : ActorId)
    (u : TaskId) :
    ((step s (.receive a)).1).taskState u = s.taskState u := by
  simp only [step]
  split
  · split <;> rfl
  · rfl

end Henret

/-!
# Henret.Proofs.Messaging

Message-ownership theorems (RFC 006).

* `send_appends` — send appends exactly the sent message at the tail;
  message identity is preserved.
* `send_preserves_other` / `receive_preserves_other` — send and
  receive touch only the target actor's mailbox. Together with
  `send_appends` and `receive_consumes_one`: one `send` performs
  exactly one tail append and one `receive` exactly one head removal —
  no single operation duplicates a message.

  SCOPE NOTE (RFC 022): `Message` is a *value* (`id`, `payload`);
  occurrence identity is not modeled. Two distinct `send` operations
  may legitimately deliver equal `Message` values to one or more
  mailboxes; the theorems above are per-operation, not a global
  "each message value exists once" claim. Fresh `MessageId`
  allocation with a mailbox-ownership invariant is possible future
  work (see RFC 022).
* `receive_consumes_one` — a successful receive removes exactly the
  head message; the remainder is unchanged and in order.
* `receive_empty_invalid` — receive from an empty mailbox is defined:
  it is invalid and leaves the state unchanged.
-/
