import Henret.Proofs.StepProjections

namespace Henret

/-! ## Task-scoped send (RFC 024) -/

/-- A scoped send appends exactly `m` to the target mailbox (identity
preserved, FIFO order preserved). Guards: `t` is the running task in
`running` state with an owning actor; `b`'s mailbox exists. -/
theorem send_appends {s : RuntimeState} {t : TaskId} {b : ActorId}
    {o : ActorId} {mb : Mailbox}
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some o) (hmb : s.mailboxes b = some mb)
    (m : Message) :
    ((step s (.send t b m)).1).mailboxes b =
      some ⟨mb.messages ++ [m]⟩ := by
  simp [step, hrt, hts, how, hmb, upd, Mailbox.enqueue]

/-- Send does not touch any mailbox other than the target's,
regardless of guard outcomes. -/
theorem send_preserves_other {s : RuntimeState} {t : TaskId}
    {b c : ActorId} (h : c ≠ b) (m : Message) :
    ((step s (.send t b m)).1).mailboxes c = s.mailboxes c := by
  simp only [step]
  split
  · split
    · split
      · split
        · simp [upd, h]
        · rfl
      · rfl
    all_goals rfl
  · rfl

/-- A send by a task that is not running is invalid and a no-op. -/
theorem send_not_running_invalid {s : RuntimeState} {t : TaskId}
    {b : ActorId} (h : s.running ≠ some t) (m : Message) :
    step s (.send t b m) = (s, .invalid) := by
  simp [step, h]

/-- A send by a task with no owning actor is invalid: only actor
tasks send. -/
theorem send_unowned_invalid {s : RuntimeState} {t : TaskId}
    {b : ActorId} (how : s.taskOwner t = none) (m : Message) :
    (step s (.send t b m)).2 = .invalid := by
  simp only [step]
  split
  · split
    · rw [how]
    all_goals rfl
  · rfl

/-! ## Actor-local receive (RFC 024) -/

/-- A successful scoped receive consumes exactly one message — the
head of the receiving task's **own** actor's mailbox. -/
theorem receive_consumes_one {s : RuntimeState} {t : TaskId}
    {a : ActorId} {m : Message} {ms : List Message}
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some a)
    (hmb : s.mailboxes a = some ⟨m :: ms⟩) :
    step s (.receive t) =
      ({ s with mailboxes := upd s.mailboxes a (some ⟨ms⟩) },
        .received m) := by
  simp [step, hrt, hts, how, hmb, Mailbox.dequeue]

/-- Corollary: the mailbox length decreases by exactly one. -/
theorem receive_length {s : RuntimeState} {t : TaskId} {a : ActorId}
    {m : Message} {ms : List Message}
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some a)
    (hmb : s.mailboxes a = some ⟨m :: ms⟩) :
    ∃ mb' : Mailbox,
      ((step s (.receive t)).1).mailboxes a = some mb' ∧
      mb'.messages.length + 1 = (m :: ms).length := by
  refine ⟨⟨ms⟩, ?_, by simp⟩
  rw [receive_consumes_one hrt hts how hmb]
  simp [upd]

/-- Receive does not touch any mailbox other than the receiving
task's own actor's. -/
theorem receive_preserves_other {s : RuntimeState} {t : TaskId}
    {a b : ActorId} (how : s.taskOwner t = some a) (h : b ≠ a) :
    ((step s (.receive t)).1).mailboxes b = s.mailboxes b := by
  simp only [step]
  split
  · split
    · rw [how]
      split
      · split
        · split
          · simp_all [upd]
          · rfl
        · rfl
      · rfl
    all_goals rfl
  · rfl

/-- Receive from an empty (own) mailbox is defined: invalid, state
unchanged. -/
theorem receive_empty_invalid {s : RuntimeState} {t : TaskId}
    {a : ActorId}
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some a) (hmb : s.mailboxes a = some ⟨[]⟩) :
    step s (.receive t) = (s, .invalid) := by
  simp [step, hrt, hts, how, hmb, Mailbox.dequeue]

/-- A receive by an unowned task is invalid: only actor tasks
receive. -/
theorem receive_unowned_invalid {s : RuntimeState} {t : TaskId}
    (how : s.taskOwner t = none) :
    (step s (.receive t)).2 = .invalid := by
  simp only [step]
  split
  · split
    · rw [how]
    all_goals rfl
  · rfl

/-- **Actor-local receive discipline** (RFC 024 headline): any
successful receive dequeues the head of the receiving task's own
actor's mailbox — the actor is derived from ownership — and leaves
every other mailbox untouched. -/
theorem receive_only_own {s : RuntimeState} {t : TaskId} {m : Message}
    (h : (step s (.receive t)).2 = .received m) :
    ∃ a mb mb',
      s.taskOwner t = some a ∧
      s.mailboxes a = some mb ∧
      mb.dequeue = some (m, mb') ∧
      ((step s (.receive t)).1).mailboxes a = some mb' ∧
      ∀ b, b ≠ a → ((step s (.receive t)).1).mailboxes b = s.mailboxes b := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => simp [step, hrt, hts] at h
    | some st =>
      cases st with
      | running =>
        cases how : s.taskOwner t with
        | none => simp [step, hrt, hts, how] at h
        | some a =>
          cases hmb : s.mailboxes a with
          | none => simp [step, hrt, hts, how, hmb] at h
          | some mb =>
            cases hd : mb.dequeue with
            | none => simp [step, hrt, hts, how, hmb, hd] at h
            | some p =>
              obtain ⟨m', mb'⟩ := p
              have hm : m' = m := by
                simp [step, hrt, hts, how, hmb, hd] at h
                exact h
              subst hm
              refine ⟨a, mb, mb', rfl, hmb, hd, ?_, ?_⟩
              · simp [step, hrt, hts, how, hmb, hd, upd]
              · intro b hb
                exact receive_preserves_other how hb
      | new => simp [step, hrt, hts] at h
      | ready => simp [step, hrt, hts] at h
      | yielded => simp [step, hrt, hts] at h
      | sleeping => simp [step, hrt, hts] at h
      | completed => simp [step, hrt, hts] at h
      | cancelled => simp [step, hrt, hts] at h
  · simp [step, hrt] at h

/-! ## Environment injection (RFC 024) -/

/-- Injection appends exactly `m` to the target mailbox. -/
theorem inject_appends {s : RuntimeState} {a : ActorId} {mb : Mailbox}
    (h : s.mailboxes a = some mb) (m : Message) :
    ((step s (.inject a m)).1).mailboxes a =
      some ⟨mb.messages ++ [m]⟩ := by
  simp only [step, h]
  simp [upd, Mailbox.enqueue]

/-- Injection does not touch any other actor's mailbox. -/
theorem inject_preserves_other {s : RuntimeState} {a b : ActorId}
    (h : b ≠ a) (m : Message) :
    ((step s (.inject a m)).1).mailboxes b = s.mailboxes b := by
  simp only [step]
  split
  · simp [upd, h]
  · rfl


/-! ## Mailbox monotonicity: messaging never removes a mailbox -/

/-- Send never removes a mailbox. -/
theorem send_mailbox_isSome {s : RuntimeState} {t : TaskId}
    {b c : ActorId} {mb : Mailbox}
    (h : s.mailboxes c = some mb) (m : Message) :
    ∃ mb', ((step s (.send t b m)).1).mailboxes c = some mb' := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
    | some st =>
      cases st with
      | running =>
        cases how : s.taskOwner t with
        | none => exact ⟨mb, by simp [step, hrt, hts, how]; exact h⟩
        | some o =>
          cases hmb : s.mailboxes b with
          | none => exact ⟨mb, by simp [step, hrt, hts, how, hmb]; exact h⟩
          | some mbb =>
            by_cases hcb : c = b
            · subst hcb
              exact ⟨mbb.enqueue m, by simp [step, hrt, hts, how, hmb, upd]⟩
            · exact ⟨mb, by simpa [step, hrt, hts, how, hmb, upd, hcb] using h⟩
      | new => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
      | ready => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
      | yielded => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
      | sleeping => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
      | completed => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
      | cancelled => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
  · exact ⟨mb, by simp [step, hrt]; exact h⟩

/-- Inject never removes a mailbox. -/
theorem inject_mailbox_isSome {s : RuntimeState} {a c : ActorId}
    {mb : Mailbox} (h : s.mailboxes c = some mb) (m : Message) :
    ∃ mb', ((step s (.inject a m)).1).mailboxes c = some mb' := by
  cases hmb : s.mailboxes a with
  | none => exact ⟨mb, by simp [step, hmb]; exact h⟩
  | some mba =>
    by_cases hca : c = a
    · subst hca
      exact ⟨mba.enqueue m, by simp [step, hmb, upd]⟩
    · exact ⟨mb, by simpa [step, hmb, upd, hca] using h⟩

/-- Receive never removes a mailbox. -/
theorem receive_mailbox_isSome {s : RuntimeState} {t : TaskId}
    {c : ActorId} {mb : Mailbox} (h : s.mailboxes c = some mb) :
    ∃ mb', ((step s (.receive t)).1).mailboxes c = some mb' := by
  by_cases hrt : s.running = some t
  · cases hts : s.taskState t with
    | none => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
    | some st =>
      cases st with
      | running =>
        cases how : s.taskOwner t with
        | none => exact ⟨mb, by simp [step, hrt, hts, how]; exact h⟩
        | some a =>
          cases hmb : s.mailboxes a with
          | none => exact ⟨mb, by simp [step, hrt, hts, how, hmb]; exact h⟩
          | some mba =>
            cases hd : mba.dequeue with
            | none => exact ⟨mb, by simp [step, hrt, hts, how, hmb, hd]; exact h⟩
            | some p =>
              by_cases hca : c = a
              · subst hca
                exact ⟨p.2, by simp [step, hrt, hts, how, hmb, hd, upd]⟩
              · exact ⟨mb, by simpa [step, hrt, hts, how, hmb, hd, upd, hca] using h⟩
      | new => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
      | ready => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
      | yielded => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
      | sleeping => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
      | completed => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
      | cancelled => exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
  · exact ⟨mb, by simp [step, hrt]; exact h⟩

end Henret

/-!
# Henret.Proofs.Messaging

Message-ownership theorems (RFC 006, scoped by RFC 024).

* `send_appends` — a running, owned task's send appends exactly the
  sent message at the target's tail; identity preserved.
* `receive_only_own` — **actor-local receive discipline**: a successful
  receive dequeues from the receiving task's own actor's mailbox (the
  actor derived from `taskOwner`, never named by the caller) and
  touches no other mailbox.
* `receive_consumes_one` / `receive_length` — a successful receive
  removes exactly the head; the remainder is unchanged and in order.
* `send_not_running_invalid`, `send_unowned_invalid`,
  `receive_unowned_invalid`, `receive_empty_invalid` — the guards are
  theorems: only the running task sends, only actor-owned tasks
  message, empty receive is a defined no-op.
* `inject_appends` / `inject_preserves_other` — environment injection
  is the task-free delivery path, with the same per-operation
  exactness.
* `Henret.Proofs.StepProjections` — all three messaging operations
  touch only `mailboxes`; every other field is untouched (proved per
  projection as `@[simp]` lemmas).

SCOPE NOTE (RFC 022): `Message` is a *value* (`id`, `payload`);
occurrence identity is not modeled. Two distinct send/inject
operations may legitimately deliver equal `Message` values to one or
more mailboxes; the theorems above are per-operation, not a global
"each message value exists once" claim. Fresh `MessageId` allocation
with a mailbox-ownership invariant is possible future work.
-/
