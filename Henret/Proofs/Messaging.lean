import Henret.Proofs.StepProjections

namespace Henret

/-! ## Task-scoped send (RFC 024, updated for RFC 033) -/

/-- A scoped send appends exactly one envelope — stamped with the current
occurrence id and the sender's actor — to the target mailbox. -/
theorem send_appends {s : RuntimeState} {t : TaskId} {b o : ActorId} {mb : Mailbox}
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some o) (hmb : s.mailboxes b = some mb)
    (m : Message) :
    ((step s (.send t b m)).1).mailboxes b =
      some ⟨mb.messages ++ [⟨s.nextMsgId, s.taskOwner t, m⟩]⟩ := by
  cases hw : s.mailboxWaiters b with
  | cons w ws => simp [step, hrt, hts, how, hmb, hw, upd, Mailbox.enqueue]
  | nil =>
    cases htw : s.timedMailboxWaiters b <;>
      simp [step, hrt, hts, how, hmb, hw, htw, upd, Mailbox.enqueue]

/-- Send does not touch any mailbox other than the target's. -/
theorem send_preserves_other {s : RuntimeState} {t : TaskId}
    {b c : ActorId} (h : c ≠ b) (m : Message) :
    ((step s (.send t b m)).1).mailboxes c = s.mailboxes c := by
  simp only [step]
  split
  · split
    · split
      · split
        · cases hw : s.mailboxWaiters b with
          | cons w ws => simp [hw, upd, h]
          | nil =>
            cases htw : s.timedMailboxWaiters b <;> simp [hw, htw, upd, h]
        · rfl
      · rfl
    all_goals rfl
  · rfl

/-- A send by a non-running task is invalid and a no-op. -/
theorem send_not_running_invalid {s : RuntimeState} {t : TaskId}
    {b : ActorId} (h : s.running ≠ some t) (m : Message) :
    step s (.send t b m) = (s, .invalid) := by
  simp [step, h]

/-- A send by an unowned task is invalid. -/
theorem send_unowned_invalid {s : RuntimeState} {t : TaskId}
    {b : ActorId} (how : s.taskOwner t = none) (m : Message) :
    (step s (.send t b m)).2 = .invalid := by
  simp only [step]
  split
  · split
    · rw [how]
    all_goals rfl
  · rfl

/-! ## Actor-local receive (RFC 024, updated for RFC 033) -/

/-- A successful scoped receive consumes exactly the head **envelope** of
the receiving task's own actor's mailbox (RFC 033). -/
theorem receive_consumes_one {s : RuntimeState} {t : TaskId}
    {a : ActorId} {env : Envelope} {es : List Envelope}
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some a)
    (hmb : s.mailboxes a = some ⟨env :: es⟩) :
    step s (.receive t) =
      ({ s with mailboxes := upd s.mailboxes a (some ⟨es⟩) },
        .received env) := by
  simp [step, hrt, hts, how, hmb, Mailbox.dequeue]

/-- Corollary: the mailbox length decreases by exactly one. -/
theorem receive_length {s : RuntimeState} {t : TaskId} {a : ActorId}
    {env : Envelope} {es : List Envelope}
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some a)
    (hmb : s.mailboxes a = some ⟨env :: es⟩) :
    ∃ mb' : Mailbox,
      ((step s (.receive t)).1).mailboxes a = some mb' ∧
      mb'.messages.length + 1 = (env :: es).length := by
  refine ⟨⟨es⟩, ?_, by simp⟩
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

/-- Receive from an empty own mailbox parks the task (RFC 031). -/
theorem receive_empty_parks {s : RuntimeState} {t : TaskId}
    {a : ActorId}
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some a) (hmb : s.mailboxes a = some ⟨[]⟩) :
    step s (.receive t) =
      ({ s with
           taskState      := upd s.taskState t (some .waiting)
           running        := none
           mailboxWaiters := fun ac => if ac = a then s.mailboxWaiters a ++ [t]
                                       else s.mailboxWaiters ac },
       .blocked) := by
  simp [step, hrt, hts, how, hmb, Mailbox.dequeue]

/-- Result-driven parking theorem (RFC 031 headline). -/
theorem receive_blocked_parks {s : RuntimeState} {t : TaskId}
    (h : (step s (.receive t)).2 = .blocked) :
    ∃ a,
      s.running = some t ∧
      s.taskState t = some .running ∧
      s.taskOwner t = some a ∧
      s.mailboxes a = some Mailbox.empty ∧
      ((step s (.receive t)).1).taskState t = some .waiting ∧
      ((step s (.receive t)).1).running = none ∧
      t ∈ ((step s (.receive t)).1).mailboxWaiters a ∧
      (∀ b, b ≠ a →
        ((step s (.receive t)).1).mailboxWaiters b = s.mailboxWaiters b) ∧
      ((step s (.receive t)).1).mailboxes = s.mailboxes := by
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
            | some p => simp [step, hrt, hts, how, hmb, hd] at h
            | none =>
              have hempty : mb = Mailbox.empty := by
                cases hms : mb.messages with
                | nil => cases mb; simp_all [Mailbox.empty]
                | cons e es =>
                  exact absurd hd (by simp [Mailbox.dequeue, hms])
              subst hempty
              refine ⟨a, hrt, rfl, rfl, hmb, ?_, ?_, ?_, ?_, ?_⟩
              · simp [step, hrt, hts, how, hmb, Mailbox.dequeue, Mailbox.empty, upd_self]
              · simp [step, hrt, hts, how, hmb, Mailbox.dequeue, Mailbox.empty]
              · simp [step, hrt, hts, how, hmb, Mailbox.dequeue, Mailbox.empty]
              · intro b hb
                simp [step, hrt, hts, how, hmb, Mailbox.dequeue, Mailbox.empty, hb]
              · simp [step, hrt, hts, how, hmb, Mailbox.dequeue, Mailbox.empty]
      | new => simp [step, hrt, hts] at h
      | ready => simp [step, hrt, hts] at h
      | yielded => simp [step, hrt, hts] at h
      | sleeping => simp [step, hrt, hts] at h
      | waiting => simp [step, hrt, hts] at h
      | waitingTimed => simp [step, hrt, hts] at h
      | completed => simp [step, hrt, hts] at h
      | cancelled => simp [step, hrt, hts] at h
  · simp [step, hrt] at h

/-- An unowned task's receive is invalid. -/
theorem receive_unowned_invalid {s : RuntimeState} {t : TaskId}
    (how : s.taskOwner t = none) :
    (step s (.receive t)).2 = .invalid := by
  simp only [step]
  split
  · split
    · rw [how]
    all_goals rfl
  · rfl

/-- **Actor-local receive discipline** (RFC 024 headline, updated for RFC 033):
any successful receive dequeues the head **envelope** of the receiving task's
own actor's mailbox and leaves every other mailbox untouched. -/
theorem receive_only_own {s : RuntimeState} {t : TaskId} {env : Envelope}
    (h : (step s (.receive t)).2 = .received env) :
    ∃ a mb mb',
      s.taskOwner t = some a ∧
      s.mailboxes a = some mb ∧
      mb.dequeue = some (env, mb') ∧
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
              obtain ⟨env', mb'⟩ := p
              have henv : env' = env := by
                simp [step, hrt, hts, how, hmb, hd] at h; exact h
              subst henv
              refine ⟨a, mb, mb', rfl, hmb, hd, ?_, ?_⟩
              · simp [step, hrt, hts, how, hmb, hd, upd]
              · intro b hb
                exact receive_preserves_other how hb
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed =>
        simp [step, hrt, hts] at h
  · simp [step, hrt] at h

/-! ## Environment injection (RFC 024, updated for RFC 033) -/

/-- Injection appends exactly one envelope (stamped with current occurrence
id and `source = none`) to the target mailbox. -/
theorem inject_appends {s : RuntimeState} {a : ActorId} {mb : Mailbox}
    (h : s.mailboxes a = some mb) (m : Message) :
    ((step s (.inject a m)).1).mailboxes a =
      some ⟨mb.messages ++ [⟨s.nextMsgId, none, m⟩]⟩ := by
  cases hw : s.mailboxWaiters a with
  | cons w ws => simp [step, h, hw, upd, Mailbox.enqueue]
  | nil =>
    cases htw : s.timedMailboxWaiters a <;>
      simp [step, h, hw, htw, upd, Mailbox.enqueue]

/-- Injection does not touch any other actor's mailbox. -/
theorem inject_preserves_other {s : RuntimeState} {a b : ActorId}
    (h : b ≠ a) (m : Message) :
    ((step s (.inject a m)).1).mailboxes b = s.mailboxes b := by
  simp only [step]
  split
  · cases hw : s.mailboxWaiters a with
    | cons w ws => simp [hw, upd, h]
    | nil =>
      cases htw : s.timedMailboxWaiters a <;> simp [hw, htw, upd, h]
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
              cases hw : s.mailboxWaiters c with
              | cons w ws =>
                exact ⟨mbb.enqueue ⟨s.nextMsgId, s.taskOwner t, m⟩,
                        by simp [step, hrt, hts, how, hmb, hw, upd]⟩
              | nil =>
                cases htw : s.timedMailboxWaiters c <;>
                  exact ⟨mbb.enqueue ⟨s.nextMsgId, s.taskOwner t, m⟩,
                          by simp [step, hrt, hts, how, hmb, hw, htw, upd]⟩
            · cases hw : s.mailboxWaiters b with
              | cons w ws =>
                exact ⟨mb, by simpa [step, hrt, hts, how, hmb, hw, upd, hcb] using h⟩
              | nil =>
                cases htw : s.timedMailboxWaiters b <;>
                  exact ⟨mb, by simpa [step, hrt, hts, how, hmb, hw, htw, upd, hcb] using h⟩
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed =>
        exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
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
      cases hw : s.mailboxWaiters c with
      | cons w ws =>
        exact ⟨mba.enqueue ⟨s.nextMsgId, none, m⟩,
                by simp [step, hmb, hw, upd]⟩
      | nil =>
        cases htw : s.timedMailboxWaiters c <;>
          exact ⟨mba.enqueue ⟨s.nextMsgId, none, m⟩,
                  by simp [step, hmb, hw, htw, upd]⟩
    · cases hw : s.mailboxWaiters a with
      | cons w ws =>
        exact ⟨mb, by simpa [step, hmb, hw, upd, hca] using h⟩
      | nil =>
        cases htw : s.timedMailboxWaiters a <;>
          exact ⟨mb, by simpa [step, hmb, hw, htw, upd, hca] using h⟩

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
      | new | ready | yielded | sleeping | completed | cancelled | waiting | waitingTimed =>
        exact ⟨mb, by simp [step, hrt, hts]; exact h⟩
  · exact ⟨mb, by simp [step, hrt]; exact h⟩

end Henret

/-!
# Henret.Proofs.Messaging

Message-ownership theorems (RFC 006, RFC 024, RFC 033).

Each delivered **envelope** carries `occurrence : MessageId` (globally
unique, allocated from `nextMsgId`) and `source : Option ActorId`
(`some a` for `send`, `none` for `inject`).

Key theorems:
* `send_appends` — sends append one stamped envelope at the target's tail.
* `inject_appends` — inject appends one `source = none` envelope.
* `receive_only_own` — successful receive dequeues the head **envelope**
  of the receiving task's own actor's mailbox (actor-local discipline).
* `receive_consumes_one` — removes exactly the head; remainder unchanged.
* `receive_empty_parks` / `receive_blocked_parks` — empty receive parks.
* `inject_preserves_other` / `send_preserves_other` — cross-mailbox isolation.
* Mailbox isSome monotonicity: send/inject/receive never remove a mailbox.

Occurrence uniqueness theorems live in `Henret.Proofs.Occurrence` (RFC 033).
-/
