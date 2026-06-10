import Henret.Trace.Run
/-!
  # Henret.Trace.Theorems  (RFC 045)

  Event soundness: each headline event, when emitted by `stepTrace`,
  certifies the corresponding semantic fact about the operation.  Because
  `traceEvents` mirrors `step`'s guards exactly, every soundness proof is
  a guard-case analysis closed by `simp`.

  The RFC requires soundness for receive, park, wake, timer, and
  spawnChild; all are below, plus `scheduled`, `sent`, and `waiterWoke`.
-/
namespace Henret.Trace

open Henret

/-! ## Helper: events accessor -/

/-- The event list of `stepTrace s op`. -/
abbrev eventsOf (s : RuntimeState) (op : RuntimeOp) : List TraceEvent :=
  (stepTrace s op).2.2

@[simp] theorem eventsOf_eq (s : RuntimeState) (op : RuntimeOp) :
    eventsOf s op = traceEvents s op := rfl

/-! ## received -/

/-- A `received` event for `.receive t` certifies that `t` is running,
    owns actor `a`, and `a`'s mailbox head is the delivered occurrence. -/
theorem event_received_sound {s : RuntimeState} {t : TaskId} {a : ActorId} {occ : MessageId}
    (he : .received t a occ ∈ eventsOf s (.receive t)) :
    ∃ mb env mb',
      s.running = some t ∧
      s.taskState t = some .running ∧
      s.taskOwner t = some a ∧
      s.mailboxes a = some mb ∧
      mb.dequeue = some (env, mb') ∧
      env.occurrence = occ := by
  simp only [eventsOf_eq, traceEvents] at he
  by_cases hrt : s.running = some t
  · simp only [if_pos hrt] at he
    match hts : s.taskState t, how : s.taskOwner t with
    | some .running, some a' =>
      match hmb : s.mailboxes a' with
      | none => simp [hts, how, hmb] at he
      | some mb =>
        match hd : mb.dequeue with
        | none => simp [hts, how, hmb, hd] at he
        | some (env, mb') =>
          simp only [hts, how, hmb, hd, List.mem_singleton, TraceEvent.received.injEq,
                     true_and, and_true] at he
          obtain ⟨haa, hocc⟩ := he
          subst haa; subst hocc
          exact ⟨mb, env, mb', hrt, rfl, rfl, hmb, hd, rfl⟩
    | none, _ => simp [hts] at he
    | some .new, _ | some .ready, _ | some .running, none | some .yielded, _
    | some .sleeping, _ | some .waitingTimed, _ | some .completed, _
    | some .cancelled, _ | some .waiting, _ | some .failed, _ => simp [hts, how] at he
  · simp only [if_neg hrt] at he; simp at he

/-- A `parked` event for `.receive t` certifies that `t` is now `.waiting`
    and queued in actor `a`'s waiter list. -/
theorem event_parked_sound {s : RuntimeState} {t : TaskId} {a : ActorId}
    (he : .parked t a ∈ eventsOf s (.receive t)) :
    ((step s (.receive t)).1).taskState t = some .waiting ∧
    t ∈ ((step s (.receive t)).1).mailboxWaiters a := by
  simp only [eventsOf_eq, traceEvents] at he
  by_cases hrt : s.running = some t
  · simp only [if_pos hrt] at he
    cases hts : s.taskState t with
    | none => simp [hts] at he
    | some st => cases st with
      | running =>
        cases how : s.taskOwner t with
        | none => simp [hts, how] at he
        | some a' =>
          cases hmb : s.mailboxes a' with
          | none => simp [hts, how, hmb] at he
          | some mb =>
            cases hd : mb.dequeue with
            | some p => obtain ⟨env, mb'⟩ := p; simp [hts, how, hmb, hd] at he
            | none =>
              simp only [hts, how, hmb, hd, List.mem_singleton, TraceEvent.parked.injEq,
                         true_and, and_true] at he
              subst he
              refine ⟨by simp [step, hrt, hts, how, hmb, hd, upd_self], ?_⟩
              simp [step, hrt, hts, how, hmb, hd, upd_self]
      | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting | failed =>
        simp [hts] at he
  · simp only [if_neg hrt] at he; simp at he

/-! ## directWoke -/

/-- A `directWoke` event for `.wake t` certifies that `t` was sleeping. -/
theorem event_directWoke_sound {s : RuntimeState} {t : TaskId}
    (he : .directWoke t ∈ eventsOf s (.wake t)) :
    s.taskState t = some .sleeping := by
  simp only [eventsOf_eq, traceEvents] at he
  cases hts : s.taskState t with
  | none => simp [hts] at he
  | some st =>
    cases st with
    | sleeping => rfl
    | new | ready | running | yielded | waitingTimed | completed | cancelled | waiting | failed =>
      simp [hts] at he

/-! ## timerWoke -/

/-- A `timerWoke now t` event for `.tick now` certifies that `now` is not
    in the past and `t`'s timer had expired by `now`. -/
theorem event_timerWoke_sound {s : RuntimeState} {now : Nat} {t : TaskId}
    (he : .timerWoke now t ∈ eventsOf s (.tick now)) :
    s.now ≤ now ∧
    t ∈ ((Timer.expired s.timers now).map TimerEntry.task) := by
  simp only [eventsOf_eq, traceEvents] at he
  by_cases hle : s.now ≤ now
  · simp only [if_pos hle, List.mem_map] at he
    obtain ⟨u, hu, heq⟩ := he
    -- heq : TraceEvent.timerWoke now u = TraceEvent.timerWoke now t
    simp only [TraceEvent.timerWoke.injEq, true_and] at heq
    subst heq
    refine ⟨hle, ?_⟩
    rcases List.mem_append.mp hu with hu | hu <;>
      exact (List.mem_filter.mp hu).1
  · simp only [if_neg hle] at he; simp at he

/-! ## spawnChild -/

/-- A `spawnChild parent child a` event certifies that `parent` is the
    running task and `child = nextId` is the fresh task it created for
    actor `a`. -/
theorem event_spawnChild_sound {s : RuntimeState} {parent child : TaskId} {a : ActorId}
    (he : .spawnChild parent child a ∈ eventsOf s (.spawnChild parent a)) :
    s.running = some parent ∧
    s.taskState parent = some .running ∧
    child = s.nextId ∧
    s.taskState s.nextId = none := by
  simp only [eventsOf_eq, traceEvents] at he
  by_cases hrt : s.running = some parent
  · simp only [if_pos hrt] at he
    cases hts : s.taskState parent with
    | none => simp [hts] at he
    | some st => cases st with
      | running =>
        cases how : s.taskOwner parent with
        | none => simp [hts, how] at he
        | some oa =>
          cases hfresh : s.taskState s.nextId with
          | some _ => simp [hts, how, hfresh] at he
          | none =>
            simp only [hts, how, hfresh, List.mem_singleton, TraceEvent.spawnChild.injEq,
                       true_and, and_true] at he
            subst he
            exact ⟨hrt, rfl, rfl, rfl⟩
      | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting | failed =>
        simp [hts] at he
  · simp only [if_neg hrt] at he; simp at he

/-! ## scheduled -/

/-- A `scheduled t` event certifies that nothing was running, `t` was the
    `readyQ` head, and `t` was runnable. -/
theorem event_scheduled_sound {s : RuntimeState} {t : TaskId}
    (he : .scheduled t ∈ eventsOf s .schedule) :
    s.running = none ∧
    (∃ q, s.readyQ = t :: q) ∧
    (s.taskState t).any TaskState.isRunnable := by
  simp only [eventsOf_eq, traceEvents] at he
  cases hr : s.running with
  | some r => simp [hr] at he
  | none =>
    cases hq : s.readyQ with
    | nil => simp [hr, hq] at he
    | cons u q =>
      by_cases hrun : (s.taskState u).any TaskState.isRunnable
      · simp only [hr, hq, if_pos hrun, List.mem_singleton, TraceEvent.scheduled.injEq] at he
        subst he
        exact ⟨rfl, ⟨q, rfl⟩, hrun⟩
      · simp [hr, hq, hrun] at he

/-! ## waiterWoke (send) -/

/-- A `waiterWoke a w` event for `.send t a m` certifies that `w` is the
    head of actor `a`'s (regular or timed) waiter list. -/
theorem event_waiterWoke_send_sound {s : RuntimeState} {t : TaskId} {a : ActorId}
    {m : Message} {w : TaskId}
    (he : .waiterWoke a w ∈ eventsOf s (.send t a m)) :
    (∃ ws, s.mailboxWaiters a = w :: ws) ∨
    (s.mailboxWaiters a = [] ∧ ∃ ws, s.timedMailboxWaiters a = w :: ws) := by
  simp only [eventsOf_eq, traceEvents] at he
  by_cases hrt : s.running = some t
  · simp only [if_pos hrt] at he
    cases hts : s.taskState t with
    | none => simp [hts] at he
    | some st => cases st with
      | running =>
        cases how : s.taskOwner t with
        | none => simp [hts, how] at he
        | some oa =>
          cases hmb : s.mailboxes a with
          | none => simp [hts, how, hmb] at he
          | some mb =>
            cases hw : s.mailboxWaiters a with
            | cons w' ws =>
              simp only [hts, how, hmb, hw, List.mem_cons, List.mem_singleton,
                         TraceEvent.sent.injEq, TraceEvent.waiterWoke.injEq,
                         reduceCtorEq, false_or, true_and] at he
              refine Or.inl ⟨ws, ?_⟩
              rcases he with he | he
              · rw [he]
              · simp at he
            | nil =>
              cases htw : s.timedMailboxWaiters a with
              | cons w' ws =>
                simp only [hts, how, hmb, hw, htw, List.mem_cons, List.mem_singleton,
                           TraceEvent.sent.injEq, TraceEvent.waiterWoke.injEq,
                           reduceCtorEq, false_or, true_and] at he
                refine Or.inr ⟨rfl, ws, ?_⟩
                rcases he with he | he
                · rw [he]
                · simp at he
              | nil => simp [hts, how, hmb, hw, htw] at he
      | new | ready | yielded | sleeping | waitingTimed | completed | cancelled | waiting | failed =>
        simp [hts] at he
  · simp only [if_neg hrt] at he; simp at he

end Henret.Trace
