import Henret.Trace.Event
/-!
  # Henret.Trace.Run  (RFC 045)

  `stepTrace` and `runTraceLedger`: execution that, in addition to the
  ordinary `(state, result)` pair, emits a list of `TraceEvent`s.

  ## Agreement by construction

  `stepTrace` is defined to reuse `step` for its state and result
  components, adding only a separate `traceEvents` computation.  As a
  result the agreement theorems

      stepTrace_state_eq_step  : (stepTrace s op).1   = (step s op).1
      stepTrace_result_eq_step : (stepTrace s op).2.1 = (step s op).2

  hold by `rfl`.  `runTraceLedger` accumulates events left-to-right and
  agrees with `run` on the final state (`runTraceLedger_state_eq_run`).
-/
namespace Henret.Trace

open Henret

/-- The semantic events observed when `op` is applied in state `s`.

    Mirrors `step`'s guard structure branch-by-branch, but produces only
    observations — never state.  Guards match `step` exactly, so an
    `invalid`/`noEffect` event is emitted precisely when `step` would
    reject or no-op the operation. -/
def traceEvents (s : RuntimeState) (op : RuntimeOp) : List TraceEvent :=
  match op with
  | .spawn a =>
      match s.taskState s.nextId with
      | none   => [.spawned s.nextId a]
      | some _ => [.invalid op]
  | .spawnChild t a =>
      if s.running = some t then
        match s.taskState t, s.taskOwner t with
        | some .running, some _ =>
          match s.taskState s.nextId with
          | none   => [.spawnChild t s.nextId a]
          | some _ => [.invalid op]
        | _, _ => [.invalid op]
      else [.invalid op]
  | .schedule =>
      match s.running, s.readyQ with
      | none, t :: _ =>
        if (s.taskState t).any TaskState.isRunnable then [.scheduled t]
        else [.invalid op]
      | _, _ => [.invalid op]
  | .yield t =>
      if s.running = some t then
        match s.taskState t with
        | some .running => [.yielded t]
        | _ => [.invalid op]
      else [.invalid op]
  | .complete t =>
      if s.running = some t then
        match s.taskState t with
        | some .running => [.completed t]
        | _ => [.invalid op]
      else [.invalid op]
  | .cancel t =>
      match s.taskState t with
      | some st => if st.isTerminal then [.invalid op] else [.cancelled t]
      | none    => [.invalid op]
  | .cancelTree root =>
      -- One cancellation event per task in the cancellation set.
      (descendantsOf s root).map (fun t => .cancelled t)
  | .send t b _m =>
      if s.running = some t then
        match s.taskState t, s.taskOwner t, s.mailboxes b with
        | some .running, some _, some _ =>
          let base : TraceEvent := .sent t b s.nextMsgId
          match s.mailboxWaiters b with
          | w :: _ => [base, .waiterWoke b w]
          | []     =>
            match s.timedMailboxWaiters b with
            | w :: _ => [base, .waiterWoke b w]
            | []     => [base]
        | _, _, _ => [.invalid op]
      else [.invalid op]
  | .inject a _m =>
      match s.mailboxes a with
      | some _ =>
        let base : TraceEvent := .injected a s.nextMsgId
        match s.mailboxWaiters a with
        | w :: _ => [base, .waiterWoke a w]
        | []     =>
          match s.timedMailboxWaiters a with
          | w :: _ => [base, .waiterWoke a w]
          | []     => [base]
      | none => [.invalid op]
  | .receive t =>
      if s.running = some t then
        match s.taskState t, s.taskOwner t with
        | some .running, some a =>
          match s.mailboxes a with
          | some mb =>
            match mb.dequeue with
            | some (env, _) => [.received t a env.occurrence]
            | none          => [.parked t a]
          | none => [.invalid op]
        | _, _ => [.invalid op]
      else [.invalid op]
  | .receiveUntil t d =>
      if s.running = some t then
        match s.taskState t, s.taskOwner t with
        | some .running, some a =>
          match s.mailboxes a with
          | some mb =>
            match mb.dequeue with
            | some (env, _) => [.received t a env.occurrence]
            | none          =>
              if d ≤ s.now then [.noEffect op .timedOut]
              else [.parked t a]
          | none => [.invalid op]
        | _, _ => [.invalid op]
      else [.invalid op]
  | .receiveByOccurrence t occ =>
      if s.running = some t then
        match s.taskState t, s.taskOwner t with
        | some .running, some a =>
          match s.mailboxes a with
          | some mb =>
            match mb.dequeueFirst (·.occurrence = occ) with
            | some (env, _) => [.received t a env.occurrence]
            | none          => [.parked t a]
          | none => [.invalid op]
        | _, _ => [.invalid op]
      else [.invalid op]
  | .receiveFrom t src =>
      if s.running = some t then
        match s.taskState t, s.taskOwner t with
        | some .running, some a =>
          match s.mailboxes a with
          | some mb =>
            match mb.dequeueFirst (·.source = some src) with
            | some (env, _) => [.received t a env.occurrence]
            | none          => [.parked t a]
          | none => [.invalid op]
        | _, _ => [.invalid op]
      else [.invalid op]
  | .sleep t d =>
      if s.running = some t then
        match s.taskState t with
        | some .running => [.slept t d]
        | _ => [.invalid op]
      else [.invalid op]
  | .tick t =>
      if s.now ≤ t then
        let expiredTasks := (Timer.expired s.timers t).map TimerEntry.task
        let woken := expiredTasks.filter (fun u => s.taskState u = some .sleeping) ++
                     expiredTasks.filter (fun u => s.taskState u = some .waitingTimed)
        woken.map (fun u => .timerWoke t u)
      else [.invalid op]
  | .wake t =>
      match s.taskState t with
      | some .sleeping => [.directWoke t]
      | _ => [.invalid op]
  | .fail t =>
      match s.taskState t with
      | some st => if st.isTerminal then [.invalid op] else [.failed t]
      | none    => [.invalid op]
  | .restartOne parent failedChild actor =>
      if s.running = some parent then
        match s.taskState parent with
        | some .running =>
          if s.taskParent failedChild = some parent then
            match s.taskState failedChild with
            | some .failed =>
              match s.taskState s.nextId with
              | none   => [.restarted parent failedChild s.nextId actor]
              | some _ => [.invalid op]
            | _ => [.invalid op]
          else [.invalid op]
        | _ => [.invalid op]
      else [.invalid op]
  | .closeActor a =>
      match s.mailboxes a with
      | some _ => [.actorClosed a]
      | none   => [.invalid op]
  | .shutdown => [.shutdownBegun]
  | .stopWhenIdle =>
      if s.running = none ∧ s.readyQ = [] ∧ s.timers = []
      then [.stoppedWhenIdle] else [.invalid op]
  | .acquire t =>
      if s.running = some t then
        match s.taskState t with
        | some .running => [.noEffect op (.acquired s.nextResourceId)]
        | _ => [.invalid op]
      else [.invalid op]
  | .release t r =>
      if s.running = some t then
        match s.taskState t with
        | some .running =>
          match s.resources r with
          | some ⟨o, .allocated⟩ => if o = t then [.noEffect op .ok] else [.invalid op]
          | _ => [.invalid op]
        | _ => [.invalid op]
      else [.invalid op]
  | .finalize r =>
      match s.resources r with
      | some ⟨_, .closing⟩ => [.noEffect op .ok]
      | _ => [.invalid op]
  | .setPriority t _ =>
      match s.taskState t with
      | some _ => [.noEffect op .ok]
      | none => [.invalid op]
  | .setDeadline t _ =>
      match s.taskState t with
      | some _ => [.noEffect op .ok]
      | none => [.invalid op]

/-- One step, with its event ledger.  State and result are *exactly*
    `step s op`; only the third component is new. -/
def stepTrace (s : RuntimeState) (op : RuntimeOp) :
    RuntimeState × StepResult × List TraceEvent :=
  let (s', r) := step s op
  (s', r, traceEvents s op)

/-- Run a sequence, accumulating results and events left-to-right. -/
def runTraceLedger (s : RuntimeState) :
    List RuntimeOp → RuntimeState × List StepResult × List TraceEvent
  | []        => (s, [], [])
  | op :: ops =>
    let (s', r, evs) := stepTrace s op
    let (s'', rs, evs') := runTraceLedger s' ops
    (s'', r :: rs, evs ++ evs')

/-! ## Agreement with `step` / `run` -/

/-- `stepTrace` agrees with `step` on the resulting state (by construction). -/
@[simp] theorem stepTrace_state_eq_step (s : RuntimeState) (op : RuntimeOp) :
    (stepTrace s op).1 = (step s op).1 := rfl

/-- `stepTrace` agrees with `step` on the result (by construction). -/
@[simp] theorem stepTrace_result_eq_step (s : RuntimeState) (op : RuntimeOp) :
    (stepTrace s op).2.1 = (step s op).2 := rfl

/-- The events of `stepTrace` are exactly `traceEvents`. -/
@[simp] theorem stepTrace_events (s : RuntimeState) (op : RuntimeOp) :
    (stepTrace s op).2.2 = traceEvents s op := rfl

/-- `runTraceLedger` agrees with `run` on the final state. -/
theorem runTraceLedger_state_eq_run (s : RuntimeState) (ops : List RuntimeOp) :
    (runTraceLedger s ops).1 = run s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    simp only [runTraceLedger, run_cons]
    exact ih (step s op).1

/-- `runTraceLedger` agrees with `runTrace` on the result list. -/
theorem runTraceLedger_results_eq_runTrace (s : RuntimeState) (ops : List RuntimeOp) :
    (runTraceLedger s ops).2.1 = (runTrace s ops).2 := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    simp only [runTraceLedger, runTrace, stepTrace]
    rw [ih (step s op).1]

end Henret.Trace
