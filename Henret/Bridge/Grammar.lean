import Henret.Model
/-!
  # Henret.Bridge.Grammar  (RFC 036)

  Translation from henret's `RuntimeOp` to the queue-operation grammar
  used by the single-worker bridge.

  ## Design (RFC 036)

  `RuntimeOp` is the full scheduler grammar (12 operations).
  The bridge `QOp` grammar mirrors the lean-runtime queue grammar and adds
  `Filter` for the cancellation case (RFC 036):

  | QOp        | Meaning                               |
  |------------|---------------------------------------|
  | `Push w t` | Append task `t` to worker `w`'s queue |
  | `Pop w`    | Dequeue the head of worker `w`'s queue |
  | `Filter w t` | Remove all occurrences of `t` from worker `w`'s queue |
  | `Steal s d` | (multi-worker only; no-op in single-worker bridge) |
  | `Wake t`   | (mirrored from lean-runtime; not emitted by single-worker `toQOps`) |
  | `Inject t` | (mirrored from lean-runtime; not emitted by single-worker `toQOps`) |

  In the single-worker bridge, `toQOps` only ever emits `Push`, `Pop`, and
  `Filter`. `Wake`, `Steal`, and `Inject` are kept in the grammar for
  lean-runtime mirror fidelity but are not produced by this bridge (RFC 036,
  Design A: eliminate `Wake` from `toQOps`; `applyQOp .Wake` is a no-op).

  ## Ready-queue effect table

  | RuntimeOp      | `toQOps` (valid)         | `toQOps` (invalid) |
  |----------------|--------------------------|---------------------|
  | `spawn a`      | `[Push 0 nextId]`        | `[]`               |
  | `spawnChild t a` | `[Push 0 nextId]`      | `[]`               |
  | `schedule`     | `[Pop 0]`                | `[]`               |
  | `yield t`      | `[Push 0 t]`             | `[]`               |
  | `wake t`       | `[Push 0 t]`             | `[]`               |
  | `cancel t`     | `[Filter 0 t]`           | `[]`               |
  | `send t b m`   | `[Push 0 w]` (waiter) or `[]` | `[]`          |
  | `inject a m`   | `[Push 0 w]` (waiter) or `[]` | `[]`          |
  | `tick t`       | `[Push 0 u₁, ...]`       | `[]`               |
  | `complete t`   | `[]`                     | `[]`               |
  | `receive t`    | `[]`                     | `[]`               |
  | `sleep t d`    | `[]`                     | `[]`               |

  Guard compatibility: `toQOps s op = []` whenever `(step s op).2 = .invalid`.
-/
namespace Henret.Bridge

/-! ## QOp — the bridge/lean-runtime queue operation grammar -/

/-- Worker index (lean-runtime uses `Nat`-indexed workers). In the single-worker
bridge, the worker is always 0. -/
abbrev WorkerIdx := Nat

/-- Queue operations. Mirrors the lean-runtime queue grammar plus `Filter`
    (RFC 036) for cancellation. `Wake`, `Steal`, and `Inject` are included
    for grammar-mirror fidelity but are not emitted by the single-worker
    `toQOps` translation. -/
inductive QOp where
  /-- Append task `t` to worker `w`'s queue. -/
  | Push   (worker : WorkerIdx) (task : TaskId)   : QOp
  /-- Dequeue the head of worker `w`'s queue (schedule step). -/
  | Pop    (worker : WorkerIdx)                   : QOp
  /-- Remove all occurrences of task `t` from worker `w`'s queue (cancel). -/
  | Filter (worker : WorkerIdx) (task : TaskId)   : QOp
  /-- (Multi-worker only; no-op in single-worker bridge.) -/
  | Steal  (src dst : WorkerIdx)                  : QOp
  /-- (Lean-runtime mirror; not emitted by single-worker toQOps.) -/
  | Wake   (task : TaskId)                        : QOp
  /-- (Lean-runtime mirror; not emitted by single-worker toQOps.) -/
  | Inject (task : TaskId)                        : QOp
deriving Repr, DecidableEq

/-! ## Grammar translation -/

/-- Translate a single `RuntimeOp` to the list of `QOp`s it drives.

    Guard-compatible (RFC 036): for every operation, if `step s op` returns
    `.invalid` then `toQOps s op = []`.  The single-worker bridge only emits
    `Push`, `Pop`, and `Filter`; `Wake`, `Steal`, and `Inject` are never
    produced by this translation. -/
def toQOps (s : RuntimeState) (op : RuntimeOp) : List QOp :=
  match op with
  | .spawn _ =>
      if s.taskState s.nextId = none then [.Push 0 s.nextId] else []
  | .spawnChild t _ =>
      if s.running = some t then
        match s.taskState t with
        | some .running =>
          match s.taskOwner t, s.taskState s.nextId with
          | some _, none => [.Push 0 s.nextId]
          | _, _         => []
        | _ => []
      else []
  | .schedule =>
      match s.running, s.readyQ with
      | none, t :: _ =>
          if (s.taskState t).any TaskState.isRunnable then [.Pop 0] else []
      | _, _ => []
  | .yield t =>
      if s.running = some t then
        match s.taskState t with
        | some .running => [.Push 0 t]
        | _             => []
      else []
  | .wake t =>
      match s.taskState t with
      | some .sleeping => [.Push 0 t]
      | _              => []
  | .cancel t =>
      match s.taskState t with
      | some st => if st.isTerminal then [] else [.Filter 0 t]
      | none    => []
  | .send t b _ =>
      -- Full guard check matching step: running, .running state, has owner, mailbox exists
      if s.running = some t then
        match s.taskState t with
        | some .running =>
          match s.taskOwner t, s.mailboxes b with
          | some _, some _ =>
            match s.mailboxWaiters b with
            | []     => []
            | w :: _ => [.Push 0 w]
          | _, _ => []
        | _ => []
      else []
  | .inject a _ =>
      -- Guard: mailbox must exist
      match s.mailboxes a with
      | some _ =>
        match s.mailboxWaiters a with
        | []     => []
        | w :: _ => [.Push 0 w]
      | none => []
  | .receive _ => []
  | .sleep _ _ => []
  | .complete _ => []
  | .tick t =>
      -- Use argument t, not s.now (architect review §4.3)
      if s.now ≤ t then
        let woken := ((Timer.expired s.timers t).map TimerEntry.task).filter
                       (fun u => s.taskState u = some .sleeping)
        woken.map (fun u => .Push 0 u)
      else []

/-! ## Direct-effect lemmas -/

theorem toQOps_spawn_valid (s : RuntimeState) (a : ActorId)
    (h : s.taskState s.nextId = none) :
    toQOps s (.spawn a) = [.Push 0 s.nextId] := by simp [toQOps, h]

theorem toQOps_spawn_invalid (s : RuntimeState) (a : ActorId)
    (h : s.taskState s.nextId ≠ none) :
    toQOps s (.spawn a) = [] := by simp [toQOps, h]

theorem toQOps_spawnChild_valid (s : RuntimeState) (t : TaskId) (a : ActorId) (oa : ActorId)
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some oa) (hfresh : s.taskState s.nextId = none) :
    toQOps s (.spawnChild t a) = [.Push 0 s.nextId] := by
  simp [toQOps, hrt, hts, how, hfresh]

theorem toQOps_schedule_empty (s : RuntimeState) (h : s.readyQ = []) :
    toQOps s .schedule = [] := by simp [toQOps, h]

theorem toQOps_schedule_norunning (s : RuntimeState) (t : TaskId)
    (h : s.running = some t) :
    toQOps s .schedule = [] := by simp [toQOps, h]

theorem toQOps_schedule_nonempty (s : RuntimeState) (t : TaskId) (rest : List TaskId)
    (hr : s.running = none) (h : s.readyQ = t :: rest)
    (hrun : (s.taskState t).any TaskState.isRunnable = true) :
    toQOps s .schedule = [.Pop 0] := by simp [toQOps, hr, h, hrun]

theorem toQOps_yield_valid (s : RuntimeState) (t : TaskId)
    (hrt : s.running = some t) (hts : s.taskState t = some .running) :
    toQOps s (.yield t) = [.Push 0 t] := by simp [toQOps, hrt, hts]

theorem toQOps_yield_invalid (s : RuntimeState) (t : TaskId)
    (h : s.running ≠ some t ∨ s.taskState t ≠ some .running) :
    toQOps s (.yield t) = [] := by
  rcases h with h | h
  · simp [toQOps, h]
  · by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simp [toQOps, hrt, hts]
      | some st => cases st with
        | running => exact absurd hts (by simp [hts] at h)
        | new | ready | yielded | sleeping | completed | cancelled | waiting =>
          simp [toQOps, hrt, hts]
    · simp [toQOps, hrt]

theorem toQOps_wake_valid (s : RuntimeState) (t : TaskId)
    (h : s.taskState t = some .sleeping) :
    toQOps s (.wake t) = [.Push 0 t] := by simp [toQOps, h]

theorem toQOps_wake_invalid (s : RuntimeState) (t : TaskId)
    (h : s.taskState t ≠ some .sleeping) :
    toQOps s (.wake t) = [] := by
  cases hts : s.taskState t with
  | none => simp [toQOps, hts]
  | some st => cases st with
    | sleeping => exact absurd hts h
    | new | ready | running | yielded | completed | cancelled | waiting => simp [toQOps, hts]

theorem toQOps_cancel_valid (s : RuntimeState) (t : TaskId) (st : TaskState)
    (hts : s.taskState t = some st) (hnt : ¬st.isTerminal) :
    toQOps s (.cancel t) = [.Filter 0 t] := by
  simp [toQOps, hts, hnt]

theorem toQOps_cancel_invalid_terminal (s : RuntimeState) (t : TaskId) (st : TaskState)
    (hts : s.taskState t = some st) (ht : st.isTerminal) :
    toQOps s (.cancel t) = [] := by simp [toQOps, hts, ht]

theorem toQOps_cancel_invalid_unspawned (s : RuntimeState) (t : TaskId)
    (hts : s.taskState t = none) :
    toQOps s (.cancel t) = [] := by simp [toQOps, hts]

theorem toQOps_send_valid_waiter (s : RuntimeState) (t b w : TaskId) (m : Message)
    (oa : ActorId) (mb : Mailbox) (ws : List TaskId)
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some oa) (hmb : s.mailboxes b = some mb)
    (hwt : s.mailboxWaiters b = w :: ws) :
    toQOps s (.send t b m) = [.Push 0 w] := by
  simp [toQOps, hrt, hts, how, hmb, hwt]

theorem toQOps_send_valid_no_waiter (s : RuntimeState) (t b : TaskId) (m : Message)
    (oa : ActorId) (mb : Mailbox)
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some oa) (hmb : s.mailboxes b = some mb)
    (hwt : s.mailboxWaiters b = []) :
    toQOps s (.send t b m) = [] := by
  simp [toQOps, hrt, hts, how, hmb, hwt]

theorem toQOps_inject_valid_waiter (s : RuntimeState) (a w : ActorId) (m : Message)
    (mb : Mailbox) (ws : List TaskId)
    (hmb : s.mailboxes a = some mb) (hwt : s.mailboxWaiters a = w :: ws) :
    toQOps s (.inject a m) = [.Push 0 w] := by
  simp [toQOps, hmb, hwt]

theorem toQOps_inject_valid_no_waiter (s : RuntimeState) (a : ActorId) (m : Message)
    (mb : Mailbox) (hwt : s.mailboxWaiters a = []) (hmb : s.mailboxes a = some mb) :
    toQOps s (.inject a m) = [] := by
  simp [toQOps, hmb, hwt]

theorem toQOps_inject_invalid (s : RuntimeState) (a : ActorId) (m : Message)
    (hmb : s.mailboxes a = none) :
    toQOps s (.inject a m) = [] := by simp [toQOps, hmb]

theorem toQOps_complete_nil (s : RuntimeState) (t : TaskId) :
    toQOps s (.complete t) = [] := rfl

theorem toQOps_receive_nil (s : RuntimeState) (t : TaskId) :
    toQOps s (.receive t) = [] := rfl

theorem toQOps_sleep_nil (s : RuntimeState) (t : TaskId) (d : Nat) :
    toQOps s (.sleep t d) = [] := rfl

theorem toQOps_tick_invalid (s : RuntimeState) (t : Nat) (h : ¬(s.now ≤ t)) :
    toQOps s (.tick t) = [] := by simp [toQOps, h]

theorem toQOps_tick_valid (s : RuntimeState) (t : Nat) (h : s.now ≤ t) :
    toQOps s (.tick t) =
      (((Timer.expired s.timers t).map TimerEntry.task).filter
        (fun u => s.taskState u = some .sleeping)).map (fun u => .Push 0 u) := by
  simp [toQOps, h]

end Henret.Bridge
