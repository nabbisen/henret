import Henret.Model
/-!
  # Henret.Bridge.Grammar

  Translation from henret's `RuntimeOp` to lean-runtime's `QOp` grammar.

  `RuntimeOp` is the full scheduler grammar (spawn, schedule, yield, complete,
  cancel, send, receive, inject, sleep, tick, wake, spawnChild — 12 operations).

  `QOp` is the queue-centric sub-grammar (Push, Steal, Pop, Wake, Inject — 5
  ops focused on task movement between worker queues).

  Not every `RuntimeOp` has a queue effect. The mapping is:

  | RuntimeOp | Queue effect (QOp list) | Notes |
  |---|---|---|
  | `spawn a` | `[Push 0 nextId]` | Task enters queue 0 (single-worker model) |
  | `schedule` | `[Pop 0]` | Dequeue head task to run |
  | `yield t` | `[Push 0 t]` | Re-enqueue running task |
  | `complete t` | `[]` | No queue movement; task terminates |
  | `cancel t` | `[]` | No queue movement; task terminates |
  | `send t b m` | `[]` or `[Wake w]` | Wake head waiter if present |
  | `receive t` | `[]` | Dequeue from actor mailbox, not task queue |
  | `inject a m` | `[]` or `[Wake w]` | Wake head waiter if present |
  | `sleep t d` | `[]` | Task leaves queue; tracked by timer |
  | `tick t` | `[Wake w₁, ...]` | Wake all expired timers |
  | `wake t` | `[Wake t]` | Re-enqueue sleeping task |
  | `spawnChild t a` | `[Push 0 nextId]` | Child enters queue 0 |

  This module defines `toQOps` and its direct-effect lemmas.
  The bridge preservation theorem lives in `Henret.Bridge.Preservation`.
-/
namespace Henret.Bridge

/-! ## QOp — the lean-runtime queue operation grammar -/

/-- Worker index (lean-runtime uses `Nat`-indexed workers). In the single-worker
model used by the bridge, the worker is always 0. -/
abbrev WorkerIdx := Nat

/-- Queue operations in the lean-runtime model. These correspond 1-to-1 with
the operations in `lean-runtime/LeanRuntime/Core.lean`. -/
inductive QOp where
  | Push  (worker : WorkerIdx) (task : TaskId)   : QOp
  | Pop   (worker : WorkerIdx)                   : QOp
  | Steal (src dst : WorkerIdx)                  : QOp
  | Wake  (task : TaskId)                        : QOp
  | Inject (task : TaskId)                       : QOp
deriving Repr, DecidableEq

/-! ## Grammar translation -/

/-- Translate a single `RuntimeOp` to the list of `QOp`s it drives.
    Validity-aware: each guard matches the corresponding `step` guard, so
    `toQOps s op = []` whenever `step s op` would return `.invalid`. -/
def toQOps (s : RuntimeState) (op : RuntimeOp) : List QOp :=
  match op with
  | .spawn _        =>
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
  | .schedule       =>
      match s.running, s.readyQ with
      | none, t :: _ =>
          if (s.taskState t).any TaskState.isRunnable then [.Pop 0] else []
      | _, _ => []
  | .yield t        =>
      if s.running = some t then
        match s.taskState t with
        | some .running => [.Push 0 t]
        | _             => []
      else []
  | .complete _     => []
  | .cancel _       => []
  | .send _ b _     =>
      match s.mailboxWaiters b with
      | []     => []
      | w :: _ => [.Wake w]
  | .inject a _     =>
      match s.mailboxWaiters a with
      | []     => []
      | w :: _ => [.Wake w]
  | .receive _      => []
  | .sleep _ _      => []
  | .tick _         =>
      (Timer.expired s.timers s.now).filterMap fun e =>
        if s.taskState e.task == some .sleeping
        then some (.Wake e.task) else none
  | .wake t         =>
      match s.taskState t with
      | some .sleeping => [.Push 0 t]
      | _              => []

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

theorem toQOps_complete_nil (s : RuntimeState) (t : TaskId) :
    toQOps s (.complete t) = [] := rfl

theorem toQOps_cancel_nil (s : RuntimeState) (t : TaskId) :
    toQOps s (.cancel t) = [] := rfl

theorem toQOps_receive_nil (s : RuntimeState) (t : TaskId) :
    toQOps s (.receive t) = [] := rfl

theorem toQOps_sleep_nil (s : RuntimeState) (t : TaskId) (d : Nat) :
    toQOps s (.sleep t d) = [] := rfl

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

theorem toQOps_send_no_waiter (s : RuntimeState) (t b : ActorId) (m : Message)
    (h : s.mailboxWaiters b = []) :
    toQOps s (.send t b m) = [] := by simp [toQOps, h]

theorem toQOps_send_waiter (s : RuntimeState) (t b w : ActorId) (m : Message)
    (ws : List TaskId) (h : s.mailboxWaiters b = w :: ws) :
    toQOps s (.send t b m) = [.Wake w] := by simp [toQOps, h]

theorem toQOps_inject_no_waiter (s : RuntimeState) (a : ActorId) (m : Message)
    (h : s.mailboxWaiters a = []) :
    toQOps s (.inject a m) = [] := by simp [toQOps, h]

theorem toQOps_inject_waiter (s : RuntimeState) (a w : ActorId) (m : Message)
    (ws : List TaskId) (h : s.mailboxWaiters a = w :: ws) :
    toQOps s (.inject a m) = [.Wake w] := by simp [toQOps, h]

theorem toQOps_schedule_empty (s : RuntimeState) (h : s.readyQ = []) :
    toQOps s .schedule = [] := by simp [toQOps, h]

theorem toQOps_schedule_nonempty (s : RuntimeState) (t : TaskId) (rest : List TaskId)
    (hr : s.running = none) (h : s.readyQ = t :: rest)
    (hrun : (s.taskState t).any TaskState.isRunnable = true) :
    toQOps s .schedule = [.Pop 0] := by simp [toQOps, hr, h, hrun]

end Henret.Bridge
