import Henret
import Henret.Bridge
import Henret.Examples.Basic

open Henret Henret.Examples

def check (label : String) (ok : Bool) : IO Unit := do
  if ok then
    IO.println s!"  ok: {label}"
  else
    throw <| IO.userError s!"FAILED: {label}"

def main : IO Unit := do
  IO.println "henret-demo — executable actor/task runtime model"

  IO.println "scenario 1: lifecycle (spawn → run → yield → run → complete)"
  let s1 := lifecycle
  IO.println s!"  task 0: {showState (s1.taskState 0)}"
  check "task 0 completed" (s1.taskState 0 == some .completed)
  check "ready queue empty" s1.readyQ.isEmpty

  IO.println "scenario 2: mailbox send/receive"
  let (s2, trace) := mailboxScenario
  check "received message 1"
    (trace.contains (.received ⟨0, some 7, ⟨1, 100⟩⟩))
  check "mailbox holds exactly message 2"
    ((s2.mailboxes 7).map Mailbox.messages == some [⟨1, some 7, ⟨2, 200⟩⟩])

  IO.println "scenario 3: sleep and tick (no early wake)"
  let s3 := sleepTick
  IO.println s!"  task 0: {showState (s3.taskState 0)}  task 1: {showState (s3.taskState 1)}"
  check "task 0 (deadline 10) still sleeping at t=7"
    (s3.taskState 0 == some .sleeping)
  check "task 1 (deadline 5) woken at t=7"
    (s3.taskState 1 == some .ready)

  IO.println "scenario 4: cancel is terminal"
  let s4 := cancelScenario
  check "cancelled task stays cancelled"
    (s4.taskState 0 == some .cancelled)
  check "cancelled task not re-queued" s4.readyQ.isEmpty

  IO.println "scenario 5: drivers complete all spawned tasks"
  let s5 := driven
  check "op-level driver completed tasks 0..4"
    ((List.range 5).all fun t => s5.taskState t == some .completed)
  let s6 := drained
  check "drain driver completed tasks 0..4"
    ((List.range 5).all fun t => s6.taskState t == some .completed)

  IO.println "scenario 6: v0.2.0 model (ownership, logical clock, tick filter)"
  -- ownership recorded at spawn and immutable afterwards
  let (s7, _) := step RuntimeState.init (.spawn 42)
  check "spawned task owned by actor 42" (s7.taskOwner 0 == some 42)
  let s7b := run s7 [.schedule, .yield 0, .schedule, .complete 0]
  check "ownership survives lifecycle" (s7b.taskOwner 0 == some 42)
  -- logical clock: monotonic, backwards tick is invalid and a no-op
  let (s8, _) := step s7 (.tick 10)
  check "clock advanced to 10" (s8.now == 10)
  let (s8b, r8) := step s8 (.tick 3)
  check "backwards tick rejected" (r8 matches .invalid)
  check "backwards tick left state unchanged" (s8b.now == 10)
  -- tick wakes only sleeping tasks. NOTE: in reachable states cancel
  -- already drops the timer (WellFormed.timers_sleep), so to exercise
  -- the tick filter itself we construct an *arbitrary* state holding a
  -- stale entry for a cancelled task.
  let stale : RuntimeState :=
    { RuntimeState.init with
        taskState := upd RuntimeState.init.taskState 0 (some .cancelled)
        timers    := [⟨5, 0⟩]
        nextId    := 1 }
  let (stale', r9) := step stale (.tick 10)
  check "stale timer entry consumed by tick" stale'.timers.isEmpty
  check "stale timer task not woken" (r9 matches .woke [])
  check "stale timer task not re-queued" (!(stale'.readyQ.contains 0))
  check "cancelled stale-timer task unchanged"
    (stale'.taskState 0 == some .cancelled)
  -- and the reachable-state path: cancel drops the timer eagerly
  let s9 := run RuntimeState.init
    [.spawn 1, .schedule, .sleep 0 5, .cancel 0]
  check "cancel drops the pending timer" s9.timers.isEmpty

  IO.println "scenario 7: park → deliver → wake → re-receive → consume (RFC 031)"
  -- the full blocked-receive round trip: an empty own-mailbox receive
  -- parks the running task; a later inject wakes the head waiter; the
  -- woken task is rescheduled and its re-issued receive consumes the
  -- message (Mesa semantics: wake is a notification, not a handoff)
  let s10 := run RuntimeState.init [.spawn 7, .schedule]
  let (s11, r11) := step s10 (.receive 0)
  check "empty own-mailbox receive is blocked" (r11 matches .blocked)
  check "task 0 parked in waiting state" (s11.taskState 0 == some .waiting)
  check "running slot cleared" (s11.running == none)
  check "task 0 in actor 7's waiter list" ((s11.mailboxWaiters 7).contains 0)
  check "non-running receive is invalid, not blocked"
    ((step s10 (.receive 99)).2 matches .invalid)
  let (s12, r12) := step s11 (.inject 7 ⟨1, 100⟩)
  check "inject delivers ok" (r12 matches .ok)
  check "head waiter woken to ready" (s12.taskState 0 == some .ready)
  check "waiter list drained" (s12.mailboxWaiters 7 == [])
  check "woken task re-queued" (s12.readyQ.contains 0)
  check "message sits in mailbox until re-receive (Mesa, no handoff)"
    ((s12.mailboxes 7).map Mailbox.messages == some [⟨0, none, ⟨1, 100⟩⟩])
  let s13 := run s12 [.schedule]
  let (s14, r14) := step s13 (.receive 0)
  check "re-issued receive consumes the delivered message"
    (r14 matches .received ⟨0, none, ⟨1, 100⟩⟩)
  check "mailbox empty after consume"
    ((s14.mailboxes 7).map Mailbox.messages == some [])


  IO.println "scenario 8: spawnChild parent chain (RFC 032)"
  let s15 := spawnChildScenario
  check "child task 1 has task 0 as parent"
    (s15.taskParent 1 == some 0)
  check "parent task 0 completed"
    (s15.taskState 0 == some .completed)
  check "child task 1 queued as .new"
    (s15.taskState 1 == some .new)

  IO.println "scenario 9: bridge queue projection tracks readyQ (RFC 036)"
  -- Run a sequence and verify BridgeState holds at the end via the
  -- trace theorem. This exercises bridge_run_tracks_single_worker.
  let ops9 : List Henret.RuntimeOp := [.spawn 0, .schedule, .yield 1]
  let finalState9 := Henret.run Henret.RuntimeState.init ops9
  let finalQueues9 := Henret.Bridge.applyQOps
    Henret.Bridge.WorkerQueues.init
    (Henret.Bridge.toQOpsTrace Henret.RuntimeState.init ops9)
  -- bridge_run_tracks_single_worker guarantees finalState9.readyQ = finalQueues9 0
  check "bridge queue projection matches readyQ"
    (finalState9.readyQ == finalQueues9 0)
  check "bridge other workers empty"
    (finalQueues9 1 == [] && finalQueues9 2 == [])


  IO.println "scenario 10: cascade cancel (RFC 039)"
  -- Spawn root under actor 0, schedule it, spawn a child, spawn an unrelated
  -- task under actor 1, then cancel the subtree rooted at task 0.
  let s_a := run RuntimeState.init [.spawn 0]        -- task 0 spawned, actor 0
  let s_b := run s_a [.schedule]                     -- task 0 is now running
  let s_c := run s_b [.spawnChild 0 0]               -- task 1: child of task 0, actor 0
  let s_d := run s_c [.spawn 1]                      -- task 2: unrelated, actor 1
  let s_e := run s_d [.cancelTree 0]                 -- cancel subtree rooted at 0
  check "cancelTree: root (task 0) is cancelled"
    (s_e.taskState 0 == some .cancelled)
  check "cancelTree: child (task 1) is cancelled"
    (s_e.taskState 1 == some .cancelled)
  check "cancelTree: unrelated task (task 2) unchanged (.new)"
    (s_e.taskState 2 == some .new)
  check "cancelTree: readyQ has no cancelled tasks"
    (s_e.readyQ.all (fun t => !(s_e.taskState t == some .cancelled)))

  IO.println "all demo stages passed"

/-!
Demo executable (`lake exe henret-demo`).

Runs the example scenarios, prints observations, and asserts the
expected outcomes. A non-zero exit code means a regression.
-/
