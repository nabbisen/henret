import Henret

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
    (trace.contains (.received ⟨1, 100⟩))
  check "mailbox holds exactly message 2"
    ((s2.mailboxes 7).map Mailbox.messages == some [⟨2, 200⟩])

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

  IO.println "all demo stages passed"

/-!
Demo executable (`lake exe henret-demo`).

Runs the example scenarios, prints observations, and asserts the
expected outcomes. A non-zero exit code means a regression.
-/
