import Henret.Render.State
/-!
  # Henret.Render.Diagram  (RFC 050)

  Pure-string Mermaid renderers — no external dependency.  Paste the
  output into any Markdown preview that supports Mermaid.  Covers the
  parent tree, the actor/mailbox view, and the single-worker bridge
  projection.
-/
namespace Henret.Render

open Henret

/-- A Mermaid `graph TD` of the parent relation: an edge `p --> c` for
    every `taskParent c = some p`.  Restart replacements are annotated. -/
def parentTreeMermaid (s : RuntimeState) : String :=
  let tasks := (List.range s.nextId).filter (fun t => s.taskState t ≠ none)
  let nodes := tasks.map (fun t =>
    let tag := match s.restartOf t with
      | some old => s!"T{t}[\"task {t} (restart of {old})\"]"
      | none     => s!"T{t}[\"task {t}\"]"
    s!"  {tag}")
  let edges := tasks.filterMap (fun c =>
    match s.taskParent c with
    | some p => some s!"  T{p} --> T{c}"
    | none   => none)
  String.intercalate "\n" ("graph TD" :: (nodes ++ edges))

/-- A Mermaid `graph LR` of actors and their mailbox depth / waiter count. -/
def mailboxMermaid (s : RuntimeState) : String :=
  let actors := (List.range s.nextId).filterMap (fun a =>
    match s.mailboxes a with
    | none    => none
    | some mb =>
      let n := mb.messages.length
      let w := (s.mailboxWaiters a).length + (s.timedMailboxWaiters a).length
      some s!"  A{a}[\"actor {a}\\nmsgs={n} waiters={w}\"]")
  String.intercalate "\n" ("graph LR" :: actors)

/-- The single-worker bridge projection: `BridgeState` relates `readyQ`
    to the worker-queue model with worker 0 = `readyQ` and all other
    workers empty (proved by `bridge_run_tracks_single_worker`). -/
def bridgeWorkerQueues (s : RuntimeState) : String :=
  s!"worker 0: {s.readyQ}\n(other workers: empty — single-worker projection)"

end Henret.Render
