/-!
  # Henret.Meta.Docs  (RFC 084 / RFC 075)

  The **checked source of truth** for the model documentation tables. Each
  descriptor sits next to the model definition it documents; the generator
  (`scripts/extract_model_docs.py`) validates that every `name` resolves to a
  real Lean constructor/field, that names are duplicate-free, and that the
  metadata count equals the real count (084-1) before emitting any table.

  Descriptors are plain `String` data so this module is import-cheap (084-5):
  the model tables never force a proof build. The `since`/`category`/`group`
  values are curatorial; only `name` is validated against the source.
-/
namespace Henret.Meta

/-- A documented inductive constructor (operation / state / result). -/
structure ConstructorDoc where
  name     : String
  since    : String
  category : String
  summary  : String
deriving Repr

/-- A documented `WellFormed` invariant field. -/
structure FieldDoc where
  name    : String
  group   : String
  since   : String
  summary : String
deriving Repr

/-- `RuntimeOp` — the 27-operation grammar (`Henret/Scheduler/Op.lean`). -/
def runtimeOpDocs : List ConstructorDoc :=
  [ { name := "spawn",              since := "RFC 004", category := "lifecycle",   summary := "create a root task owned by an actor" },
    { name := "schedule",           since := "RFC 004", category := "lifecycle",   summary := "select the ready-queue head to run" },
    { name := "yield",              since := "RFC 004", category := "lifecycle",   summary := "requeue the running task" },
    { name := "complete",           since := "RFC 004", category := "lifecycle",   summary := "terminate the running task" },
    { name := "cancel",             since := "RFC 004", category := "lifecycle",   summary := "cancel a single task" },
    { name := "send",               since := "RFC 006", category := "messaging",   summary := "running task sends an envelope to an actor" },
    { name := "receive",            since := "RFC 029", category := "messaging",   summary := "dequeue the head envelope or park" },
    { name := "inject",             since := "RFC 006", category := "messaging",   summary := "environment delivers an envelope to an actor" },
    { name := "sleep",              since := "RFC 007", category := "time",        summary := "park the running task with a timer" },
    { name := "tick",               since := "RFC 007", category := "time",        summary := "advance logical time and wake expired timers" },
    { name := "wake",               since := "RFC 005", category := "time",        summary := "directly move a sleeping task to ready" },
    { name := "spawnChild",         since := "RFC 032", category := "lifecycle",   summary := "spawn a child task recording its parent" },
    { name := "cancelTree",         since := "RFC 039", category := "supervision", summary := "cancel a task and all its descendants" },
    { name := "receiveUntil",       since := "RFC 040", category := "time",        summary := "timed receive: park with a deadline or time out" },
    { name := "receiveByOccurrence", since := "RFC 041", category := "messaging",  summary := "selective receive by occurrence id" },
    { name := "receiveFrom",        since := "RFC 041", category := "messaging",   summary := "selective receive by source actor" },
    { name := "fail",               since := "RFC 049", category := "supervision", summary := "mark a task failed and remove it everywhere" },
    { name := "restartOne",         since := "RFC 049", category := "supervision", summary := "spawn a fresh replacement for a failed child" },
    { name := "closeActor",         since := "RFC 055", category := "shutdown",    summary := "close an actor; future send/inject rejected" },
    { name := "shutdown",           since := "RFC 055", category := "shutdown",    summary := "begin runtime shutdown" },
    { name := "stopWhenIdle",       since := "RFC 055", category := "shutdown",    summary := "stop the runtime if quiescent" },
    { name := "stopWhenDrained",    since := "RFC 087", category := "shutdown",    summary := "stop the runtime if quiescent and resources drained" },
    { name := "acquire",            since := "RFC 057", category := "resource",    summary := "running task allocates a fresh resource" },
    { name := "release",            since := "RFC 057", category := "resource",    summary := "owning task releases an allocated resource" },
    { name := "finalize",           since := "RFC 057", category := "resource",    summary := "environment reclaims a closing resource" },
    { name := "setPriority",        since := "RFC 059", category := "metadata",    summary := "set a spawned task's scheduling priority" },
    { name := "setDeadline",        since := "RFC 059", category := "metadata",    summary := "set a spawned task's logical deadline" } ]

/-- `TaskState` — the 10 task lifecycle states (`Henret/Actor/Task.lean`). -/
def taskStateDocs : List ConstructorDoc :=
  [ { name := "new",          since := "RFC 004", category := "initial",   summary := "spawned, not yet scheduled" },
    { name := "ready",        since := "RFC 004", category := "runnable",  summary := "in the ready queue" },
    { name := "running",      since := "RFC 004", category := "runnable",  summary := "currently running" },
    { name := "yielded",      since := "RFC 004", category := "runnable",  summary := "voluntarily requeued" },
    { name := "sleeping",     since := "RFC 007", category := "blocked",   summary := "parked on a timer" },
    { name := "completed",    since := "RFC 004", category := "terminal",  summary := "finished normally" },
    { name := "cancelled",    since := "RFC 004", category := "terminal",  summary := "cancelled" },
    { name := "waiting",      since := "RFC 029", category := "blocked",   summary := "parked on an empty mailbox" },
    { name := "waitingTimed", since := "RFC 040", category := "blocked",   summary := "parked on a mailbox with a deadline" },
    { name := "failed",       since := "RFC 049", category := "terminal",  summary := "failed (supervision)" } ]

/-- `StepResult` — the 10 step outcomes (`Henret/Core/Result.lean`). -/
def stepResultDocs : List ConstructorDoc :=
  [ { name := "ok",        since := "RFC 004", category := "success", summary := "applied; no interesting value" },
    { name := "spawned",   since := "RFC 004", category := "success", summary := "spawn created this task" },
    { name := "scheduled", since := "RFC 004", category := "success", summary := "schedule selected this task" },
    { name := "received",  since := "RFC 033", category := "success", summary := "receive dequeued this envelope" },
    { name := "blocked",   since := "RFC 029", category := "blocked", summary := "legal but cannot progress now (parked)" },
    { name := "timedOut",  since := "RFC 040", category := "blocked", summary := "receiveUntil fast path: deadline passed" },
    { name := "woke",      since := "RFC 007", category := "success", summary := "tick woke these tasks" },
    { name := "backpressured", since := "RFC 056", category := "rejected", summary := "valid send/inject rejected: mailbox at capacity (no-op)" },
    { name := "acquired",  since := "RFC 057", category := "success",  summary := "acquire allocated this resource id" },
    { name := "invalid",   since := "RFC 004", category := "rejected", summary := "not valid in the current state (no-op)" } ]

/-- `WellFormed` — the 33 reachability-invariant fields
    (`Henret/Proofs/Invariants.lean`). -/
def wellFormedDocs : List FieldDoc :=
  [ { name := "readyQ_nodup",            group := "scheduling",  since := "RFC 013", summary := "the ready queue has no duplicates" },
    { name := "readyQ_queued",           group := "scheduling",  since := "RFC 013", summary := "every ready-queue task is runnable" },
    { name := "running_runs",            group := "scheduling",  since := "RFC 013", summary := "the running task is in .running state" },
    { name := "timers_nodup",            group := "timers",      since := "RFC 015", summary := "timer entries are duplicate-free" },
    { name := "timers_sleep",            group := "timers",      since := "RFC 015", summary := "timer-backed tasks are sleeping" },
    { name := "fresh_none",              group := "identity",    since := "RFC 013", summary := "ids at/above nextId are unspawned" },
    { name := "timers_sorted",           group := "timers",      since := "RFC 015", summary := "the timer wheel is sorted" },
    { name := "spawned_has_owner",       group := "ownership",   since := "RFC 013", summary := "every spawned task has an owner" },
    { name := "owned_has_mailbox",       group := "ownership",   since := "RFC 013", summary := "every owning actor has a mailbox" },
    { name := "runnable_queued",         group := "scheduling",  since := "RFC 028", summary := "every runnable task is in the ready queue" },
    { name := "waiters_waiting",         group := "waiting",     since := "RFC 031", summary := "every mailbox waiter is waiting" },
    { name := "waiters_owned",           group := "waiting",     since := "RFC 031", summary := "every waiter has an owner" },
    { name := "waiting_queued",          group := "waiting",     since := "RFC 031", summary := "every waiting task is a waiter" },
    { name := "waiters_nodup",           group := "waiting",     since := "RFC 031", summary := "waiter lists are duplicate-free" },
    { name := "parent_lt",               group := "parenthood",  since := "RFC 032", summary := "a parent id is below its child" },
    { name := "parent_spawned",          group := "parenthood",  since := "RFC 032", summary := "a parent task exists" },
    { name := "occ_fresh",               group := "occurrence",  since := "RFC 033", summary := "every occurrence id is below nextMsgId" },
    { name := "occ_nodup",               group := "occurrence",  since := "RFC 033", summary := "occurrence ids are distinct per mailbox" },
    { name := "occ_disjoint",            group := "occurrence",  since := "RFC 033", summary := "occurrence ids are distinct across mailboxes" },
    { name := "owner_spawned",           group := "exactness",   since := "RFC 038", summary := "an owned task is spawned" },
    { name := "parent_child_spawned",    group := "exactness",   since := "RFC 038", summary := "a task with a parent is spawned" },
    { name := "timed_has_deadline",      group := "timed-wait",  since := "RFC 040", summary := "a waitingTimed task has a deadline" },
    { name := "deadline_is_timed",       group := "timed-wait",  since := "RFC 040", summary := "a task with a deadline is waitingTimed" },
    { name := "timed_has_timer",         group := "timed-wait",  since := "RFC 040", summary := "a waitingTimed task has a timer" },
    { name := "timed_is_waiter",         group := "timed-wait",  since := "RFC 040", summary := "a waitingTimed task is a timed waiter" },
    { name := "timed_waiters_valid",     group := "timed-wait",  since := "RFC 040", summary := "every timed waiter is waitingTimed" },
    { name := "timed_waiters_nodup",     group := "timed-wait",  since := "RFC 040", summary := "timed-waiter lists are duplicate-free" },
    { name := "timed_waiters_exclusive", group := "timed-wait",  since := "RFC 040", summary := "a task waits on at most one timed mailbox" },
    { name := "mailbox_within_capacity", group := "capacity",    since := "RFC 056", summary := "no mailbox exceeds its configured capacity" },
    { name := "resource_fresh",          group := "resource",    since := "RFC 057", summary := "ids at or above the counter are unallocated" },
    { name := "resource_owner_spawned",  group := "resource",    since := "RFC 057", summary := "every resource is owned by a spawned task" },
    { name := "allocated_owner_nonterminal", group := "resource", since := "RFC 057", summary := "an allocated resource's owner is live" },
    { name := "closing_owner_terminal",  group := "resource",    since := "RFC 057", summary := "a closing resource's owner is terminal" } ]

end Henret.Meta
