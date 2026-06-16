import Henret.Core.Id

/-!
# Henret.Actor.Meta  (RFC 059)

Optional per-task scheduling metadata: a `priority` and an optional logical
`deadline`. Metadata is **optional** — a task without an entry uses the default
(`defaultMeta`) — honouring the RFC 059 non-goal that not every task must carry
priority/deadline metadata.

Convention (RFC 059 review questions):
- **higher `priority` Nat = higher priority** (`priorityPolicy` picks the max);
- a **smaller `deadline` is more urgent**, and a **missing deadline sorts last**
  (a task with no deadline is the least urgent under earliest-deadline-first).

Deadlines are **logical-time ordering metadata only** — Henret makes no
wall-clock or real-time guarantee.
-/

namespace Henret

/-- Scheduling metadata for a task. -/
structure TaskMeta where
  /-- Higher is more important. -/
  priority : Nat := 0
  /-- Logical-time deadline; `none` = no deadline (least urgent). -/
  deadline : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- The metadata a task without an explicit entry is treated as having:
lowest priority, no deadline. -/
def defaultMeta : TaskMeta := { priority := 0, deadline := none }

end Henret
