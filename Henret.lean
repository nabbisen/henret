import Henret.Core.Id
import Henret.Core.Result
import Henret.Actor.Task
import Henret.Actor.Mailbox
import Henret.Scheduler.Op
import Henret.Scheduler.Timer
import Henret.Scheduler.Model
import Henret.Scheduler.Driver
import Henret.Proofs.Lifecycle
import Henret.Proofs.Messaging
import Henret.Proofs.Timers
import Henret.Refinement.Contract
import Henret.Refinement.ReferenceBackend
import Henret.Examples.Basic

/-!
# Henret

Executable actor and task runtime models for Lean 4.

The default import is Lean-only (RFC 003): no C compiler, no native
backend, no OS reactor. Optional native backend material, if added,
lives outside this import path (RFC 010).
-/
