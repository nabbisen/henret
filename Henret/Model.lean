import Henret.Core.Id
import Henret.Core.Result
import Henret.Actor.Task
import Henret.Actor.Mailbox
import Henret.Scheduler.Op
import Henret.Scheduler.Timer
import Henret.Scheduler.Model
import Henret.Scheduler.Driver

/-!
# Henret.Model

The executable model, nothing else: identifiers, task/actor state,
the operation grammar, timers, `step`/`run`, and the drivers. Import
this when you want to *run* the model without elaborating any proofs
(RFC 025).
-/
