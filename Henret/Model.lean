import Henret.Core.Id
import Henret.Core.Result
import Henret.Actor.Task
import Henret.Actor.Mailbox
import Henret.Scheduler.Op
import Henret.Scheduler.Timer
import Henret.Scheduler.Model
import Henret.Scheduler.Policy
import Henret.Scheduler.Driver

/-!
# Henret.Model

The **light model import** (RFC 025, boundary clarified by RFC 027):
identifiers, task/actor state, the operation grammar, timers,
`step`/`run`, and the drivers, together with the lightweight structural
lemmas those modules carry inline (`upd_self`/`upd_ne`,
`Mailbox.dequeue_spec`, the timer sortedness lemmas, and the driver
liveness proof `drain_completes`).

It does **not** import the heavy proof corpus under `Henret.Proofs` —
in particular `reachable_wf`, the messaging discipline theorems, and
the ownership corollaries are absent after this import. It is a light
import, not a definition-only import; a true definition/lemma split is
recorded as possible future work in RFC 027.
-/
