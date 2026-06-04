import Henret.Proofs.StepProjections
import Henret.Proofs.Lifecycle
import Henret.Proofs.Messaging
import Henret.Proofs.Timers
import Henret.Proofs.Ownership
import Henret.Proofs.Invariants
import Henret.Proofs.InvariantsPreservation

/-!
# Henret.Proofs

Every theorem about the model: lifecycle, messaging (including the
actor-local receive discipline), timers and the logical clock,
ownership, and the reachability invariant with its preservation
theorem. Brings in
`Henret.Model` transitively (RFC 025).
-/
