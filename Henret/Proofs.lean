import Henret.Proofs.StepProjections
import Henret.Proofs.Lifecycle
import Henret.Proofs.Messaging
import Henret.Proofs.Timers
import Henret.Proofs.Ownership
import Henret.Proofs.Invariants
import Henret.Proofs.InvariantsPreservation
import Henret.Proofs.Parenthood

/-!
# Henret.Proofs

Every theorem about the model: lifecycle, messaging (including the
actor-local receive discipline), timers and the logical clock,
ownership, and the reachability invariant with its preservation
theorem. Brings in
`Henret.Model` transitively (RFC 025).
Parenthood theorems (RFC 032): `reachable_parent_lt`,
`parent_chain_terminates`.
-/
