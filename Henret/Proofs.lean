import Henret.Proofs.StepProjections
import Henret.Proofs.Lifecycle
import Henret.Proofs.Messaging
import Henret.Proofs.Timers
import Henret.Proofs.Ownership
import Henret.Proofs.StepFields
import Henret.Proofs.Invariants
import Henret.Proofs.InvariantsPreservation
import Henret.Proofs.ResourceReachable
import Henret.Proofs.ResourceBranch
import Henret.Proofs.Policy
import Henret.Proofs.Parenthood
import Henret.Proofs.Occurrence
import Henret.Proofs.Supervision
import Henret.Proofs.Restart
import Henret.Proofs.Shutdown

/-!
# Henret.Proofs

Every theorem about the model: lifecycle, messaging (including the
actor-local receive discipline and occurrence identity), timers and
the logical clock, ownership, and the reachability invariant with its
preservation theorem.
Parenthood theorems (RFC 032): `reachable_parent_lt`,
`parent_chain_terminates`.
Occurrence identity (RFC 033): `reachable_occurrence_unique`,
`send_stamps_source`, `inject_stamps_none`.
-/
