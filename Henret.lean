import Henret.Model
import Henret.Proofs
import Henret.Refinement
import Henret.Bridge
import Henret.Trace

/-!
# Henret

Executable actor and task runtime models for Lean 4.

Lighter entry points (RFC 025): `Henret.Model` (executable model
only), `Henret.Proofs` (model + all theorems), `Henret.Refinement`
(backend contracts). Examples live in `Henret.Examples.Basic` and are
no longer part of this default import.

The default import is Lean-only (RFC 003): no C compiler, no native
backend, no OS reactor. Optional native backend material, if added,
lives outside this import path (RFC 010).
-/
