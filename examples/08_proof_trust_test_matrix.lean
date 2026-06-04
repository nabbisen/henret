import Henret
/-!
# Example 08 — Proof / Trust / Test Matrix

Concept: every correctness claim in Henret is classified as one of:

```
PROVEN    — checked by the Lean kernel (propext + Quot.sound only)
ASSUMED   — stated as a trusted interface / axiom
TESTED    — covered by an executable check
OUTSCOPE  — explicitly not claimed
```

This is not formality for its own sake.  The classification tells readers
exactly how much to trust each claim, and keeps future contributors honest.

Run with:  `lake env lean examples/08_proof_trust_test_matrix.lean`
-/
open Henret

/-! ## PROVEN — the kernel checked it -/

-- Completed tasks never resume.  No hypothesis about reachability needed.
#check @step_preserves_completed
-- This holds for *any* RuntimeState, even one constructed from thin air.
example (s : RuntimeState) (h : s.taskState 0 = some .completed) :
    ((step s (.spawn 99)).1).taskState 0 = some .completed :=
  step_preserves_completed h _

-- Duplicate wake is invalid.
#check @wake_twice_invalid

-- Receive consumes exactly one message.
#check @receive_consumes_one

-- Timer queue sortedness is preserved by every operation.
#check @run_preserves_sorted

-- Audit: #print axioms reports only propext and Quot.sound.
-- #print axioms step_preserves_completed   ← uncomment to inspect

/-! ## TESTED — the demo checks it -/

-- driveOps (the op-level fueled driver) completes spawned tasks.
-- This is tested, not proven, because the termination argument depends on
-- the fuel counter rather than a structural proof about driveOps itself.
#eval
  let s := run RuntimeState.init (List.replicate 5 (.spawn 0))
  let s' := Henret.driveOps 20 s
  (s'.taskState 0, s'.taskState 4)
-- (some completed, some completed)

/-! ## OUTSCOPE — explicitly not claimed -/

-- The following are NOT part of Henret's claims.  Attempting to derive them
-- from Henret's theorems would be incorrect.
--
-- • Correctness of C deque memory operations (no race-freedom proof)
-- • OS scheduling fairness under real threads
-- • Wall-clock timer accuracy
-- • Production runtime throughput
-- • General-purpose async/await semantics
--
-- These are documented in docs/proof-trust-test-matrix.md.

/-! ## ASSUMED — in the optional native layer (future, RFC 010) -/

-- The Lean-only core (v0.1.0) has zero project-specific assumptions.
-- When a native backend lands, its typed assumptions will be registered in
-- docs/assumption-index.md and mapped to conformance tests.
--
-- Example of what an assumption would look like (not present in v0.1.0):
--
--   axiom c_deque_push_spec : ∀ q v, dequeue (push q v) = some (v, q)
