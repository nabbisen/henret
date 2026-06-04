import Henret
import Henret.Native.DequeModel
import Henret.Native.Assumptions
open Henret Henret.Native
/-!
# Example 09 — Optional FFI Backend Boundary (RFC 010)

Concept: the typed-axiom discipline for a native C deque backend.

The native modules (`Henret.Native.*`) are **not** imported by `import Henret`.
Build them separately: `lake build HenretNative`.

Run with:  `lake env lean examples/09_optional_ffi_boundary.lean`
           (requires `lake build HenretNative` first)
-/

/-! ## The contract -/

-- DequeModel: 6-law abstract contract (analogous to MailboxBackend)
#check @DequeModel

-- listDeque: verified reference implementation; all laws hold by rfl
#check @listDeque
example : listDeque.toList_empty = rfl := rfl

/-! ## Refinement theorem (PROVEN, no native axioms) -/

-- Any backend satisfying DequeModel tracks listDeque on any program.
#check @qRun_tracks
-- #print axioms qRun_tracks  -- only [propext]

-- LIFO driver liveness: no native axioms either
#check @drivePopB_complete
-- #print axioms drivePopB_complete  -- [propext, Quot.sound]

/-! ## The native backend (6 ASSUMED axioms) -/

-- The 6 axioms that bound the C deque's trust surface
#check @NativeDeque.toList_empty   -- ASSUMED
#check @NativeDeque.toList_push    -- ASSUMED
#check @NativeDeque.steal_val      -- ASSUMED
#check @NativeDeque.steal_rest     -- ASSUMED
#check @NativeDeque.pop_val        -- ASSUMED
#check @NativeDeque.pop_rest       -- ASSUMED

-- These 6 make nativeDequeModel a DequeModel
#check @nativeDequeModel

-- Consequence: the native deque tracks the reference — PROVEN given the 6
-- #print axioms nativeDequeModel_qRun_tracks
-- → [propext, Classical.choice,
--    NativeDeque.toList_empty, .toList_push, .steal_val,
--    .steal_rest, .pop_val, .pop_rest]

-- The core is unaffected: importing native axioms does NOT change
-- #print axioms step_preserves_terminal  → still [propext]

/-! ## What is NOT claimed -/

-- C memory race-freedom (concurrent steal + push) is OUTSCOPE:
-- it requires Iris-style concurrent separation logic, not Lean axioms.
-- OS scheduling fairness and wall-clock timer accuracy are also OUTSCOPE.
-- See docs/native-backend-boundary.md.
