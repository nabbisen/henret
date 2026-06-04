import Henret.Native.DequeModel

/-!
# Henret.Native.Assumptions

Typed-axiom pattern for a native C deque backend.

## The discipline

A native backend is trusted not because its C code is proven correct, but
because its trust surface is **small and named**.  The pattern:

```text
1. Declare the C operations as `opaque` Lean functions
   (no C linkage yet — just abstract types)
2. State each behavioral law as an `axiom`
   (6 total, matching `DequeModel`)
3. Build a `DequeModel` from the axioms
4. All downstream proofs are PROVEN (no further trust needed)
```

`#print axioms nativeDequeModel_qRun_tracks` then lists exactly these
6 axioms — the auditable trust surface — plus the standard kernel axioms.

## What is NOT claimed

* C memory race-freedom (concurrent steal + push): not representable in
  Lean's type theory; requires Iris-style concurrent separation logic.
* Performance, fairness under OS threads, wall-clock timer accuracy.
* Correctness of the C code itself: the axioms express *what* is trusted;
  conformance tests (`differentialTest`) exercise *whether* it holds.

See `docs/assumption-index.md` for the v0.1.0 status and
`docs/native-backend-boundary.md` for the full discipline.
-/

namespace Henret.Native

/-! ## Step 1: declare the abstract native type and operations -/

/-- Opaque carrier for the native C Chase-Lev deque.
In a real deployment this would be `@[extern "lean_cl_deque_new"] opaque NativeDeque.mk : IO NativeDeque` etc.
Here we declare the pure-state abstraction; the IO wrapper is a separate layer. -/
private opaque NativeDequePointed : NonemptyType
/-- The native deque type. Opaque: no Lean representation. -/
noncomputable def NativeDeque : Type := NativeDequePointed.type
instance : Nonempty NativeDeque := NativeDequePointed.property

noncomputable opaque NativeDeque.empty : NativeDeque
noncomputable opaque NativeDeque.push  : NativeDeque → TaskId → NativeDeque
/-- FIFO steal: thief removes from the top. -/
noncomputable opaque NativeDeque.steal : NativeDeque → Option TaskId × NativeDeque
/-- LIFO pop: owner removes from the bottom. -/
noncomputable opaque NativeDeque.pop   : NativeDeque → Option TaskId × NativeDeque
/-- Sequential observation of deque contents (top → bottom).
In the C implementation this corresponds to a snapshot under mutual exclusion or
a quiescent read — safe only when no concurrent steal is in flight. -/
noncomputable opaque NativeDeque.toList : NativeDeque → List TaskId

/-! ## Step 2: the 6 typed axioms — the entire trust surface -/

/-- ASSUMED: empty deque is empty. -/
axiom NativeDeque.toList_empty : NativeDeque.toList NativeDeque.empty = []

/-- ASSUMED: push appends to the bottom. -/
axiom NativeDeque.toList_push (d : NativeDeque) (t : TaskId) :
    NativeDeque.toList (NativeDeque.push d t) =
    NativeDeque.toList d ++ [t]

/-- ASSUMED: steal returns the correct head value. -/
axiom NativeDeque.steal_val (d : NativeDeque) :
    (NativeDeque.steal d).1 = (stealHead (NativeDeque.toList d)).1

/-- ASSUMED: steal leaves the correct tail. -/
axiom NativeDeque.steal_rest (d : NativeDeque) :
    NativeDeque.toList (NativeDeque.steal d).2 =
    (stealHead (NativeDeque.toList d)).2

/-- ASSUMED: pop returns the correct last value. -/
axiom NativeDeque.pop_val (d : NativeDeque) :
    (NativeDeque.pop d).1 = (popLast (NativeDeque.toList d)).1

/-- ASSUMED: pop leaves the correct remainder. -/
axiom NativeDeque.pop_rest (d : NativeDeque) :
    NativeDeque.toList (NativeDeque.pop d).2 =
    (popLast (NativeDeque.toList d)).2

/-! ## Step 3: the native backend satisfies the contract -/

/-- The native deque satisfies `DequeModel`.
This definition itself is **definitional** — no proof obligations beyond the
6 axioms above. -/
noncomputable def nativeDequeModel : DequeModel where
  Carrier      := NativeDeque
  empty        := NativeDeque.empty
  push         := NativeDeque.push
  steal        := NativeDeque.steal
  pop          := NativeDeque.pop
  toList       := NativeDeque.toList
  toList_empty := NativeDeque.toList_empty
  toList_push  := NativeDeque.toList_push
  steal_val    := NativeDeque.steal_val
  steal_rest   := NativeDeque.steal_rest
  pop_val      := NativeDeque.pop_val
  pop_rest     := NativeDeque.pop_rest

/-! ## Step 4: all downstream proofs are PROVEN -/

/-- Any native deque program tracks the reference implementation.
PROVEN once the 6 axioms are granted.
`#print axioms nativeDequeModel_qRun_tracks` →
  [NativeDeque.toList_empty, ...(the 6)..., propext] -/
theorem nativeDequeModel_qRun_tracks :
    ∀ (prog : List QOp) (d : NativeDeque) (qs : List TaskId),
      NativeDeque.toList d = qs →
      NativeDeque.toList (qRunMachine nativeDequeModel d prog) = qRunRef qs prog :=
  qRun_tracks nativeDequeModel

/-- The owner-end stack driver starves no fueled task — even on the native deque.
PROVEN (the driver proof does not depend on any native axiom). -/
theorem nativeDequeModel_driveComplete (b : Nat) (q : List Fueled)
    (h : q.length + totalFuel q ≤ b) :
    (driveStackB b q).length = q.length :=
  driveStackB_complete b q h

end Henret.Native
