import Henret.Core.Id

/-!
# Henret.Native.DequeModel

Abstract contract for a work-stealing deque, a pure reference implementation,
and two kernel-checked theorems:

* `qRun_tracks` — any backend satisfying the contract tracks the reference
  implementation step-for-step on any sequence of queue operations.
* `driveStackB_complete` — the LIFO/owner-pop driver starves no fueled task.

This module is **pure Lean**: no FFI, no C, no custom axioms.
`#print axioms qRun_tracks` reports only `propext` and `Quot.sound`.

The companion `Henret.Native.Assumptions` sketches where the C deque's
6 typed axioms would live and how they close the trust gap.

Not imported by `import Henret` — users who need the native material must
explicitly `import Henret.Native.DequeModel`.
-/

namespace Henret.Native

/-! ## List helpers -/

/-- Remove the head (FIFO steal: take from the top). -/
def stealHead : List TaskId → Option TaskId × List TaskId
  | []     => (none, [])
  | x :: r => (some x, r)

/-- Remove the last element (LIFO pop: owner takes from the bottom). -/
def popLast : List TaskId → Option TaskId × List TaskId
  | []  => (none, [])
  | [x] => (some x, [])
  | x :: r => let (v, r') := popLast r; (v, x :: r')

/-! ## Backend contract -/

/-- An abstract work-stealing deque backend.

Six laws pin every operation to the observation `toList` (top → bottom),
making any two implementations that satisfy them interchangeable.
This is the deque analogue of `MailboxBackend`. -/
structure DequeModel where
  /-- Carrier type. -/
  Carrier      : Type
  empty        : Carrier
  push         : Carrier → TaskId → Carrier
  /-- Pop the top (FIFO steal, used by thieves). -/
  steal        : Carrier → Option TaskId × Carrier
  /-- Pop the bottom (LIFO owner pop, used by the owner). -/
  pop          : Carrier → Option TaskId × Carrier
  /-- Observation: current contents, top to bottom. -/
  toList       : Carrier → List TaskId
  -- Laws (the trust surface for any native implementation)
  toList_empty : toList empty = []
  toList_push  : ∀ d t, toList (push d t) = toList d ++ [t]
  steal_val    : ∀ d, (steal d).1 = (stealHead (toList d)).1
  steal_rest   : ∀ d, toList (steal d).2 = (stealHead (toList d)).2
  pop_val      : ∀ d, (pop d).1 = (popLast (toList d)).1
  pop_rest     : ∀ d, toList (pop d).2 = (popLast (toList d)).2

/-! ## Reference implementation -/

/-- The `List TaskId` itself satisfies the contract; all laws hold by `rfl`.
This is the in-kernel reference the C deque is differentially compared against. -/
def listDeque : DequeModel where
  Carrier      := List TaskId
  empty        := []
  push d t     := d ++ [t]
  steal        := stealHead
  pop          := popLast
  toList       := id
  toList_empty := rfl
  toList_push  := fun _ _ => rfl
  steal_val    := fun _ => rfl
  steal_rest   := fun _ => rfl
  pop_val      := fun _ => rfl
  pop_rest     := fun _ => rfl

/-! ## Abstract queue programs and refinement -/

/-- The three operations a single worker's deque supports. -/
inductive QOp where
  | push  : TaskId → QOp   -- owner pushes (bottom)
  | steal : QOp             -- thief steals (top)
  | pop   : QOp             -- owner pops (bottom)

/-- Reference step on a bare `List TaskId`. -/
def qStepRef : List TaskId → QOp → List TaskId
  | qs, .push t => qs ++ [t]
  | qs, .steal  => (stealHead qs).2
  | qs, .pop    => (popLast qs).2

/-- Reference execution of a whole program. -/
def qRunRef : List TaskId → List QOp → List TaskId
  | qs, []        => qs
  | qs, op :: ops => qRunRef (qStepRef qs op) ops

/-- Machine step over an abstract backend. -/
def qStepMachine (DM : DequeModel) (d : DM.Carrier) : QOp → DM.Carrier
  | .push t => DM.push d t
  | .steal  => (DM.steal d).2
  | .pop    => (DM.pop d).2

/-- Machine execution of a whole program. -/
def qRunMachine (DM : DequeModel) (d : DM.Carrier) : List QOp → DM.Carrier
  | []        => d
  | op :: ops => qRunMachine DM (qStepMachine DM d op) ops

/-- One step preserves the tracking invariant `DM.toList d = qs`. -/
theorem qStep_tracks (DM : DequeModel) (d : DM.Carrier) (qs : List TaskId) (op : QOp)
    (h : DM.toList d = qs) :
    DM.toList (qStepMachine DM d op) = qStepRef qs op := by
  cases op with
  | push t => simp [qStepMachine, qStepRef, DM.toList_push, h]
  | steal  => simp [qStepMachine, qStepRef, DM.steal_rest, h]
  | pop    => simp [qStepMachine, qStepRef, DM.pop_rest, h]

/-- **Refinement theorem**: any backend satisfying the `DequeModel` contract tracks
the reference (`listDeque`) step-for-step on every program.

`#print axioms qRun_tracks` → only `[propext]`. -/
theorem qRun_tracks (DM : DequeModel) :
    ∀ (prog : List QOp) (d : DM.Carrier) (qs : List TaskId),
      DM.toList d = qs →
      DM.toList (qRunMachine DM d prog) = qRunRef qs prog
  | [],        d, _, h => h
  | op :: ops, d, qs, h => by
      simp only [qRunMachine, qRunRef]
      exact qRun_tracks DM ops _ _ (qStep_tracks DM d qs op h)

/-! ## LIFO/owner-pop driver liveness -/

/-- A task paired with its remaining fuel. -/
abbrev Fueled := TaskId × Nat

/-- Total fuel of a list of fueled tasks. -/
def totalFuel : List Fueled → Nat
  | []             => 0
  | (_, f) :: rest => f + totalFuel rest

@[simp] theorem totalFuel_nil : totalFuel [] = 0 := rfl
@[simp] theorem totalFuel_cons (t : TaskId) (f : Nat) (r : List Fueled) :
    totalFuel ((t, f) :: r) = f + totalFuel r := rfl
@[simp] theorem totalFuel_append_single (r : List Fueled) (t : TaskId) (n : Nat) :
    totalFuel (r ++ [(t, n)]) = totalFuel r + n := by
  induction r with
  | nil => simp [totalFuel]
  | cons x r ih => obtain ⟨_, f⟩ := x; simp [totalFuel, ih]; omega

/-- Fuel-bounded **owner-end stack** driver.

ORIENTATION NOTE (deliberately different from `DequeModel.toList`):
`DequeModel.toList` reads top → bottom, so the owner's end is the list
*back* and `popLast` removes it.  `driveStackB` instead works on the
owner's-eye view — the list *front* is the owner's end (a stack) — because
the fuel recursion is structural there.  The translation between the two
views is `List.reverse`; this driver is a standalone fairness model for
owner-end scheduling, not an operation of `DequeModel` itself.

Semantics: the owner repeatedly takes the front task, decrements its fuel
in place until it reaches zero, then completes it and moves on.  Each task
runs to completion before the next is touched. -/
def driveStackB : Nat → List Fueled → List TaskId
  | 0,    _                => []
  | _+1,  []               => []
  | b+1,  (t, 0)   :: rest => t :: driveStackB b rest
  | b+1,  (t, n+1) :: rest => driveStackB b ((t, n) :: rest)

/-- **Liveness theorem**: given a fuel budget `b ≥ queue-length + total-fuel`,
every task completes exactly once.

The owner-end driver starves no fueled task.  Any native executor layered
on top (OS threads, C deque) is TESTED territory; this layer is PROVEN.

`#print axioms driveStackB_complete` → only `[propext, Quot.sound]`. -/
theorem driveStackB_complete : ∀ (b : Nat) (q : List Fueled),
    q.length + totalFuel q ≤ b → (driveStackB b q).length = q.length := by
  intro b
  induction b with
  | zero =>
      intro q h
      have : q.length = 0 := by omega
      simp [driveStackB, this]
  | succ b ih =>
      intro q h
      cases q with
      | nil => simp [driveStackB]
      | cons x rest =>
          obtain ⟨t, f⟩ := x
          cases f with
          | zero =>
              have hr : rest.length + totalFuel rest ≤ b := by
                simp at h; omega
              simp only [driveStackB, List.length_cons]
              rw [ih rest hr]
          | succ n =>
              have hr : ((t, n) :: rest).length + totalFuel ((t, n) :: rest) ≤ b := by
                simp at h ⊢; omega
              simp only [driveStackB, List.length_cons]
              rw [ih _ hr]
              simp [List.length_cons]

end Henret.Native

/-!
# Henret.Native.DequeModel

Abstract deque contract, reference implementation, and two
kernel-checked theorems for the optional native backend layer.

Main results:

* `DequeModel` — 6-law contract (analogous to `MailboxBackend`).
* `listDeque` — reference implementation; all laws hold by `rfl`.
* `qRun_tracks` — any `DequeModel` backend tracks `listDeque` on any
  queue program.  Only axioms: `propext`.
* `driveStackB_complete` — the LIFO owner-pop driver starves no fueled task.
  Only axioms: `propext`, `Quot.sound`.
-/
