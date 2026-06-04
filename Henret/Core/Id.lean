/-!
# Henret.Core.Id

Identifiers for tasks and actors (RFC 004).

Identifiers are plain naturals so the model stays decidable and
executable. A fresh-id counter in the runtime state guarantees
uniqueness by construction; nothing here depends on the concrete
representation beyond decidable equality.
-/

namespace Henret

/-- Identity of a task. -/
abbrev TaskId := Nat

/-- Identity of an actor. -/
abbrev ActorId := Nat

/-- Update a function map at one key. The single mutation primitive
used by the whole model; every state change to a per-id map goes
through `upd`, which keeps preservation proofs uniform. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun j => if j = i then v else f j

@[simp] theorem upd_self {α : Type} (f : Nat → α) (i : Nat) (v : α) :
    upd f i v i = v := by simp [upd]

@[simp] theorem upd_ne {α : Type} (f : Nat → α) {i j : Nat} (v : α)
    (h : j ≠ i) : upd f i v j = f j := by simp [upd, h]

end Henret
