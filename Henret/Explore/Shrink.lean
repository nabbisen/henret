import Henret.Explore.Check
/-!
  # Henret.Explore.Shrink  (RFC 048)

  Bounded exploration and deletion-based counterexample shrinking.
-/
namespace Henret.Explore

open Henret

/-- Search all programs up to `depth` for the first that violates `p`.
    Returns the first counterexample, or `none` if `p` holds on the whole
    bounded sample. -/
def explore (w : SmallWorld) (depth : Nat) (p : Property) : Option (List RuntimeOp) :=
  (genPrograms w depth).find? (fun prog => ! p prog)

/-- Does `p` hold on every program up to `depth`? -/
def confirms (w : SmallWorld) (depth : Nat) (p : Property) : Bool :=
  (explore w depth p).isNone

/-- One deletion pass: try removing each operation; keep a removal if the
    property still fails on the shortened program. -/
def shrinkPass (p : Property) : List RuntimeOp → List RuntimeOp
  | []      => []
  | op :: rest =>
    -- try dropping `op`
    if ! p rest then
      -- still a counterexample without `op`: drop it, continue shrinking rest
      shrinkPass p rest
    else
      -- `op` is needed: keep it, shrink the tail
      op :: shrinkPass p rest

/-- Shrink to a fixed point: repeat deletion passes until no operation can
    be removed.  `fuel` bounds the number of passes. -/
def shrinkProgram (p : Property) (fuel : Nat) (prog : List RuntimeOp) : List RuntimeOp :=
  match fuel with
  | 0     => prog
  | f + 1 =>
    let next := shrinkPass p prog
    if next.length < prog.length then shrinkProgram p f next
    else prog

/-- Find a counterexample and shrink it, in one step. -/
def findAndShrink (w : SmallWorld) (depth : Nat) (p : Property) :
    Option (List RuntimeOp) :=
  (explore w depth p).map (shrinkProgram p (depth + 1))

end Henret.Explore
