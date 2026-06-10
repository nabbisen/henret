import Henret.Explore
/-!
# Bounded model explorer entry point (RFC 048)

Confirms the proven invariants over a bounded sample and demonstrates
counterexample shrinking on a deliberately false property.  Build/run:

    lake exe henret-explore

This is empirical model-search support, **not** a proof.  Defaults are
tiny to keep the search bounded; widen `SmallWorld`/`depth` for local
exploration only.
-/
open Henret.Explore

def world : SmallWorld := { maxTask := 2, maxActor := 2, maxMsg := 1, maxTime := 2 }
def depth : Nat := 3

def reportProperty (name : String) (holds : Bool) : IO Unit :=
  if holds then IO.println s!"  CONFIRMED  {name} holds over all programs up to depth {depth}"
  else IO.println s!"  VIOLATED   {name} has a counterexample"

def main : IO UInt32 := do
  IO.println "Henret bounded model explorer (RFC 048)"
  IO.println "========================================"
  IO.println s!"world = {repr world}, depth = {depth}, programs = {(genPrograms world depth).length}"
  IO.println "Confirming proven invariants over the bounded sample:"
  let wf  := confirms world depth propWellFormed
  let occ := confirms world depth (propOccurrenceUnique world)
  let br  := confirms world depth propBridge
  reportProperty "well-formedness (bounded structural)" wf
  reportProperty "occurrence uniqueness (bounded)" occ
  reportProperty "single-worker bridge tracking" br
  IO.println "Shrinking a deliberately false property (readyQ always empty):"
  match findAndShrink world depth propReadyAlwaysEmpty with
  | some prog => IO.println s!"  minimal counterexample: {repr prog}"
  | none      => IO.println "  (no counterexample found — unexpected)"
  if wf && occ && br then
    IO.println "All proven invariants confirmed over the bounded sample."
    return 0
  else
    IO.eprintln "A proven invariant failed the bounded check — investigate."
    return 1
