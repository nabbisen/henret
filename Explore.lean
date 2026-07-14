import Henret.Explore
/-!
# Bounded model explorer entry point (RFC 048)

Confirms the proven invariants over a bounded sample and demonstrates
counterexample shrinking on a deliberately false property.  Build/run:

    lake exe henret-explore

This is empirical model-search support, **not** a proof. Defaults are tiny to
keep the search bounded. The world bounds and depth may be overridden through
the `HENRET_EXPLORE_*` environment variables; selected values are printed.
-/
open Henret.Explore

def readBound (name : String) (fallback : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | none => pure fallback
  | some raw =>
      match raw.toNat? with
      | some value => pure value
      | none => throw <| IO.userError s!"{name} must be a natural number, got {raw}"

def reportProperty (depth : Nat) (name : String) (holds : Bool) : IO Unit :=
  if holds then IO.println s!"  CONFIRMED  {name} holds over all programs up to depth {depth}"
  else IO.println s!"  VIOLATED   {name} has a counterexample"

def main : IO UInt32 := do
  let maxTask ← readBound "HENRET_EXPLORE_MAX_TASK" 2
  let maxActor ← readBound "HENRET_EXPLORE_MAX_ACTOR" 2
  let maxMsg ← readBound "HENRET_EXPLORE_MAX_MSG" 1
  let maxTime ← readBound "HENRET_EXPLORE_MAX_TIME" 2
  let depth ← readBound "HENRET_EXPLORE_DEPTH" 3
  let world : SmallWorld := { maxTask, maxActor, maxMsg, maxTime }
  let programCount := (genPrograms world depth).length
  IO.println "Henret bounded model explorer (RFC 048)"
  IO.println "========================================"
  IO.println s!"world = {repr world}, depth = {depth}, programs = {programCount}"
  IO.println "Confirming proven invariants over the bounded sample:"
  let wf  := confirms world depth propWellFormed
  let occ := confirms world depth (propOccurrenceUnique world)
  let br  := confirms world depth propBridge
  reportProperty depth "well-formedness (bounded structural)" wf
  reportProperty depth "occurrence uniqueness (bounded)" occ
  reportProperty depth "single-worker bridge tracking" br
  IO.println "Shrinking a deliberately false property (readyQ always empty):"
  let shrunk := findAndShrink world depth propReadyAlwaysEmpty
  let counterexampleFound := shrunk.isSome
  let counterexampleFails := match shrunk with
    | some prog => !propReadyAlwaysEmpty prog
    | none => false
  let counterexampleMinimal := decide (shrunk = some [Henret.RuntimeOp.spawn 0])
  match shrunk with
  | some prog => IO.println s!"  minimal counterexample: {repr prog}"
  | none      => IO.println "  (no counterexample found — unexpected)"
  -- RFC 103 machine-readable result. scripts/explorer_result.py is the sole
  -- parser and derives retained manifest evidence from this executed line.
  IO.println <| "HENRET_EXPLORER_RESULT " ++
    "{\"schema\":1,\"world\":{\"maxTask\":" ++ toString maxTask ++
    ",\"maxActor\":" ++ toString maxActor ++ ",\"maxMsg\":" ++ toString maxMsg ++
    ",\"maxTime\":" ++ toString maxTime ++ "},\"depth\":" ++ toString depth ++
    ",\"program_count\":" ++ toString programCount ++
    ",\"well_formed\":" ++ toString wf ++
    ",\"occurrence_unique\":" ++ toString occ ++
    ",\"bridge\":" ++ toString br ++
    ",\"counterexample_found\":" ++ toString counterexampleFound ++
    ",\"counterexample_fails\":" ++ toString counterexampleFails ++
    ",\"counterexample_minimal\":" ++ toString counterexampleMinimal ++ "}"
  if wf && occ && br && counterexampleFound && counterexampleFails && counterexampleMinimal then
    IO.println "All proven invariants confirmed over the bounded sample."
    return 0
  else
    IO.eprintln "Explorer evidence contract failed — investigate."
    return 1
