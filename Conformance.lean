import Henret.Conformance
/-!
# Conformance checker entry point (RFC 047)

Runs the golden trace conformance suite, prints a per-scenario report, and
exits non-zero if any scenario fails.  Build and run with:

    lake exe henret-conformance
-/
open Henret.Conformance

def main : IO UInt32 := do
  IO.println "Henret golden trace conformance suite (RFC 047)"
  IO.println "================================================"
  IO.println suiteReport
  IO.println "------------------------------------------------"
  if allPass then
    IO.println s!"ALL {goldenScenarios.length} SCENARIOS PASSED"
    return 0
  else
    IO.eprintln "CONFORMANCE FAILURE: at least one scenario did not match"
    return 1
