import Henret.Conformance
/-!
# Conformance checker entry point (RFC 047)

Runs the golden trace conformance suite, prints a per-scenario report, and
exits non-zero if any scenario fails.  Build and run with:

    lake exe henret-conformance
-/
open Henret.Conformance

def main : IO UInt32 := do
  IO.println "Henret golden conformance suite (RFC 047 traces + RFC 083 branches)"
  IO.println "===================================================================="
  IO.println suiteReport
  IO.println "--- branch coverage (RFC 083) ---"
  IO.println branchReport
  IO.println "--- coverage registry (RFC 083) ---"
  IO.println coverageReport
  IO.println "--------------------------------------------------------------------"
  if allPass && branchAllPass && coverageComplete then
    IO.println s!"ALL PASSED: {goldenScenarios.length} trace + {branchScenarios.length} branch scenarios; coverage complete"
    return 0
  else
    if !allPass then IO.eprintln "CONFORMANCE FAILURE: a trace scenario did not match"
    if !branchAllPass then IO.eprintln "CONFORMANCE FAILURE: a branch scenario did not match"
    if !coverageComplete then IO.eprintln "CONFORMANCE FAILURE: branch coverage is incomplete"
    return 1
