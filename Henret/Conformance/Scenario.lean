import Henret.Trace
/-!
  # Henret.Conformance.Scenario  (RFC 047)

  A golden-trace conformance scenario: a named operation sequence with the
  canonical `TraceEvent` list Henret produces for it.  External runtimes
  compare their observed traces against these golden traces to certify
  behavioral conformance.

  The expected trace is the model's own canonical output.  Checking it in
  serves two purposes: (1) it is a regression gate — any change to `step`
  or `traceEvents` that alters observable behavior is caught; (2) it is
  the reference an external adapter compares against.
-/
namespace Henret.Conformance

open Henret Henret.Trace

/-- A golden conformance scenario. -/
structure GoldenScenario where
  /-- Stable scenario identifier. -/
  name        : String
  /-- One-line human-readable purpose. -/
  description : String
  /-- The operation sequence driving the scenario. -/
  ops         : List RuntimeOp
  /-- The canonical event trace Henret produces. -/
  expected    : List TraceEvent
  /-- Starting state (default: the empty initial state). -/
  initial     : RuntimeState := RuntimeState.init

/-- The trace Henret actually produces for a scenario. -/
def observe (sc : GoldenScenario) : List TraceEvent :=
  (runTraceLedger sc.initial sc.ops).2.2

/-- Trace refinement.  The first version is exact equality; relaxed
    variants (e.g. permitting legitimate reorderings on multi-worker
    runtimes) can be added when a real integration needs them
    (see RFC 047 §Refinement relation). -/
def TraceRefines (expected observed : List TraceEvent) : Prop :=
  expected = observed

instance (expected observed : List TraceEvent) :
    Decidable (TraceRefines expected observed) :=
  inferInstanceAs (Decidable (expected = observed))

/-- A scenario passes when Henret's observed trace equals its golden
    expected trace. -/
def checkScenario (sc : GoldenScenario) : Bool :=
  observe sc == sc.expected

/-- The index and the (expected, observed) pair of the first event that
    differs, or `none` if the traces agree up to the shorter length and
    have equal length. -/
def firstMismatch (expected observed : List TraceEvent) :
    Option (Nat × Option TraceEvent × Option TraceEvent) :=
  let rec go (i : Nat) : List TraceEvent → List TraceEvent →
      Option (Nat × Option TraceEvent × Option TraceEvent)
    | [],      []      => none
    | e :: es, o :: os => if e == o then go (i + 1) es os
                          else some (i, some e, some o)
    | e :: _,  []      => some (i, some e, none)
    | [],      o :: _  => some (i, none, some o)
  go 0 expected observed

/-- A human-readable pass/fail report for a scenario. -/
def scenarioReport (sc : GoldenScenario) : String :=
  if checkScenario sc then
    s!"PASS  {sc.name}  ({sc.description})"
  else
    match firstMismatch sc.expected (observe sc) with
    | some (i, e, o) =>
        s!"FAIL  {sc.name}  first mismatch at event {i}: expected {repr e}, observed {repr o}"
    | none =>
        s!"FAIL  {sc.name}  (length mismatch)"

end Henret.Conformance
