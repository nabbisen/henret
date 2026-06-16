import Henret.Conformance.Scenario
import Henret.Conformance.Golden
import Henret.Conformance.Export
import Henret.Conformance.Branch
import Henret.Conformance.Coverage
/-!
# Henret.Conformance  (RFC 047)

A golden-trace conformance suite.  External runtimes compare their
observed `TraceEvent` traces against Henret's canonical golden traces to
certify behavioral conformance.

## Exports

- `Henret.Conformance.GoldenScenario` — a named scenario with its golden trace.
- `Henret.Conformance.observe` / `checkScenario` / `scenarioReport` — run and check.
- `Henret.Conformance.TraceRefines` — the refinement relation (equality, v1).
- `Henret.Conformance.goldenScenarios` — the ten required scenarios.
- `Henret.Conformance.allPass` / `suiteReport` — the executable gate and report.
- `Henret.Conformance.conformance_suite_passes` — kernel-checked proof that
  every golden scenario matches (the regression gate).
- `Henret.Conformance.renderSuite` — human-readable rendering.

See `docs/conformance-suite.md` for the adapter contract.
-/
