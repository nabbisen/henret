import Henret.Explore.Gen
import Henret.Explore.Check
import Henret.Explore.Shrink
/-!
# Henret.Explore  (RFC 048)

A bounded model explorer and shrinker.  Enumerates small `RuntimeOp`
sequences, checks executable property predicates, and minimizes
counterexamples by deletion.

**This is a development/testing tool, not part of the verified model.**
It lives in the separate `HenretExplore` Lake library, outside the
default `import Henret` path.  The checkers are bounded necessary
conditions (testing-only), deliberately not connected to soundness
theorems — they confirm the proven invariants over a bounded sample and
catch regressions; they never substitute for `reachable_wf` et al.

## Exports

- `Henret.Explore.SmallWorld`, `genOps`, `genPrograms` — the generator.
- `Henret.Explore.checkWellFormedBool`, `checkOccUniqueBool`,
  `checkBridgeBool` — bounded checkers; `propWellFormed`,
  `propOccurrenceUnique`, `propBridge`, `propReadyAlwaysEmpty` — properties.
- `Henret.Explore.explore`, `confirms`, `shrinkProgram`, `findAndShrink`
  — search and minimization.

See `docs/model-explorer.md`.
-/
