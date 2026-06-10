# RFC 051 — Package, Documentation, and Release Maturity

## Status

Implemented (v0.15.2).

## Summary

Prepare Henret for a polished public ecosystem release. This RFC is about
library character, not new semantics: stable imports, examples, changelog policy,
release gates, documentation structure, and user-facing claims.

## Motivation

Henret is no longer a small experiment. It has a public identity, substantial
proof corpus, bridge work, and ecosystem value. A sophisticated Lean package
needs reliable packaging and documentation habits:

- predictable import barrels;
- examples that do not break user code;
- release notes that distinguish semantics from docs;
- theorem names that are discoverable;
- assumption budget that remains auditable;
- clear migration notes for grammar changes.

## Non-goals

This RFC does not:

- add new model operations;
- require publishing to any specific registry in this RFC;
- promise API stability before RFC 052 governance is accepted;
- optimize elaboration performance beyond import hygiene.

## Proposed design

### Import tiers

Confirm or refine these tiers:

```lean
import Henret.Model       -- executable model, light theorem specs acceptable
import Henret.Proofs      -- all proof modules
import Henret.Refinement  -- backend contracts
import Henret.Bridge      -- bridge layer
import Henret.Trace       -- trace/event layer, after RFC 045
import Henret             -- full public package barrel
```

Examples remain opt-in.

### Documentation structure

```text
docs/
  getting-started.md
  guided-tour.md
  proof-trust-test-matrix.md
  proof-index.md
  assumption-index.md
  bridge-guide.md
  conformance-guide.md
  release-policy.md
  migration/
    v0.8-to-v0.9.md
```

### Release checklist

Add `docs/release-checklist.md`:

```text
- build passes
- demo passes
- doc symbol check passes
- axiom audit passes
- no stale phrase gate violations
- proof matrix updated
- changelog updated
- migration notes updated if grammar changed
- archive contains no generated junk
```

### Versioning discipline

Until RFC 052, use conservative versioning:

- patch: docs, tests, non-public helper lemmas;
- minor: new theorem, new example, additive module;
- breaking minor or major: `RuntimeOp`, `RuntimeState`, `StepResult`, theorem rename.

## Implementation tasks

1. Audit import barrels.
2. Move examples out of any default imports if any remain.
3. Create release checklist.
4. Create migration notes template.
5. Create theorem naming style guide.
6. Create docs index landing page.
7. Add CI script that runs all local gates in one command.
8. Add package metadata review: license, description, repository URL placeholder, keywords.
9. Add changelog policy.

## Acceptance criteria

- A new user can build and run the demo from README alone.
- A proof user can find theorems from `docs/proof-index.md`.
- A maintainer can run one script to execute all gates.
- Grammar changes require migration notes.
- Release claims are classified by proof/trust/test status.

## Risks

Documentation work can expand endlessly. Keep this RFC focused on release
maturity, not a full book.
