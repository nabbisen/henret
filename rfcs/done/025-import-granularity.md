---
rfc: 25
title: Import Granularity
status: Implemented
implemented_in: v0.3.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: tooling
---

# RFC-HENRET-025: Import Granularity

## Motivation

`import Henret` pulled in every proof, both refinement modules, and the
example scenarios. The v0.2.0 review flagged this: users who only want to
run the model should not elaborate the whole proof corpus, and examples
should not be part of the default library import forever.

## Design

Three barrels plus a trimmed root:

```lean
import Henret.Model       -- executable model only (Core/Actor/Scheduler)
import Henret.Proofs      -- model + every theorem
import Henret.Refinement  -- MailboxBackend contract + reference backend
import Henret             -- Model + Proofs + Refinement (no Examples)
```

`Henret.Examples.Basic` is opt-in; the demo executable imports it
explicitly. `Henret.Native.*` remains opt-in as before (RFC 010).

## Acceptance criteria

- [x] `import Henret.Model` elaborates no proof module.
- [x] `import Henret` no longer includes examples.
- [x] Demo and all examples still build.
