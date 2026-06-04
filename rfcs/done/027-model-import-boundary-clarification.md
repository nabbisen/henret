---
title: Model Import Boundary Clarification
rfc: RFC-HENRET-027
status: Implemented (v0.3.1) — decision: light import (Option A)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-027: Model Import Boundary Clarification

## Motivation

RFC 025 claimed `import Henret.Model` was "the executable model with
nothing else." The v0.3.0 review showed this was overstated: the model
modules carry inline structural lemmas (`upd_self`/`upd_ne`,
`Mailbox.dequeue_spec`, the timer sortedness lemmas, `drain_completes`),
so the import avoids the heavy corpus under `Henret.Proofs` but is not
proof-free.

## Decision

**Option A — light import, documented honestly.** `Henret.Model` is the
light model import: the executable model plus the lightweight lemmas its
modules carry inline. The acceptance check is scoped accordingly: heavy
corpus theorems (`reachable_wf`, `receive_only_own`, ownership corollaries)
are absent after this import; inline lemmas are present by design.

The rationale for keeping lemmas inline: `upd_self`/`upd_ne` and
`Mailbox.dequeue_spec` are the modules' own specifications — splitting them
out would separate definitions from the facts that pin their meaning, hurt
locality, and force every consumer of the model to know about a second
module for basic rewriting. `drain_completes` is the driver's documented
contract.

**Option B — true definition/lemma split** (`Henret.Model` definitions
only, `Henret.ModelLemmas` for the inline lemmas) is recorded here as
possible future work if elaboration cost of the light import ever becomes a
measured problem. It is not justified at the current scale (~10 small
lemmas).

## Acceptance criteria

- [x] Import-persona documentation matches actual module contents
      (`Henret/Model.lean` docstring, handoff, RFC 025 context).
- [x] Examples and the demo use the intended import paths.
