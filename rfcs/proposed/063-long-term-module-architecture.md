---
rfc: 63
title: Long-Term Module Architecture
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [62, 68]
blocks: []
category: tooling
---

# RFC 063 — Long-Term Module Architecture

## Status

Proposed.

## Summary

Plan Henret v1.x modularity so the package can grow without becoming a monolith.

## Motivation

Henret now includes core model, proofs, refinement, bridge, native assumptions, examples, scripts, and external runtime relations. v1 needs a stable module architecture that separates learning imports, core imports, proof imports, bridge imports, and optional advanced profiles.

## Non-goals

- Do not perform the module split until public API impact is reviewed.
- Do not break existing import paths without deprecation aliases.
- Do not split modules merely by line count; split by user persona and semantic dependency.

## Design

Proposed architecture:

```text
Henret.Core          -- ids, result, basic state fragments
Henret.Model         -- full default executable model
Henret.Profile       -- semantic profiles
Henret.Proofs.Core   -- lifecycle + basic safety
Henret.Proofs.Actor  -- messaging + waiting + occurrence
Henret.Proofs.Time   -- timers + sleep/wake
Henret.Proofs.Supervision
Henret.Proofs.Policy
Henret.Bridge
Henret.Conformance
Henret.Native        -- optional assumptions only
Henret.Examples      -- opt-in only
```

Keep `import Henret` as stable kitchen-sink import for compatibility.

## Formal model changes

- Introduce new barrels first.
- Keep old imports as forwarding modules for at least one minor cycle.
- Update docs and examples gradually.

## Proof obligations

- Import smoke tests: each barrel imports exactly what it claims.
- Doc-symbol check per barrel.
- Axiom audit per barrel.

## Tests and examples

- Example: using only `Henret.Model`.
- Example: using `Henret.Proofs.Actor` without bridge/native.
- Example: bridge user import.

## Documentation updates

- Add module dependency diagram.
- Add import cost notes.
- Add deprecation policy.

## Acceptance criteria

- Stable import story exists.
- Examples do not import more than needed.
- Optional native assumptions remain opt-in.
- No hidden import of examples in library barrels.

## Risks and review questions

- Should v1 keep `Henret` as kitchen-sink or make it lightweight?
- How much backward compatibility is necessary before public release?
- Should bridge move to a separate package later?
