---
title: Documentation and Public Claim Repair
rfc: RFC-HENRET-026
status: Implemented (v0.3.1)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-026: Documentation and Public Claim Repair

## Motivation

The v0.3.0 review approved the architecture of RFC 019–025 but blocked
public tagging on five claim/documentation drifts (RB-01..05) and two
wording should-fixes. For a project whose identity is explicit
proof/trust/test boundaries, stale claims matter more than in an ordinary
prototype.

## Changes

- **RB-01** — `send_preserves_tasks` / `receive_preserves_tasks` (removed by
  RFC 024) replaced in the proof index and matrix with the
  `Henret.Proofs.StepProjections` lemma family.
- **RB-02** — guided tour now shows the eleven-operation grammar
  (`send t b m`, `receive t`, `inject a m`) and presents
  `receive_only_own` as the actor-local receive theorem.
- **RB-03** — `Henret/Actor/Mailbox.lean` no longer claims positional
  exact-one message ownership; reworded to per-operation value semantics
  per the reviewer's recommended text. Matrix row 7 scoped likewise.
- **RB-04** — `Henret.Model` honestly documented as a *light* model import
  (carries inline structural lemmas; excludes the heavy proof corpus); the
  handoff corrected. Boundary decision recorded in RFC 027.
- **RB-05** — `lakefile.lean` comment no longer claims examples are in the
  root import.
- **SF-04** — `Op.lean` send docstring carries a PROVENANCE NOTE: guards
  give *existence* provenance, not message provenance; envelopes are
  future work (RFC 022 path).
- **SF-05** — gate 6 forbidden-phrase list extended (stale theorem names,
  backticked old grammar, "five #eval"); **gate 7 added**:
  `scripts/doc_symbol_check.py` extracts backticked theorem names from the
  proof docs and `#check`s each — stale names become build failures.

## Acceptance criteria

- [x] No `send_preserves_tasks`/`receive_preserves_tasks` references in
      live docs.
- [x] No pre-RFC-024 grammar outside historical RFC/review context.
- [x] All backticked theorem names in proof docs resolve (gate 7: 99/99).
- [x] Seven-gate release script green.
