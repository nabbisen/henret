---
rfc: 81
title: Package Boundary and Evidence Ledger
status: Implemented
implemented_in: v0.17.3
supersedes: []
superseded_by: []
depends_on: [80]
blocks: []
category: governance
---

# RFC 081 — Package Boundary and Evidence Ledger

## Status

Implemented in **v0.17.3**. Approved in the v0.17.0 audit review (item A5,
decision **A — intended split**, priority **P0 — blocks public ledger
claims**); amendments 081-A..C and the v2-review final-pass amendments
081-1..4 applied. Delivered: `docs/evidence-ledger.yaml` (machine-readable
source of truth), its generated `docs/evidence-ledger.md`,
`docs/package-boundary.md`, the evidence-location columns on the proof matrix,
the honesty-ledger wording in the README, and
`scripts/forbidden_claim_check.py` (ledger validation + forbidden-claim gate)
wired into the RFC 080 doc-consistency gate. The RFC 080 manifest's
`runtime_package` block now references the ledger.

## Summary

Make Henret's honesty ledger truthful about *where* each piece of evidence
lives. The concrete runtime (`lean-runtime-workspace`: the C Chase-Lev
backend plus the differential / linearizability / stress harnesses) is a
separately versioned sibling package, not part of the model-package
checkout or its release tarball. Provide a machine-readable evidence
ledger that distinguishes in-tree model evidence from out-of-tree runtime
evidence, distinguishes *trusted* from *tested-out-of-tree*, and a doc gate
that forbids implying this tarball verifies the `runtimeTests` tier.

## Motivation

The v0.17.0 audit found that `lean-runtime-workspace` is absent from the
model checkout, so several matrix rows classified `TESTED` (the concurrent
harnesses) and parts of the FFI story cannot be verified from the released
artifact. Henret's core value is its honesty discipline; a ledger that
asserts evidence not present in the artifact undercuts exactly that value.

## Decision

Default to the **intended split**: Henret is a pure Lean semantic-reference
package; the runtime is a clean sibling package. (If the project instead
chooses a monorepo, restore `lean-runtime-workspace` as a workspace member
and have CI build and test both — not recommended, as it weakens the
Lean-only identity and lets native assumptions contaminate the model.)

The model's claims are **not** weakened by the split. The model can remain
public-quality; the ledger only stops *implying* that out-of-tree runtime
tests were run by the model-package tarball.

## Goals

- Every claim states its evidence *location*, machine-readably.
- *Trusted* (C/FFI design) is never collapsed with *tested-out-of-tree*.
- A doc gate blocks claims that imply in-tree runtime verification.

## Non-goals

- Re-homing or deleting the runtime package.
- Changing any proven theorem or trusted axiom.
- Weakening model-package claims.

## 081-A — Machine-readable evidence ledger

A structured ledger (`docs/evidence-ledger.md` with a generated/checked
data source), not prose alone. Per-claim record:

```yaml
claim_id: runtime.linearizability
claim: Concurrent histories pass the Wing-Gong checker
tier: TESTED
evidence_location: sibling_runtime_package
package: lean-runtime-workspace/lean-runtime
version_or_commit: null
verified_by_this_tarball: false
verified_by_ci: false
notes: Not present in the henret model-package tarball.
```

RFC 080's manifest links to this ledger.

## 081-B — Tier and location vocabulary (closed)

```text
tier:               PROVEN | TRUSTED | TESTED | OUTSCOPE | PLANNED
evidence_location:  in_tree_model_proof | in_tree_model_test
                    | sibling_runtime_package | external_artifact | planned
verified_by_this_tarball: true | false
verified_by_ci:           true | false
external_version:         optional
```

`TRUSTED` (e.g. the C/FFI sequential-spec axioms) and `TESTED`
(empirical out-of-tree harnesses) are distinct tiers and must not be merged.

## 081-C — Forbidden-claim gate

A doc check rejects phrasing such as:

```text
this release verifies runtimeTests | runtimeTests pass | all runtime tests pass
```

unless the runtime package is actually included in the release manifest and
`verified_by_ci: true`. Allowed posture:

```text
"Runtime evidence exists in a separately versioned package and is not
 verified by this tarball's gates."
```

## Deliverables

```text
docs/evidence-ledger.yaml          SOURCE OF TRUTH (081-1)
docs/evidence-ledger.md            generated/checked rendering of the YAML
docs/package-boundary.md           what is in this package vs the sibling
docs/proof-trust-test-matrix.md    add the evidence-location column
README.md                          honesty-ledger wording update
scripts/forbidden_claim_check.py   the 081-C gate (runs in RFC 080 stage 9)
release/release-verification.json  runtime_package scope block (RFC 080)
```

## Final-pass amendments (RFCs 080-086 v2 review)

**081-1 — Machine-readable source first.** The source of truth is
`docs/evidence-ledger.yaml`; `docs/evidence-ledger.md` is a generated or
checked rendering. Markdown is never the primary ledger.

**081-2 — Immutable external coordinates or explicit null.** A claim with
`evidence_location: sibling_runtime_package` must carry either
`external_version`/`external_commit` + `verified_by_ci: true`, or an
explicit null posture (`external_version: null`, `external_commit: null`,
`verified_by_ci: false`, plus a `notes:` line). No vague external evidence.

**081-3 — `claim_id` is stable, namespaced API.** e.g. `model.reachable_wf`,
`model.occurrence_unique`, `native.deque_axioms`, `runtime.linearizability`,
`runtime.stress_partition`. Renaming a `claim_id` is treated as a
documentation/API migration.

**081-4 — Forbidden phrases are examples, not the whole rule.** The
forbidden-claim checker combines: a forbidden-phrase list + allowed-context
patterns + evidence-ledger validation — so it stops phrase whack-a-mole.

## Acceptance criteria

```text
- docs/evidence-ledger.yaml is the source of truth; the .md is generated/checked.
- Every matrix row carries tier + evidence-location + verified_by_this_tarball.
- TRUSTED and TESTED are never collapsed.
- Out-of-tree claims carry immutable coordinates or an explicit null posture.
- claim_id values are stable and namespaced.
- The forbidden-claim gate = phrase list + allowed-context + ledger validation,
  and runs as an RFC 080 stage-9 check.
- package-boundary.md enumerates both packages and their toolchain link.
```

## Priority and sequencing

P0. Per the v2 review's order, RFC 081 lands **fourth** (after 085, 084
stopgap, 080). 080 records *that* gates ran; 081 records *where* the
evidence lives, and the 081-C forbidden-claim gate runs as an RFC 080
stage-9 check.

## References

- v0.17.0 audit review item A5 and additional recommendation 2.
- RFC 009 (proof/trust/test matrix), RFC 010 (optional FFI boundary),
  RFC 053 (assurance case).
