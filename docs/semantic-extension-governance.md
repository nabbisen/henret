# Semantic Extension Governance

Henret's value is precision. As the semantic core evolves, this policy
keeps theorem, documentation, and bridge claims from drifting apart. It
governs **public claims and semantic-core changes only** — private
experiments need none of this.

## Semantic-core files

A change to any of these files is a *semantic-core change* and requires
the Semantic Impact Checklist (below) in its RFC:

```text
Henret/Scheduler/Op.lean              -- the RuntimeOp grammar
Henret/Scheduler/Model.lean           -- RuntimeState + step + run
Henret/Core/Result.lean               -- StepResult
Henret/Actor/Task.lean                -- TaskState
Henret/Actor/Mailbox.lean             -- Envelope, Mailbox
Henret/Proofs/Invariants.lean         -- WellFormed + RestartWellFormed
Henret/Proofs/InvariantsPreservation.lean
Henret/Bridge/*                       -- the bridge layer
```

Changes elsewhere (renderers, examples, docs, tooling, new derived
theorems that do not touch the core) are ordinary and need no checklist.

## Semantic Impact Checklist

Every semantic-core RFC must answer these ten questions explicitly. The
checklist is mirrored in `rfcs/TEMPLATE.md` so new RFCs carry it.

1. **Public types** — what changes in `RuntimeOp` / `RuntimeState` /
   `StepResult` / `TaskState` / `Envelope`?
2. **Step branches** — which `step` cases are added or altered?
3. **WellFormed fields** — which invariant fields are added, removed, or
   strengthened (base `WellFormed` *and* `RestartWellFormed`)?
4. **Preservation cases** — which `preserves_wf_*` / dispatch arms change?
5. **Examples** — which `examples/NN_*.lean` must change?
6. **Bridge translation** — what changes in `toQOps` and the
   `bridge_*` theorems?
7. **Trace events** — which `TraceEvent` constructors are added or
   changed?
8. **Matrix entries** — which `proof-trust-test-matrix.md` rows change,
   and how are new claims classified?
9. **Migration note** — what `docs/migration/` note is required (every
   grammar change needs one, even additive)?
10. **Stale phrases** — which old phrase(s) should the stale-phrase gate
    now ban?

An RFC that touches a semantic-core file without answering these is not
ready to merge.

## Theorem stability levels

Public theorems carry a stability level, documented in
`docs/proof-index.md` (not as Lean attributes):

- **Stable** — the headline reachability contract. These names are
  promised to remain, or to deprecate with a one-release alias. New work
  builds on them.
- **Experimental** — may change name or shape between minor versions.
  Newer layers whose form is still settling (bridge, restart provenance,
  progress, conformance, trace soundness).
- **Internal** — no public stability. Step-local lemmas, preservation
  lemmas, projections, helpers. Consumers should not depend on these
  directly.

The current classification lives in
[`docs/proof-index.md` § Stability](proof-index.md#theorem-stability).

## Deprecation rule

When a public theorem is renamed, keep a compatibility alias for one
release where reasonable:

```lean
/-- Deprecated: use `new_name`. -/
theorem old_name := new_name
```

Do **not** keep an alias that obscures a *semantic* change — if the
meaning changed, the old name should be removed, not aliased, so
consumers are forced to re-read the new statement.

## Bridge claim rule

No bridge RFC, theorem docstring, or release note may describe the bridge
as **"complete"** unless every operation with a `readyQ` effect is either
covered by a `bridge_*` theorem or *explicitly excluded in the headline*.
The current bridge is a **single-worker** projection; that qualifier is
mandatory wherever completeness is claimed. The honest framing is
"single-worker bridge", not "the bridge".

## Stale-phrase registration

The stale-phrase gate (gate 8 of `scripts/check.sh`) bans superseded
phrasings so docs cannot silently retain a claim the model has outgrown.
To register a new banned phrase:

1. Add the exact phrase to the gate's `grep` pattern in
   `scripts/check.sh`, in the block for the RFC that supersedes it.
2. Note the phrase and its replacement in the RFC's checklist answer #10.
3. Confirm no live doc still contains it (the gate will fail the build if
   one does).

Banned phrases are never un-banned: once a claim is superseded, its old
wording stays prohibited.

## What this is not

This is not bureaucracy for research. It constrains only public claims
and the eight semantic-core files. Everything else — new renderers, new
examples, new derived theorems, tooling — proceeds without a checklist.
The goal is to make semantic extension *predictable*, not slow.
