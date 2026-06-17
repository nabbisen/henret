# Henret Roadmap

> Henret is a kernel-checked semantic ledger for execution management:
> every transition is executable, every safety claim is named,
> every trust boundary is explicit, and every bridge to native/runtime
> machinery is scoped by a relation.

## Current version: v0.27.0

The model is a total, executable transition system (`step` / `run`) with a
**33-field `WellFormed`** invariant proved to hold in every reachable state
(`reachable_wf`). The grammar is **28 `RuntimeOp` constructors** producing
**10 `StepResult` outcomes**. Capabilities now include:

- actor-scoped send/receive with message **envelope occurrence identity**;
- **parked receive** with mailbox wait queues and Mesa-style wake-one;
- **logical time**: sleep/timer wheel, `tick`, direct `wake`;
- **timeout-aware** and **selective** receive (`receiveUntil`,
  `receiveByOccurrence`, `receiveFrom`);
- actor-scoped **child spawn** and parent-chain acyclicity;
- **supervision**: `fail`, `restartOne`, cascade `cancelTree`;
- **structured shutdown**: `closeActor`, `shutdown`, `stopWhenIdle`;
- **bounded mailboxes / backpressure** (RFC 056);
- **scheduling policy layer** (RFC 058) and **deadline & priority** metadata
  with EDF/priority/hybrid policies (RFC 059);
- **fault & outcome taxonomy** (RFC 064);
- **resource lifetime & finalization ledger** (RFC 057): `acquire` / `release`
  / `finalize`, with `released` proved a terminal state;
- **drain-before-stop** for resources (RFC 087 `stopWhenDrained`) with
  single-step persistence (088), sleeping-timer coherence (089), and
  multi-step `Frozen` permanence (090);
- **actor-owned resources** (RFC 091): a `ResourceOwner = task | actor` ledger,
  `acquireActor`, and unified `Drained`.

The single-worker **queue-projection bridge** relates `readyQ` to the
lean-runtime worker-queue model. A conformance layer (golden traces + branch
coverage) and a release-gate / evidence-ledger discipline back every claim.

**73 RFCs are implemented** (`rfcs/done/`, through 091); **18 remain proposed**
(`rfcs/proposed/`, in the 060–079 range). The RFC 057 Tier 2 thread
(087–091) is complete except for the deferred items in *Known follow-ups*.

## Open backlog (RFCs 060–079, proposed)

Grouped by theme. 058, 059, and 064 from the original 058–079 band are now
**implemented** and have moved to `rfcs/done/`.

| Theme | RFCs |
|---|---|
| **Refinement / bridge / adapter** | 060 trace-based refinement cert · 061 runtime-adapter contract · 073 adapter negative tests · 074 bridge-completeness certificate · 065 semantic equivalence & bisimulation · 072 error/result observability contract |
| **Observability / replay** | 066 deterministic replay format · 067 state snapshot & semantic diff |
| **Proof engineering / governance** | 062 proof-ergonomics library · 068 invariant-dependency graph · 069 proof-dependency budget · 070 public-theorem API stability |
| **Architecture** | 063 long-term module architecture |
| **Model semantics** | 071 semantic profiles for actor models |
| **Pedagogy / publication** | 076 counterexample catalog · 077 minimal verified actor patterns · 078 security & robustness interpretation · 079 publication & community-review plan |

See `rfcs/README.md` for the authoritative status table.

## Prioritized sequence (cross-bucket)

This is the **single ranked queue** across both buckets — the remaining RFC 057
Tier 2 work and the open 060–079 proposals — so "what next?" has one answer
rather than two parallel lists. Ranking criteria, in order: (1) unblocks the
most downstream work, (2) lowest risk / highest certainty, (3) closes an
already-open thread before opening a new one. Breaking and paradigm-shift items
are **not** placed in the queue — they are gated (see *Known follow-ups*).

**Wave 1 — cheap completions & the recurring-cost reducer.**

1. **`releaseActor`** (new RFC 092, Tier 2) — manual release of actor-owned
   resources; closes the 057 lifecycle symmetry. No blocker, low risk, 1-op
   cascade. The one Tier 2 leftover that is ready to build. Only open question
   is the authorization model (who may release).
2. **RFC 062 — Proof Ergonomics Library** — preservation proofs are the
   recurring cost centre (the ~800-line `Lifecycle.lean`; every new op cascades
   through ~12 files). Helpers/simp-sets/tactics here pay off on *every*
   subsequent RFC, so it comes early.
3. **RFC 068 / 069 — Invariant-Dependency Graph & Proof-Dependency Budget** —
   proof-corpus hygiene that complements 062 over the 33-field `WellFormed` and
   the 200+ claim matrix; cheap and additive.

**Wave 2 — the bridge / adapter / refinement spine (the project's
"useful to runtimes" identity).**

4. **RFC 074 — Bridge-Completeness Certificate** — make the (still single-worker)
   bridge's coverage honest and machine-checkable; audits an existing layer.
5. **RFC 072 — Error/Result Observability Contract** then **RFC 065 — Semantic
   Equivalence & Bisimulation** — define observable behaviour and equivalence
   levels; prerequisites for 060/061/066/067/073.
6. **RFC 061 / 060 / 073 — Adapter Contract, Trace-Based Refinement Cert,
   Adapter Negative Tests** — the external-runtime conformance cluster; depends
   on 072/065.
7. **RFC 066 / 067 — Replay Format & Snapshot/Diff** — observability tooling
   built on 065/072.

**Wave 3 — public surface & governance (pre-publication).**

8. **RFC 070 — Public Theorem API Stability** — lock the surface once the above
   stabilise.
9. **RFC 063 — Long-Term Module Architecture** — v1.x modularity plan.
10. **RFC 071 — Semantic Profiles for Actor Models** — additive kernel
    extension; not blocking, so it floats here.

**Wave 4 — pedagogy & publication (end-stage).**

11. **RFC 076 / 077 / 078 / 079** — counterexample catalog, verified actor
    patterns, security interpretation, publication plan. Done last because they
    document a surface that should be stable first.

**Gated — not in the queue (need a decision/track, not a slot):**

- **Global `stopped → Drained` invariant** (Tier 2) — *blocked on an architect
  decision*. Making it global collapses `stopWhenIdle ≡ stopWhenDrained` and is
  a breaking change to `stopWhenIdle` semantics, conflicting with the additive
  philosophy that added `stopWhenDrained` as a separate op. Do not start until
  the break/merge question is answered.
- **Wall-clock liveness / timeliness** (Tier 2) — *separate research track*. All
  current claims are safety/possibility; liveness needs new model structure
  (a fairness/progress assumption and a real-time notion distinct from the
  logical `now`) and a trace/temporal proof style. Belongs in its own RFC line,
  not a Tier 2 slice.

## Known follow-ups

- **RFC 057 Tier 2** — the safety spine is **done**: drain-before-stop (087),
  single-step drained persistence (088), sleeping-timer coherence (089),
  multi-step `Frozen` permanence (090), and actor-owned resources (091).
  Remaining: **`releaseActor`** (queued as RFC 092 above), the **global
  `stopped → Drained`** invariant (gated on an architect decision), and any
  **liveness/timeliness** guarantee for finalization (separate track). See
  *Prioritized sequence* for placement.
- **Multi-worker bridge**: the bridge is single-worker; generalising to `n`
  workers needs a task-to-worker projection (kept out of the semantic kernel
  unless a theorem requires it). RFC 074 (bridge-completeness certificate)
  should pin the single-worker scope first.

## Standing guidance

- Keep worker assignment out of the semantic kernel unless a theorem needs it.
- Design wait/timer/resource composition before adding operations that combine
  them.
- Every new operation ships with: preservation across all `WellFormed` fields,
  per-branch behavioural theorems, conformance scenarios, an axiom-audit entry,
  and a migration note.
