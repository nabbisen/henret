# Henret Roadmap

> Henret is a kernel-checked semantic ledger for execution management:
> every transition is executable, every safety claim is named,
> every trust boundary is explicit, and every bridge to native/runtime
> machinery is scoped by a relation.

## Current version: v0.19.x

The model is a total, executable transition system (`step` / `run`) with a
**33-field `WellFormed`** invariant proved to hold in every reachable state
(`reachable_wf`). The grammar is **24 `RuntimeOp` constructors** producing
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
- **resource lifetime & finalization ledger** (RFC 057): `acquire` / `release`
  / `finalize`, with `released` proved a terminal state.

The single-worker **queue-projection bridge** relates `readyQ` to the
lean-runtime worker-queue model. A conformance layer (golden traces + branch
coverage) and a release-gate / evidence-ledger discipline back every claim.

65 RFCs are implemented (`rfcs/done/`); 21 remain proposed (`rfcs/proposed/`).

## Open backlog (RFCs 058–079, proposed)

Grouped by theme; not yet sequenced into versions.

| Theme | RFCs |
|---|---|
| **Execution semantics** | 058 scheduling-policy layer · 059 deadline & priority |
| **Refinement / bridge** | 060 trace-based refinement cert · 061 runtime-adapter contract · 073 adapter negative tests · 074 bridge-completeness certificate |
| **Proof engineering / governance** | 062 proof-ergonomics library · 068 invariant-dependency graph · 069 proof-dependency budget · 070 public-theorem API stability |
| **Architecture** | 063 long-term module architecture |
| **Fault / equivalence / replay** | 064 fault model & failure taxonomy · 065 semantic equivalence & bisimulation · 066 deterministic replay format · 067 state snapshot & semantic diff |
| **Maturity / publication** | 071 semantic profiles · 072 error/result observability · 076 counterexample catalog · 077 minimal verified actor patterns · 078 security & robustness interpretation · 079 publication & community-review plan |

See `rfcs/README.md` for the authoritative status table.

## Known follow-ups

- **RFC 057 Tier 2** (not yet an RFC): drain-before-stop discipline,
  actor-owned (longer-lived) resources, and any liveness/timeliness guarantee
  for finalization — all explicitly out of scope in Tier 1.
- **Multi-worker bridge**: the bridge is single-worker; generalising to `n`
  workers needs a task-to-worker projection (kept out of the semantic kernel
  unless a theorem requires it).

## Standing guidance

- Keep worker assignment out of the semantic kernel unless a theorem needs it.
- Design wait/timer/resource composition before adding operations that combine
  them.
- Every new operation ships with: preservation across all `WellFormed` fields,
  per-branch behavioural theorems, conformance scenarios, an axiom-audit entry,
  and a migration note.
