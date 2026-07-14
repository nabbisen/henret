# Henret Roadmap

> Henret is a kernel-checked semantic ledger for execution management: every
> transition is executable, every safety claim is named, every trust boundary
> is explicit, and every bridge to native/runtime machinery is scoped by a
> relation.

## Planning baseline

The current release is **v0.34.5**. The repository contains 80 implemented,
24 proposed, and 1 archived RFC. The model currently has 29 `RuntimeOp`
constructors, 10 `StepResult` outcomes, and a 33-field `WellFormed` invariant.
The bridge covers both exact single-worker projection and multi-worker
membership projection.

The architect review of the v0.34.5 preparation work is **No-Go** for another
release or semantic feature cycle. Milestone M1 below is therefore the only
active release track. Later milestones are ordered backlog, not authorization
to start around M1.

## Milestone schedule

| Milestone | Release target | Theme | RFCs | Exit condition |
|---|---|---|---|---|
| **M0 — Planning baseline** | current | Convert review findings into owned work | 098–104 | Roadmap, RFC metadata, and indexes agree on scope and order |
| **M1 — Release integrity** | **v0.34.6** | Repair the release and evidence boundary without semantic expansion | 098–103 | Every blocking review finding is closed; the patch release is produced only from the repaired gates |
| **M2 — Maintainability and policy** | v0.35 candidate | Reduce proof cost, settle module/API policy, pin CI inputs | 062, 068, 063, 070, 104 | The large proof modules have an agreed decomposition, public API policy is explicit, and CI inputs are immutable |
| **M3 — Bridge contract spine** | v0.36 candidate | State precisely what the bridge and adapter preserve | 074 → 072 → 065 | Coverage, observability, and equivalence contracts are machine-checkable |
| **M4 — External conformance** | v0.37 candidate | Connect external runtimes to the semantic contracts | 061 → 060 → 073 and 066 → 067, in parallel after 065 | Adapter, certificate, negative-test, replay, and semantic-diff evidence share one observable contract |
| **M5 — Profiles and publication** | v0.38+ candidate | Extend and explain a stable surface | 071, 076, 077, 078, 079 | Profiles are governed and publication material describes the stabilized API and evidence |

Only v0.34.6 is a committed release boundary. Later version labels are
planning candidates and may move when their RFCs are accepted.

## M1 — v0.34.6 release-integrity critical path

M1 is a patch milestone: it changes release construction, verification, and
documentation, but does not add a runtime operation or broaden a semantic
claim.

1. **Artifact boundary — RFC 098.** Build source archives from a tracked-file
   allowlist and prove ignored/untracked local material cannot enter them.
2. **Publication immutability — RFC 099.** Reject an existing release/tag/asset
   instead of replacing it with `--clobber`.
3. **Trust-scope repair — RFC 100.** Remove the three `native_decide` proof
   shortcuts, enforce the package-wide axiom policy, and document its scope.
4. **Documentation integrity — RFC 101.** Make the root RFC index, generated
   book index, roadmap, test inventory, risk register, and release claims
   mechanically consistent.
5. **Gate unification — RFC 102.** Make demo, conformance, documentation, and
   timeout behavior mandatory release-core checks; align tag and exact-commit
   rules in contributor and release documentation.
6. **Evidence binding — RFC 103.** Execute the explorer as a bounded named gate
   and permit “CI verified” claims only when evidence names a gate that ran.

RFCs 098–101 may be implemented in parallel after acceptance. RFC 102 consumes
their gate and documentation contracts; RFC 103 follows RFC 102. The milestone
closes only when all six RFC acceptance criteria pass from a clean checkout at
the exact candidate commit. A new v0.34.6 sidecar is then generated; the
v0.34.5 evidence record is never rewritten.

### Review-finding ownership

| Architect finding | Owning RFC | Required result |
|---|---|---|
| B01: archive includes ignored/untracked content | 098 | Tracked allowlist plus archive self-test |
| B02: published assets are mutable | 099 | Fail-closed, immutable publication |
| B03: `native_decide` widens the trust boundary | 100 | Package-wide axiom policy and enforcement |
| B04: roadmap/RFC/docs contradict repository state | 101 | Generated or checked current indexes and claims |
| B05: release docs and workflow triggers disagree | 102 | One release-core contract, exact candidate commit |
| B06: explorer is claimed but not executed | 103 | Named bounded explorer gate and evidence binding |
| B07: demo/conformance are optional | 102 | Required blocking release-core gates |
| Supply-chain inputs are mutable | 104 (M2) | Immutable action/tool references and metadata |

## M2 — maintainability and policy

M2 starts only after v0.34.6 is complete. Its order is:

1. Finish RFC 062 proof ergonomics and RFC 068 invariant-dependency work.
2. Complete RFC 063 before introducing another runtime operation; use it to
   split the large lifecycle and claim modules along reviewed boundaries.
3. Resolve RFC 070's public-theorem/API policy against the resulting module
   surface.
4. Implement RFC 104 CI supply-chain pinning before any publication milestone.

This milestone deliberately carries no new semantic operation. It addresses
the review's maintainability warning before the bridge/adapter work expands the
proof surface.

## M3–M5 dependency spine

The remaining proposals are sequenced by contract dependency:

```text
074 bridge completeness
  -> 072 observable result/error contract
    -> 065 semantic equivalence
      -> 061 adapter contract -> 060 refinement certificate -> 073 negative tests
      -> 066 replay format -> 067 snapshot and semantic diff

070 stable public API
  -> 071 semantic profiles
  -> 076 counterexamples / 077 patterns / 078 security interpretation
    -> 079 publication and community review
```

RFC 104 must also be complete before RFC 079. Each milestone must update this
roadmap and RFC metadata if an accepted RFC changes these edges.

`depends_on` is the authoritative scheduling relation. `blocks` is an optional
forward-navigation hint, but every declared `A blocks B` edge must have the
inverse `B depends_on A` edge. The RFC metadata gate enforces that invariant.

## Deferred research tracks and settled boundaries

These items have no release slot and must not be smuggled into an implementation
RFC:

- RFC 092 settled the `stopped → Drained` question: the global invariant was
  rejected, and `CleanStopped`/`StoppedDrained` carry the stronger claim. Any
  proposal to reopen that decision is a breaking-change RFC, not backlog work.
- Wall-clock liveness/timeliness requires fairness, real-time, and temporal
  proof machinery distinct from the current logical-time safety model. It
  needs a separate research RFC before scheduling.
- Worker assignment remains outside the semantic kernel unless a theorem
  requires it. RFC 074 must first pin the exact scope of both bridge modes.

## Scheduling rules

- A release milestone is complete only when its RFC acceptance criteria and
  required named gates pass at the exact release commit.
- The v0.34.6 release decision must explicitly accept the residual risk that
  movable CI action/tool inputs remain until RFC 104 closes in M2.
- New operations wait until M1 and M2 close.
- Every new operation ships with preservation across all `WellFormed` fields,
  per-branch behavior theorems, conformance scenarios, an axiom-audit entry,
  and a migration note.
- Timeouts in blocking release checks fail the gate; they are never interpreted
  as a skip.
- RFC status, dependency metadata, the root index, the generated book index,
  and this roadmap must change together.
