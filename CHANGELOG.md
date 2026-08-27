# Changelog

## v0.34.6 — Release integrity: RFCs 098–104 (M1 close)

Patch milestone closing the roadmap's M1 "release integrity" track. No Lean
API, operation, theorem, profile, manifest schema, or publication-naming
change; the model, proofs, and public theorem surface (101 names) are
unchanged. This is a release-construction, verification, and documentation
release, per the architect's roadmap: v0.34.5's preparation review found the
release, evidence, and CI-input boundary needed repair before another
semantic feature cycle. RFCs 098–104 close that gap and move to
`rfcs/done/`; this entry summarizes what shipped in the commits since v0.34.5
and the version-transition patch that closes it out.

- **RFC 098 — Tracked source archive boundary.** The canonical release
  tarball is built from an explicit Git-tracked-file allowlist, not the
  working directory with a growing exclude list, so ignored/untracked local
  material cannot enter a release artifact. A project-owned archive-boundary
  self-test and deterministic tar/gzip serializer (own byte layout, not the
  system `tar`) make the archive reproducible independent of the local Git
  version — root-caused after a Git 2.54.0-vs-2.55.0 tar-layer divergence
  could not be proved equal after the fact.
- **RFC 099 — Frozen release publication immutability.** Publication now
  fails closed instead of overwriting (`--clobber`) an existing release, tag,
  or canonical asset for a version; a routine workflow rerun can never
  silently replace a published tarball, sidecar, gate record, or validation
  report.
- **RFC 100 — Package axiom scope integrity.** The three `native_decide`
  proofs in `Henret.Examples.Basic` are removed (`decide` only, per
  DEC-003); `scripts/native_decide_check.py` gates the whole package against
  undeclared `native_decide` use, and every axiom-budget statement names its
  exact import and theorem scope.
- **RFC 101 — Documentation and RFC index integrity.** `rfcs/README.md` and
  the generated mdBook RFC index are now produced from RFC front matter by
  `scripts/extract_rfc_index.py` (diff-gated, `--check`); `markdown_link_check.py`
  and `doc_count_check.py` cover repository-wide link and count drift. This
  is the mechanism this very patch exercises to move RFCs 098–104 to
  `rfcs/done/` — see "Documentation and risk register" below.
- **RFC 102 — Release gate unification.** Following the v0.34.5 timing
  evidence (interpreted demo/conformance now run in ~3 s), gates 2 (demo), 4
  (conformance), and 10 (mdBook at the exact release commit) are required,
  fail-closed `release-core` gates rather than advisory ones; a timeout is
  release-blocking, never a silent skip.
- **RFC 103 — Evidence ledger to gate binding.** `verified_by_ci: true` in
  `docs/evidence-ledger.yaml` is now a checked reference to an executable
  gate/workflow record rather than an unchecked claim, and bounded
  model-explorer execution (gate 11) is a required `release-core` gate with
  its own retained evidence.
- **RFC 104 — CI supply-chain pinning and package metadata.** Every GitHub
  Action and downloaded tool (`actions/checkout`, `actions/cache`,
  `actions/upload-artifact`, the Lean and mdBook archives) is pinned to an
  immutable commit or checksum in `ci/supply-chain.json`, verified before
  extraction/execution by `scripts/ci_supply_chain.py`; every complete
  workflow file is raw-byte SHA-256 pinned so any command/syntax change
  requires a matching reviewed policy change; `gh` is restricted to Henret's
  own create/upload/post-upload-download routes bound to the literal
  `nabbisen/henret` repository; and a project-owned per-object guard
  (`--check-release-evidence`) verifies the complete retained evidence set —
  tarball, manifest, `GATE-RUN.md`, and all 12 gate logs — before upload.
  Closed against hosted run `29831559959` at exact commit `f366fa5`,
  independently re-verified in three environments (the hosted runner, and
  two local reconstructions on different Git versions) producing a
  byte-identical archive.

This version-transition patch itself adds three findings from the RFC 104
closure review (`.git-exclude/reviewed/026`):

- **Cold release-core cache.** The `release-core`/`release-validation`
  Lake-build cache step now runs only on `pull_request` events; push/tag
  (authoritative) runs always build `.lake` cold. `docs/evidence-ledger.yaml`
  binds every PROVEN claim to `ci_gate: build.lean` (capability
  `kernel-build`); a cache-restored `.lake` object satisfied that gate
  through an input RFC 104 did not pin, hash, or record. No proof was ever
  skipped by this — Lake's content hashing owed no rebuild — but the
  authoritative run must now perform the kernel work its capability claims.
- **Supply-chain pin refresh.** `actions/checkout`'s `v6` tag moved (the
  pinned commit did not); the reviewed pin update was applied across all
  four workflows and their `workflow_sha256` entries in
  `ci/supply-chain.json` regenerated. `ci_supply_chain.py --check-updates`
  reports all pins current.
- **Write-control trust anchor documented.** Every supply-chain and
  hosted-provenance control governs what a hosted run does once it starts,
  not who may push `main` or create a release tag. `docs/src/ci-supply-chain.md`
  gains a "Write-control trust anchor" section naming this boundary
  explicitly (mirroring how the C-concurrency boundary, R3, is documented
  rather than silently assumed); `docs/risk-register.md` gains R9. Whether
  branch/tag protection is configured, and whether a cryptographic build
  provenance mechanism (e.g. artifact attestations, Sigstore) is scheduled,
  remain the human owner's decisions.

**Documentation and risk register.** RFCs 098–104 move to `rfcs/done/` with
`implemented_in: v0.34.6`; both RFC indexes are regenerated. R6 (doc/claim
drift) retires: this patch is the first to move RFCs through the RFC 101
generated-index mechanism, closing the specific roadmap/RFC/doc-index
contradiction the v0.34.5 review found. R9 (write-control trust anchor) is
added, documented but not yet resolved — see above.

**Not in this patch.** No M2 work, semantic change, or new `RuntimeOp`. Tag
creation, GitHub Release publication, and post-upload verification for
v0.34.6 follow this patch, on a fresh hosted `release-core-v4` run and the
owner's release approval — the v0.34.5 evidence record is not rewritten.

## v0.34.5 — Release-validation fix: demo compile-blowup root-caused

v0.34.4 is published and frozen (consumers pin its sidecar); this release carries a
**release-validation-only** fix and does not change the model, proofs, or the
release-core sidecar contract.

- **Root cause: demo `main` compile blowup.** The release-validation run hit its
  cap with the demo stalled — not in elaboration or runtime, but in *compilation*
  of `main` (44 min). Each `let (a, b) := step …` tuple-pattern bind in the `do`
  block makes the Lean code generator duplicate the continuation, so compile cost
  is exponential in the number of destructurings. **Fix:** rewrite the 8 binds in
  `Main.lean` as `.1`/`.2` projections. `main` now compiles in 470 ms;
  `check.sh --release-validation` runs demo + conformance interpreted and **passes
  in ~3 s** (verified against Lean 4.15.0). All 41 demo assertions + 77 conformance
  scenarios pass.
- **Advisory safety net.** Gates 2 (demo) and 4 (conformance) still run under a
  `timeout` (tunable via `HENRET_DEMO_TIMEOUT`/`HENRET_CONF_TIMEOUT`); a timeout is
  recorded `status: timeout` and is non-fatal, a real regression still surfaces.
  This now guards against any *future* slowdown rather than masking the demo hang.

- With demo + conformance now cheap interpreted, promoting them into release-core
  (architect §8) is viable and left as a follow-up decision.

## v0.34.4 — Release CI repair + two-tier gate model (RFC 097)

Makes the authoritative release gate actually complete on the standard CI runner
so the RFC 095 sidecar can be published for the iotakt/jemmet stack. **No model,
proof, or theorem change**; axioms unchanged, public theorem surface unchanged
(101 names). `manifest_schema` stays 1 (additive). `check.sh --fast`, gate-0
self-test, and the docs gate green.

- **RFC 097 — release-core / release-validation split (Implemented).** The old
  monolithic `--release` natively compiled the `henret-demo` and
  `henret-conformance` executables (C codegen for ~80 modules + link), which on a
  2 vCPU / 7 GB GitHub runner OOM-killed and, with swap, ran ~1 h to the job
  timeout. Per architect review, the gate is split by **criticality**:
  `check.sh --release-core` (alias `--release`) runs the cheap, CI-authoritative,
  kernel-checked evidence — build/proofs, examples, axiom audit, doc/metadata,
  warning budget — plus the canonical tarball and hashed manifest, and **publishes
  the sidecar**; `check.sh --release-validation` runs the demo + exhaustive
  conformance interpreted as **advisory, non-blocking** evidence, emitting a
  separate `validation-report.json`. CI authority (RFC 080-D) is preserved.
- **Manifest honesty.** `release-verification.json` gains `release_profile`,
  `required_gates_passed`, per-gate `criticality`, and `validation_reports`. Under
  `ci-core-v1` the advisory gates are not silently dropped — they appear as
  `not_run_in_release_core` with a reason. `verify_release_manifest.py` requires
  only `required` gates to pass. New `scripts/validation_report.py` and a
  `release-validation.yml` workflow produce/host the advisory report (whose
  per-gate timings are also the architect's §4 diagnostic).
- **Dirty-tree exception tightened.** Per architect review, the 080-4 exception
  now applies only to *untracked* entries; a tracked source modification stays
  dirty even if its path resembles an excluded cache/tool path. Invariant
  documented in the manifest schema. RFC 097 is fully closed.
- **Post-upload verification.** The release-gate workflow now re-downloads the
  published assets and runs `verify_release_manifest.py` against them (RFC 095 /
  RFC 097 closure condition 2), catching upload corruption a pre-upload check
  cannot. RFC 097 is now fully closed: v0.34.4 published a green `ci-core-v1`
  sidecar from CI.
- **Release publish permissions.** With the dirty-tree blocker cleared, the
  run reached the publish step and `gh release create` returned HTTP 403
  ("Resource not accessible by integration"): the workflow `GITHUB_TOKEN`
  defaulted to read-only `contents`. Added `permissions: contents: write` to
  the release-gate and release-validation workflows so the token can create
  the release and upload the tarball + sidecar + GATE-RUN.
- **Dirty-tree publish fix.** The release-core run reached the manifest step
  then failed `--release-core on a dirty source tree (080-4)`: the CI elan
  install extracted the `elan-init` binary into the checkout (untracked, not
  excluded from the tarball). Fixed by installing elan in `/tmp`, gitignoring
  `elan-init`, excluding it from the archive, and broadening the dirty-tree
  exception to ignore tooling/cache artifacts (mirrors the tarball excludes);
  the check now prints offending paths and records `git_dirty_paths`. Manifest
  also gains `gate_registry: rfc097-ci-core-v1` (architect review §4).
- **Release CI repair (folded in).** Tag filter corrected to the bare-numeric
  scheme (`[0-9]*.[0-9]*.[0-9]*`; tags are `0.34.4`, not `v0.34.4`); CI now
  attaches the canonical tarball + sidecar + `GATE-RUN.md` to the GitHub Release
  as assets (not just a workflow artifact). Filename convention pinned: published
  GitHub assets are **no-`v`** (`henret-X.Y.Z.*`), dev tarballs keep the `v`-prefix
  (`HENRET_PUBLISH_NAME=1` in CI; resolves RFC 095's filename open question). The
  demo/conformance run interpreted off gate-1 oleans (new `HenretExamples` lib).
  Consumer recipes in the integration contract, checklist, and schema doc updated.

## v0.34.3 — Stack Release Contract (RFC 096)

Implements RFC 096 (approved with minor amendments) — **no model, proof, or
theorem change**; axioms unchanged, public theorem surface unchanged (101 names).
`check.sh --fast` and the docs gate green.

- **RFC 096 — Stack Release Contract (Implemented).** The RFC 080 manifest schema
  becomes the per-package contract across the henret → iotakt → jemmet stack, with
  a thin stack manifest that pins **dependency edges**, not just a package list.
  New normative `docs/src/release-manifest-schema.md` describes `manifest_schema 1`
  (per-package, RFC 080/081/095) and `stack_manifest_schema 1` (stack): unique
  package names; edges that resolve to exactly one consumer/provider; providers
  pinned by `provider_manifest_sha256` and cross-checked against the consumer
  manifest's own `dependencies`; hash-is-identity mirror semantics; exact pins
  only (no compatibility ranges in v1); optional, RFC 081-shaped trust inventory.
  New `scripts/verify_stack_release.py` is the minimal local-file verifier
  (resolves manifests by hash, checks packages and edges, non-zero on mismatch) —
  validated on a synthetic two-package stack, catching an edge that claims a
  provider version the consumer never declared. `integration-contract.md` points
  consumers at the schema doc and states henret does not verify downstream
  packages. RFC moved to `rfcs/done/`.

## v0.34.2 — Published release manifest (RFC 095)

Implements RFC 095 (approved with amendments) and revises RFC 096 per the same
review — **no model, proof, or theorem change**; axioms unchanged, public
theorem surface unchanged (101 names). `check.sh --fast` and the docs gate green.

- **RFC 095 — Published Release-Verification Manifest (Implemented).** The RFC 080
  manifest becomes a consumer-fetchable artifact published beside the tarball, so
  iotakt/jemmet can anchor henret provenance at fetch time instead of trusting a
  CI log. `release_manifest.py` now emits a `source_archive` block
  (`name`/`sha256`/`size_bytes`) beside the retained `tarball_sha256`, and binds
  `GATE-RUN.md` by hash in `human_summary` (rendered from the core manifest first,
  so it cannot drift). New `scripts/verify_release_manifest.py` is the consumer /
  post-upload checker (tarball hash, `source_archive`, gate-pass, GATE-RUN.md
  binding; non-zero on any mismatch). `integration-contract.md` §11 documents the
  exact `sha256sum`/`jq` recipe and the checker; `release-checklist.md` adds the
  publish-sidecar and post-upload re-download verification steps. `manifest_schema`
  stays 1 (all additive). Signing remains a named follow-up (hash-only
  verification trusts the publication channel).
- **RFC 096 — Stack Release Contract (revised, still Proposed).** Folded in the
  review's required amendments: per-package manifests keep `manifest_schema`
  while the stack manifest uses a distinct `stack_manifest_schema`; the stack
  gains `dependency_edges` cross-checked against per-package `dependencies`
  declarations; `scripts/verify_stack_release.py` is named as the validation tool;
  `depends_on` now includes RFC 081 (trust inventory); peer-governance and
  mirror-identity (hash, not URL) semantics are spelled out. Awaits re-approval
  before implementation.

## v0.34.1 — Consumer-doc accuracy + release-archive hygiene

Documentation and release-tooling follow-ups from jemmet consumer feedback —
**no model, proof, or theorem change**; axioms unchanged, public theorem surface
unchanged (101 names). `check.sh --fast` and the docs gate green.

- **Consumer-doc accuracy.** `integration-contract.md` no longer hard-codes the
  operation count — it points to the live generated runtime-op table as the
  source of truth — and gains a *Driving an actual runtime* section pointing
  consumers at the out-of-tree runtime package and the bridge. The stale
  `handoff-henret-for-iotakt.md` (written at v0.6.0) is now banner-marked as a
  historical snapshot that points to the generated tables.
- **Cleaner canonical release archive (RFC 080-B).** The reproducible archive
  built by `check.sh --release` (the one its `release-verification.json` manifest
  hashes) now also excludes `__pycache__`, `*.pyc`, `docs/book/`, `.elan/`, and
  `.cache/`, matching the published-tarball exclude set so the manifest's
  `tarball_sha256` anchors a clean archive.
- **Two RFCs drafted (proposed).** [RFC 095 — Published Release-Verification
  Manifest] formalizes publishing the RFC 080 manifest as a consumer-fetchable
  sidecar; [RFC 096 — Stack Release Contract] aligns the henret/iotakt/jemmet
  stack to the RFC 080 schema rather than a parallel format. Both `Proposed`,
  awaiting architect review; no behavior change.

## v0.34.0 — mdBook Documentation Layout (RFC 094)

Documentation-architecture cleanup — **no model change, no new op, no proof
change**; axioms unchanged, all nine fast gates green and the new docs gate
(`scripts/check_docs.sh`) green. Closes RFC 094 (moved to `rfcs/done/`,
Implemented in v0.34.0). One atomic move/relink/gate-update commit, no semantic
content rewrite.

- **Documentation is now an [mdBook](https://rust-lang.github.io/mdBook/).** All
  reader-facing, integration-facing, proof-facing, and maintainer-facing docs
  moved from flat `docs/*.md` to `docs/src/*.md`, with `docs/book.toml`, a
  hand-maintained `docs/src/SUMMARY.md` (organized into three reader paths — new
  users, integrators, maintainers/contributors), and a new
  `docs/src/introduction.md`. Generated docs moved to `docs/src/generated/`;
  migration guides to `docs/src/migration/`; the refinement-contract pattern to
  `docs/src/patterns/`.
- **Book/internal boundary (RFC 094 §5).** Kept *out* of the book, at `docs/`
  root: `reviews/`, `handoff-*.md`, `risk-register.md`, and the machine-data
  `evidence-ledger.yaml` (its reader-facing rendering, `evidence-ledger.md`, is
  in the book). `release-policy`, `release-checklist`, `progress-policy`, and
  `review-playbook` are in the book's maintainer section.
- **Docs gate, separate from the Lean fast gate (RFC 094 §6).** New
  `scripts/check_docs.sh` runs `scripts/doc_summary_check.py` (orphan + every
  SUMMARY target exists + every local Markdown link resolves) and `mdbook build
  docs`. `mdbook` is intentionally **not** in `check.sh --fast`: blocking for
  documentation/layout PRs and release candidates, not on the Lean proof path.
- **Generator and gate repointing (RFC 094 §8).** `extract_model_docs.py`,
  `extract_theorem_docs.py`, `extract_rfc_index.py`, `public_theorem_index.py`,
  `proof_dependency_budget.py` now write/read `docs/src/generated/`;
  `doc_symbol_check.py` scan list, `doc_count_check.py` `EXCLUDE_DIR`,
  `forbidden_claim_check.py` ledger path, and `fault_taxonomy_check.py` doc path
  all updated. `extract_rfc_index.py` now emits RFC links that resolve from the
  book tree (`../../../rfcs/...`), fixing links that were latently broken before
  the move.
- **doc_count convention (RFC 094 §9).** `docs/src/migration/` stays excluded
  from the stale-current-count gate; the migration template now requires
  historical counts to be marked as historical.
- **Compatibility note.** This is a path-breaking documentation change: external
  links to `docs/generated/...` or other `docs/*.md` pages now live under
  `docs/src/...`. Henret is pre-contract-freeze, so no symlink shim is provided.
  The public *theorem* surface is unchanged (still 101 names); only file paths moved.
- **mdBook 0.5 line.** The book targets mdBook 0.5 (last verified with 0.5.3).
  A separate `.github/workflows/docs.yml` runs the docs gate on PRs, pushes,
  and tags, installing the latest mdBook release from its prebuilt binary;
  `scripts/check_docs.sh` reports the detected version. `book.toml` no longer
  forces `default-theme`, so the book follows the reader's light/dark
  preference. The migration template's angle-bracket placeholders were
  rewritten as `[...]` so the stricter 0.5 HTML parser builds with no warnings.
- **Migration landing page.** New `docs/src/migration/README.md` explains the
  guides, links the template and every version-to-version guide, and states the
  historical-count convention; `SUMMARY.md` points the migration section at this
  index, with the template as a child page.

Deferred from the implementation review: reader-facing path-label normalization
(a separate low-priority pass, not mixed into the layout work) and monitoring the
flat `docs/src/` page count (no action until navigation becomes painful).

## v0.33.0 — Proof Dependency Budget (RFC 069)

Additive proof-observability slice — **no model change, no new op**; axioms
unchanged, all nine fast gates green. Closes RFC 069 (moved to `rfcs/done/`,
Implemented in v0.33.0).

- `scripts/proof_dependency_budget.py` generates
  `docs/generated/proof-dependency-budget.md`: a per-theorem budget over the 156
  audited theorems, classifying each by **constructiveness** (constructive /
  classical / trusted = 122 / 33 / 1), **import weight** (core / bridge /
  standard / conformance / native, a stable namespace proxy), and **stability**
  (public-stable / internal = 47 / 109). Every `Classical.choice` user is listed
  explicitly.
- `--check` wired into `check.sh` gate 7: the budget cannot drift silently — a
  `constructive → classical` move or a new audited theorem fails the gate until
  the table is regenerated, making the classical budget a conscious decision.
- `docs/proof-dependency-budget.md` is the human-facing policy page (categories +
  four policy rules + a map to `axiom-budget.md` / `public-theorems.md` /
  `proof-api-stability.md` / `proof-ergonomics-metrics.md`).
- RFC 062 follow-ups recorded before RFC 069 (review §11): added the `*_pass`
  discipline rule to `docs/proof-style.md`; gave `docs/proof-ergonomics-metrics.md`
  a stable, citable observation schema. Phase 2B-2 (Shape-A pilot) deferred.
- Public theorem surface unchanged (101 names). Matrix claim 236.

## v0.32.0 — Proof Ergonomics Library, Phase 2B-1 (RFC 062)

Lifecycle-only proof-ergonomics slice, architect-approved (Phase 2B-1: Shape-B,
per-field, no Shape-A). **No model change, no new op** — additive proof
engineering; same theorem statements and public names, axioms unchanged, all nine
fast gates green. RFC 062 stays Proposed (Phase 2B-2 / Phase 3 gated).

- Five per-field pass-through helpers in `Henret/Proofs/StepFields.lean`:
  `wf_waiters_owned_pass`, `wf_waiters_nodup_pass`, `wf_owned_has_mailbox_pass`,
  `wf_timer_nodup_pass`, `wf_timer_sorted_pass`. Each takes exactly the
  projection-stability proof(s) the field reads.
- Adopted at 22 sites across `Preservation/Lifecycle.lean`
  (`spawn`/`schedule`/`yield`/`complete`/`cancel`/`fail`/`spawnChild`). Removed a
  defensive `by_cases u = t … simp_all` from the `waiters_owned` bullet in three
  blocks (the op never touches `mailboxWaiters`/`taskOwner`, so the split was
  unnecessary). `Lifecycle.lean`: 1692 → 1680 lines; total exported `wf_*_pass`:
  13 → 18 (all used).
- `taskState`-reading fields (`waiters_waiting`/`timers_sleep`/
  `spawned_has_owner`/`owner_spawned`) left explicit — lifecycle ops mutate
  `taskState`, so those are not pass-through and keep their `by_cases`.
- Docs: helper suffix discipline (`*_pass` vs `*_under_enqueue` vs `*_of_*`) added
  to `docs/proof-style.md`; Phase 2B-1 measurement recorded in
  `docs/proof-ergonomics-metrics.md` (Observation 2; Phase-2A private helper names
  back-filled per review §5). Matrix claim 235.
- Public theorem surface unchanged (still 101 names). Shape-A enumeration cascade
  untouched, by ruling.

## v0.31.0 — Proof Ergonomics Library, Phase 2A (RFC 062)

Messaging-only proof-ergonomics slice, architect-approved (Phase 2A). **No model
change, no new op** — additive proof engineering; same theorem statements and
public names, axioms unchanged, all nine fast gates green. RFC 062 stays Proposed
(Phase 2B/Lifecycle gated on a 2A review).

- Extracted the occurrence-identity fields under enqueue
  (`occ_fresh`/`occ_nodup`/`occ_disjoint`) into three `private`
  `*_under_enqueue` helpers in `Preservation/Messaging.lean`, shared by all five
  `send`/`inject` enqueue sites. The proof is occurrence-only (source-agnostic),
  so one helper trio replaces five inline copies. `Messaging.lean`: 2078 → 1989
  lines; the occ proof is now defined once.
- `send`/`inject` `mailbox_within_capacity` reasoning kept explicit (an enqueue
  grows the mailbox; the not-full guard bounds the new length) — never disguised
  as a pass-through (architect §10).
- New `docs/proof-ergonomics-metrics.md` records the dummy-op file-touch
  measurement (method defined in `docs/proof-style.md`; not a CI gate). Honest
  finding: Phase 2A is a Shape-B (lines/duplication) win, not a Shape-A
  (file-count) one.
- `docs/proof-style.md`: recorded the simp-set permission rule (RFC 062 Phase 1
  lesson) and the Phase-2 evidence gate; added the measurement method and the
  Phase-2A/2B/2C status.
- Public theorem surface unchanged (still 101 names; the new helpers are private
  and not on the prefix-defined public surface). Matrix claims 233–234.

## v0.30.0 — Proof Ergonomics Library, Phase 1 (RFC 062)

First slice of a phased, architect-gated proof-style modernization. **No model
change, no new op** — additive proof-engineering only; same theorem statements
and public names, axioms unchanged, all nine fast gates green. RFC 062 stays
Proposed (Phases 2–3 gated on a separate review); Phase 1 is recorded in the RFC
body.

- **Proof-style guide** — `docs/proof-style.md` codifies the policy: auditability
  over brevity (every preservation obligation stays named by a theorem,
  field-specific lemma, or explicit op classification); never `| _ =>` for op
  classification; governed named simp-sets; no Phase 1–2 macros; how-to-add a
  RuntimeOp / WellFormed field; the files-touched-per-op measurement metric.
- **Theorem-name diff gate** — `scripts/public_theorem_index.py` snapshots the
  101-name prefix-defined public theorem surface
  (`preserves_wf_`/`step_preserves_`/`reachable_`/`bridge_`/`run_preserves_`) to
  `docs/generated/public-theorems.md`, wired into gate 7. A public theorem cannot
  be renamed or removed without a recorded migration
  (`docs/proof-api-stability.md`) — catching drift the audit allowlist alone does
  not. `extract_theorem_docs.py` continues to cover the audit-allowlist surface.
- **`Time.lean` pilot** — `wf_mailbox_capacity_pass` (new in
  `Henret/Proofs/StepFields.lean`) discharges `mailbox_within_capacity` (RFC 056)
  for any step that leaves `mailboxPolicy` and `mailboxes` stable; the three time
  blocks (`preserves_wf_sleep`/`tick`/`wake`) now share it instead of repeating
  five lines apiece.
- **No simp-set in Phase 1 (documented finding).** A `henret_upd` named
  point-update simp-set was prototyped and withdrawn: the `upd` lemmas do not
  compose under a named `simp only` set, and registering one would pull a
  `Lean.Meta.*` import into the prelude-only proof tree for no payoff. Named
  simp-sets remain sanctioned; adoption is deferred to the Phase-2 dense files.
- **Matrix.** Claims 230–232 (through 232).

## v0.29.0 — Manual Actor-Resource Release (RFC 093)

Adds `releaseActor`, the voluntary-release counterpart to RFC 091's
`acquireActor`, completing the actor-resource lifecycle symmetry. Additive, zero
`sorry`, no new axiom kinds. First Wave 1 item of the prioritized roadmap.

- **New op `releaseActor a r`** (RuntimeOp 28 → 29): control-plane, running-gated
  (symmetric with `acquireActor`). Flips actor `a`'s own `allocated` resource to
  `released`. Invalid for a task-owned resource, the wrong actor, an already-
  released resource, or a non-running runtime. `release t r` (the task release)
  remains invalid for actor-owned resources.
- **Proofs.** `preserves_wf_releaseActor` (the flip discharges the live-owner
  obligation; owner unchanged → existence preserved); `bridge_releaseActor`
  (queue-stable). The drain/frozen spine carries `releaseActor` with no new
  hypotheses — it writes only an already-`allocated` slot and is running-gated.
- **Conformance.** Six scenarios incl. `releaseActor_enables_drained_stop`
  (release gives a drain route that does not need `closeActor` + `finalize`).
- **Docs.** resource-lifetime manual-release section; proof-index RFC 093; matrix
  227–229; RuntimeOp count 28 → 29.

## v0.28.0 — Clean-Stop Predicate (RFC 092 / stopped → Drained resolution)

Resolves the last deferred RFC 057 Tier 2 question — whether `.stopped` should
globally imply `Drained` — per the architect's ruling (**Option B**). Additive,
non-breaking, zero `sorry`, no new axiom kinds.

- **Decision.** Keep `stopWhenIdle` (scheduler-quiescent stop) and
  `stopWhenDrained` (quiescent + drained stop) **distinct**; do not add a global
  `stopped → Drained` invariant (which would collapse the two ops — a breaking
  change against RFC 087's additive design).
- **`Henret/Proofs/CleanStop.lean`** (new): `Stopped` (status only),
  `StoppedDrained` (`Stopped ∧ Drained`), `CleanStopped` (`Stopped ∧ Frozen`) as
  the contract handle for clean shutdown. `stopWhenDrained_enters_cleanStopped`
  (+ reachable form); projections `cleanStopped_drained` / `_quiescent`;
  permanence `cleanStopped_run_stays_frozen`. `.stopped` is an *entry* fact —
  `shutdown` relabels `.stopped → .shuttingDown` — so durable permanence is at the
  `Frozen` level.
- **Contrast theorem** `stopWhenIdle_can_stop_undrained` + golden scenario
  `stopWhenIdle_stops_with_live_resource`: a named witness that `stopWhenIdle`
  reaches `.stopped` with a live resource, so bare `.stopped` can never be
  silently claimed clean.
- **Docs.** `RuntimeStatus` / stop-op docstrings corrected; clean-stop section in
  shutdown-semantics; security reading in resource-drain (bare `.stopped` is not a
  cleanup guarantee); proof-index RFC 092; matrix 223–226. Contract rule for
  RFC 070/072/061/060/066/074: clean shutdown is `CleanStopped`, never bare
  `.stopped`.

## v0.27.0 — Actor-Owned Resources (RFC 091 / RFC 057 Tier 2)

Resources are no longer task-only. RFC 091 generalizes the ledger owner from a
task to a `ResourceOwner` sum type (`task | actor`) over a single ledger, one
`Drained` predicate, and one finalization discipline — the architect's
Option A, with unified `Drained` and a new `acquireActor` op. Zero `sorry`, no
new axiom kinds, all 9 `check.sh --fast` gates green.

- **Representation (breaking).** `ResourceRecord.owner : TaskId → ResourceOwner`
  (`inductive ResourceOwner = task | actor`). See
  `docs/migration/v0.26-to-v0.27.md`. The three task-keyed `WellFormed` fields
  become owner-generic (`resource_owner_valid` / `allocated_owner_live` /
  `closing_owner_closed`, read through `OwnerValid` / `OwnerLive` /
  `OwnerClosed`); the RFC 057 task statements survive as compatibility
  corollaries `WellFormed.allocated_owner_nonterminal` / `closing_owner_terminal`.
- **New op `acquireActor a`** (RuntimeOp 27 → 28): a control-plane allocation
  gated on `runtimeStatus = .running`, the actor being open, and the actor
  **existing** — existence witnessed by a mailbox (`ActorExists`), not by
  `actorStatus` alone (`preserves_wf_acquireActor`).
- **Lifetime.** Actor-owned resources survive task termination; `closeActor a`
  marks actor-`a`-owned `allocated` resources `closing`
  (`closeActor_marks_actor_resources_closing`); `finalize` reclaims them.
  `release t r` is invalid for actor-owned resources (Tier 1; no manual actor
  release). `WellFormed.status_irrel` narrowed to `runtimeStatus_irrel` (the
  resource invariants now depend on `actorStatus`).
- **Unified drain.** `Drained` covers actor-owned resources; `drained_step_drained`
  and `step_preserves_frozen` now carry `runtimeStatus ≠ .running` (true after
  `stopWhenDrained`), blocking `acquireActor` from re-leaking post-stop. Under
  `Drained`, `closeActor` is ledger-inert (`markActorResourcesClosing_eq_of_drained`).
- **Conformance.** 12 new scenarios; coverage registry complete. Matrix through 222.
- **Bridge.** `bridge_acquireActor` (queue-stable; the bridge tracks queues, not
  resources).

## v0.26.0 — Drained Permanence / Frozen invariant (RFC 090 / RFC 057 Tier 2 payoff)

The end-to-end payoff of the drain/stop thread (RFCs 087–089): a runtime stopped
via `stopWhenDrained` stays drained — and quiescent — for the rest of *any*
operation sequence, not just one step. Additive, no model change, no `sorry`.

- **The bundle** (`Henret/Proofs/Frozen.lean`): `Frozen s` = `running = none ∧
  readyQ = [] ∧ timers = [] ∧ runtimeStatus ≠ running ∧ Drained s`, preserved by
  every operation (`step_preserves_frozen`). The resource axis reuses RFC 088's
  `drained_step_drained`; the `wake` that RFC 088 could not rule out is blocked
  by RFC 089's `quiescent_no_sleeping`; every other repopulating operation is
  rejected by the guards. `runtimeStatus ≠ running` (not `= stopped`) keeps the
  bundle stable under `shutdown`.
- **Headlines**: `reachable_stopWhenDrained_stays_drained` and
  `reachable_stopWhenDrained_stays_quiescent` — from any reachable state, a
  successful `stopWhenDrained` stays drained and quiescent across every
  subsequent op sequence. A drained stop is permanent.
- **Docs**: proof-index RFC 090; matrix claim 212 discharged (PROVEN) plus
  claims 213–215.
- **Deferred (from RFC 087)**: actor-owned resources, the breaking global
  `stopped → Drained` invariant (covering `stopWhenIdle`), wall-clock liveness.

## v0.25.0 — Sleeping-Timer Coherence (RFC 089 / RFC 057 Tier 2 groundwork)

Closes the coherence gap that capped RFC 088 at a single step. Additive,
no model change, no `sorry`, all STD.

- **The invariant** (`Henret/Proofs/SleepingTimer.lean`): `SleepingHasTimer s`
  — every sleeping task has a registered timer — proven preserved by all 27
  operations (`step_preserves_sleepingHasTimer`) and in every reachable state
  (`reachable_sleepingHasTimer`). The model's `WellFormed` previously recorded
  only the converse (a timer's task is sleeping/waiting-timed), so an empty
  timer queue could not rule out a sleeping task.
- **Payoff**: `quiescent_no_sleeping` — a quiescent runtime (empty timer queue)
  has no sleeping tasks. This is the fact that unblocks multi-step drained
  permanence and a "stopped stays quiescent" result.
- Proven as a standalone reachable invariant (not a 34th `WellFormed` field),
  keeping the change off every preservation file, mirroring RFC 057.
- **Docs**: proof-index RFC 089; matrix claims 210–212.
- **Deferred (next slice)**: the `Frozen` bundle invariant giving multi-step
  permanence / stopped-stays-quiescent; also still deferred — actor-owned
  resources, the breaking global `stopped → Drained` invariant, wall-clock
  liveness.

## v0.24.0 — Drained-State Persistence (RFC 088 / RFC 057 Tier 2)

Closes the one-step gap that RFC 087 left open. RFC 087 proved a drained stop is
drained *at the instant of stopping*; this proves the no-leak property survives
the next operation. Additive, no model change, no `sorry`, no new axiom kinds.

- **Single-step persistence** (`Henret/Proofs/DrainedPersistence.lean`):
  `drained_step_drained` — from a drained state with `running = none`, every
  operation preserves `Drained`. The argument is structural: existing resources
  are `released` and stay so (RFC 057's `step_resources_eq_of_released`), and no
  new resource appears because `acquire` requires a running task
  (`step_resources_none_run_none`).
- **Composition with RFC 087**: `stopWhenDrained_then_step_drained` — a
  successful `stopWhenDrained` keeps `running = none` and the ledger unchanged,
  so the next operation cannot leak a resource.
- **Conformance**: `stopWhenDrained_then_acquire_stays_drained` — a post-stop
  `acquire` is `.invalid` and the ledger stays drained.
- **Docs**: `docs/resource-drain.md` persistence section; proof-index and matrix
  (claims 207–209).
- **Deferred**: multi-step permanence needs a `sleeping → timer` invariant (the
  converse of `timers_sleep`) the model does not yet carry; also still deferred
  are the breaking global `stopped → Drained` invariant, actor-owned resources,
  and wall-clock liveness.

## v0.23.0 — Resource Drain Discipline (RFC 087 / RFC 057 Tier 2)

The first Tier-2 slice of the resource ledger, on the safety/possibility axis.
Additive — no change to existing operations, no new resource state, no `sorry`,
no new axiom kinds. **No wall-clock/liveness claim.**

- **Drain progress** (`Henret/Proofs/ResourceDrain.lean`):
  `closing_finalize_releases` — a `closing` resource is always finalizable in
  one step. With Tier 1's terminal-marks-closing results, the drain path is
  never blocked.
- **Drain-before-stop**: new additive operation `stopWhenDrained` (RuntimeOp
  26 → 27) that reaches `stopped` only when quiescent **and** the ledger is
  drained (decidable `resourceDrained` check, bounded by `nextResourceId`).
  `stopWhenIdle` is unchanged.
- **Proofs** (all STD): `stopWhenDrained_stops_drained` (a successful drained
  stop never leaves a resource leaked), `resourceDrained_drained` (the bounded
  check captures the unbounded `Drained` predicate under `WellFormed`),
  `stopWhenDrained_stops` / `stopWhenDrained_noop` (per-branch),
  `preserves_wf_stopWhenDrained` (all 33 `WellFormed` fields), and
  `bridge_stopWhenDrained`.
- **Conformance**: `stopWhenDrained_drained_stops` (drain → stop succeeds) and
  `stopWhenDrained_live_resource_invalid` (stop refused while a resource is
  closing), registered in the coverage registry.
- **Downstream**: the new operation propagated through every exhaustive
  `RuntimeOp` match (step, WF dispatcher, projections, bridge, trace, stable
  theorems, model docs).
- **Docs**: new `docs/resource-drain.md`; proof-index and matrix (claims
  204–206). RFC 087 drafted and implemented.
- **Deferred** to later Tier-2 slices: the breaking global `stopped → Drained`
  invariant, actor-owned resources, and wall-clock liveness/timeliness.

## v0.22.1 — RFC 059 closeout: EDF ordering-optimality

Completes the one item deferred from v0.22.0. `deadline_policy_selects_min_deadline`
proves the earliest-deadline-first policy chooses a ready task whose deadline is
minimal — no ready task is strictly earlier (a `deadlineLt`-minimum). Supporting
results in `Henret/Proofs/MetaPolicy.lean`: `foldl_winner` (a fold-min returns an
element nothing strictly beats, given a strict-total comparator) and the order
facts `deadlineLt_irrefl`, `dlt_htA`, `dlt_htB` over the bespoke `Option Nat`
deadline order. Still an ordering fact only — no theorem claims a deadline is
met. Zero `sorry`, zero new axiom kinds; RFC 059's proof-obligation list is now
fully discharged. Matrix claim 203.

## v0.22.0 — Deadline & Priority Semantics (RFC 059)

Adds optional per-task scheduling metadata and metadata-driven policies on the
RFC 058 layer. Deadlines are **logical-time ordering only** — no real-time
claim, and no theorem asserts a deadline is met. Zero `sorry`, zero new axiom
kinds.

- **Model**: `TaskMeta { priority : Nat, deadline : Option Nat }`
  (`Henret/Actor/Meta.lean`) and a `taskMeta : TaskId → Option TaskMeta` field
  on `RuntimeState` (absent ⇒ `defaultMeta`). Two operations, `setPriority` and
  `setDeadline` (`RuntimeOp` 24 → 26), guarded on the task being spawned.
- **Design choice**: `taskMeta` is deliberately **not** part of `WellFormed`
  (the optional-metadata non-goal rules out "every spawned task has metadata"),
  so the metadata ops preserve all 33 invariant fields trivially.
- **Proofs** (`Henret/Proofs/Metadata.lean`): `wf_taskMeta_only` (zero axioms),
  `preserves_wf_setPriority`, `preserves_wf_setDeadline`, and
  `setPriority_meta_of_spawned` / `setDeadline_meta_of_spawned` (the ops no-op
  on unspawned tasks).
- **Policies** (`Henret/Scheduler/MetaPolicy.lean`): `priorityPolicy` (highest
  priority), `edfPolicy` (earliest deadline, missing-deadline-last), and
  `hybridPolicy` (priority then deadline). All three are **sound** (`pickBy_mem`
  → `choose_sound`) and inherit `policyStep_preserves_wf` from RFC 058.
- **Optimality** (`Henret/Proofs/MetaPolicy.lean`): `priority_policy_selects_max`
  (the chosen task has maximal priority among ready tasks) via `foldl_best_ge`.
  The EDF ordering-optimality analogue is a tracked closeout follow-up.
- **Downstream**: every exhaustive `RuntimeOp` match updated for the two new
  ops (`step`, the WF dispatcher, projections, bridge grammar/preservation,
  trace, stable theorems, model docs).
- **Docs**: new `docs/deadline-priority.md` (with the real-time warning and a
  negative "deadline can be missed" example); proof-index and matrix (claims
  199–202) extended.

## v0.21.0 — Scheduling Policy Layer (RFC 058)

Adds a policy-parametric scheduling layer **on top of** the unchanged core
scheduler: a policy may choose *which* ready task runs next, but only ever a
ready task, and the choice changes ordering, not safety. Additive — no new
`RuntimeOp`, no change to `step`/`schedule`, no fairness claim — and still zero
`sorry`, zero new axiom kinds.

- **Interface** (`Henret/Scheduler/Policy.lean`): `SchedulingPolicy`
  (`choose : RuntimeState → Option TaskId` + `choose_sound`, a soundness proof
  that any chosen task is in `readyQ`). The derived runner
  `policyStep p s := step (p.reorder s) .schedule` moves the chosen task to the
  queue head (a permutation) and runs the core `schedule`.
- **Built-in policies**: `fifoPolicy` (head) and `lifoPolicy` (tail), each
  proved sound.
- **Proofs** (`Henret/Proofs/Policy.lean`): `reorder_preserves_wf` (the
  permutation keeps all 33 `WellFormed` fields), and from it
  `policyStep_preserves_wf` — **parametric in the policy**, so every sound
  policy inherits the full invariant. Plus `policy_does_not_create_task`,
  `fifo_policy_equiv_schedule` (FIFO *is* the core `schedule`), and
  `fifo_picks_head` / `lifo_picks_last` (the two policies select opposite ends).
- **Profile**: `schedulingPolicy` is now part of `Profile.full`
  (`full_has_schedulingPolicy`).
- **Docs**: new `docs/scheduling-policy.md`; profile-index corrected (it had
  listed `schedulingPolicy`/`resourceLifetime` as not-yet-in-any-profile);
  proof-index and matrix (claims 196–198) extended.

## v0.20.0 — Fault & Outcome Taxonomy (RFC 064)

Gives Henret a precise, machine-checked vocabulary for the notions English
collapses into "failure": protocol invalidity, ordinary waiting, cancellation,
timeout, task fault, supervisor fault, runtime-adapter failure, and
trusted-backend failure. Purely additive — **no new operations, results, or
axioms; existing semantics unchanged** — and still zero `sorry`.

- **Machine-checked classifier** (`Henret/Diagnostics/Taxonomy.lean`):
  `FaultClass` (`progress` / `waiting` / `timeout` / `protocolInvalid`) and a
  **total** `faultClass : StepResult → FaultClass`, so adding a `StepResult`
  constructor without classifying it is a build error. `StepResult.isFault`
  marks protocol invalidity as the only `StepResult`-reportable fault.
- **Disambiguation theorems** (zero axioms): `blocked_not_invalid_class`,
  `backpressured_not_invalid_class`, `timedOut_not_invalid_class` (waiting and
  timeout are different classes from a rejected operation), and
  `invalid_is_fault` / `blocked_not_fault` / `backpressured_not_fault` /
  `timedOut_not_fault` / `ok_not_fault` (only invalidity is a fault).
- **Taxonomy reference** `docs/fault-taxonomy.md` — the eight classes, the
  `StepResult`→class and `TaskState`→class tables, and which classes are
  state-level (cancellation via `.cancelled`, task fault via `.failed`) or
  reserved/out-of-model (supervisor signal, adapter failure, trusted backend).
  Task-fault payloads, supervisor signals, and richer fault outcomes are
  explicitly **reserved**, not implemented.
- **Sync gate** `scripts/fault_taxonomy_check.py` (wired into the docs-consistency
  gate) verifies the eight class headings exist, every `StepResult` constructor
  is classified, and the doc table matches the Lean `faultClass` definition both
  ways. Guided tour, docs index, and the proof/trust/test matrix (claims
  193–195) updated.

## v0.19.2 — RFC 057 closeout + roadmap refresh

Closes the last RFC 057 loose end and corrects stale planning docs. No model or
invariant changes; **zero `sorry` and zero project axioms**.

- **`released_resource_never_live`** — the previously-deferred theorem now lands
  (`Henret/Proofs/ResourceReachable.lean`). `released_resource_never_live_step`
  (every operation fixes a released record), `released_resource_never_live_run`
  (stable along any run), and `reachable_released_resource_never_live` (stable
  in every reachable future) make `released` a proved terminal ledger state.
  The supporting `step_resources_eq_of_released` case-splits all 24 ops, closing
  the acquire/release/finalize `upd` cases by index-disjointness and the
  terminal-marking cases by `markClosingIf_eq_of_released`. All three are in the
  axiom audit; matrix claim 192.
- **Roadmap refreshed** — `docs/roadmap.md` had drifted to "Current version:
  v0.8.0"; it now reflects v0.19.x (24 ops, 10 results, 33-field invariant), the
  65 implemented RFCs, and the open 058–079 backlog grouped by theme, plus the
  RFC 057 Tier 2 and multi-worker follow-ups.

## v0.19.1 — RFC 057 cleanup: branch theorems, conformance & docs

Completes the items deferred from v0.19.0. No model or invariant changes; this
release is purely additive proofs, executable scenarios, and documentation.
Still **zero `sorry` and zero project axioms**.

- **Per-branch behavioural theorems** (`Henret/Proofs/ResourceBranch.lean`):
  `acquire_running_allocates`, `acquire_not_running_invalid`,
  `acquire_non_running_state_invalid`, `release_owner_allocated_ok`,
  `release_non_owner_invalid`, `release_released_invalid`,
  `release_closing_invalid`, `finalize_closing_ok`,
  `finalize_allocated_invalid`, `finalize_released_invalid`. Each pins the exact
  `StepResult` and ledger record for its branch; all in the axiom audit.
- **Conformance §17** — ten executable `resource_*` scenarios in
  `Henret/Conformance/Branch.lean` (acquire/release happy path, fresh-id
  allocation, non-owner / double-release / wrong-state rejections, terminal
  closing via cancel/fail/complete, closing→released finalize, non-running
  acquire). All kernel-checked under `branch_suite_passes`; each branch is
  registered in `coverage_complete`.
- **Documentation** — new `docs/migration/v0.18-to-v0.19.md` and
  `docs/resource-lifetime.md` (lifecycle diagram, proved/trusted/tested split,
  native-finalizer trust boundary, and the Tier-1 scope boundaries:
  no liveness/timeliness, `stopped` ≠ resource-drained, task-owned only,
  restart = fresh ids). `proof-index.md` and `proof-trust-test-matrix.md`
  (claims 182–191) extended.
- **Still deferred** — `released_resource_never_live` (the
  "released is a terminal ledger state" reachability theorem); its per-op
  index-inequality automation needs a cleaner structured proof and is tracked
  for a later patch. The property holds by construction (the ledger only moves
  records forward) and is exercised by the `resource_*` scenarios; only the
  closed-form theorem is outstanding.

## v0.19.0 — Resource Lifetime & Finalization Ledger (RFC 057, Tier 1)

The model now tracks **task-owned resources** through a two-path lifecycle:
`allocated → released` (synchronous release) and
`allocated → closing → released` (asynchronous finalization). When an owning
task goes terminal, every `allocated` resource it owns is automatically moved
to `closing`, so a live task never holds a dangling-closing resource and a
finalizer is always reclaiming on behalf of a task that has already stopped.
The feature is additive: a program that never calls `acquire` is behaviourally
identical to v0.18. The mathematical core (model + every preservation proof +
the single-worker bridge) is kernel-checked with **zero `sorry` and zero
project axioms**.

- **Model.** New `Henret/Resource/Ledger.lean`: `ResourceId := Nat`,
  `ResourceState` (`allocated`/`closing`/`released`), `ResourceRecord`
  (`{ owner : TaskId, state : ResourceState }`), and `markClosingIf`.
  `RuntimeState` gains `resources : ResourceId → Option ResourceRecord` and
  `nextResourceId : Nat` (init empty / 0). Three operations are added
  (`RuntimeOp` now has **24 constructors**): `acquire t` (running task
  allocates a fresh resource → `.acquired id`), `release t r` (owning running
  task releases an allocated resource → `.ok`), and `finalize r` (environment
  reclaims a closing resource → `.ok`, no running-task guard). `StepResult`
  gains `.acquired` (**10 constructors**). `complete`/`cancel`/`fail` and
  `cancelTree` now also mark owned allocated resources `closing`.
- **Invariant.** `WellFormed` gains four fields (**33 total**):
  `resource_fresh` (ids at/above the counter are unallocated),
  `resource_owner_spawned` (every resource is owned by a spawned task),
  `allocated_owner_nonterminal` (an allocated resource's owner is live), and
  `closing_owner_terminal` (a closing resource's owner is terminal). Carried
  through all of `Preservation/{Lifecycle,Messaging,Time,Resource}` and
  `Supervision`, and projected by `reachable_resource_fresh`,
  `reachable_resource_owner_spawned`, `reachable_allocated_owner_nonterminal`,
  and `reachable_closing_owner_terminal`.
- **Headline theorems.** `preserves_wf_acquire/release/finalize`;
  `nextResourceId_monotone_step`/`_run` (allocation ids never decrease);
  `complete_marks_owned_resource_closing`,
  `cancel_marks_owned_resource_closing`,
  `fail_marks_owned_resource_closing`, and
  `cancelTree_marks_descendant_resource_closing` (terminal coupling).
- **Proof infrastructure.** New `Henret/Proofs/Resource.lean` with reusable
  helpers (`markClosingIf` shape lemmas, `wf_resource_inert`,
  `wf_resource_terminal`, `wf_resources_only`, `wf_flip_to_released`,
  `upd_nonterminal`, `wakeMany_nonterminal`) that close the 33-field
  preservation obligations uniformly.
- **Bridge.** `toQOps` emits `[]` for the three ledger operations (they never
  touch the ready queue); `bridge_acquire/release/finalize` keep the
  single-worker projection stable.
- **Profile.** `resourceLifetime` `SemanticFeature` is now part of
  `Profile.full`, with `full_has_resourceLifetime`.
- **Deferred (follow-up).** `released_resource_never_live`, the per-branch
  result theorems, the §17 conformance scenarios, and the
  `migration/v0.18-to-v0.19` + `resource-lifetime` guides remain to land in a
  v0.19.x cleanup; the kernel-proven core above is complete and gate-green.

## v0.18.0 — Bounded Mailboxes & Backpressure (RFC 056, Option A reject-only)

Mailboxes can now carry a per-actor capacity bound; an over-capacity `send` or
`inject` is **rejected** with a new no-op `.backpressured` result. The feature
is purely additive and the default policy is unbounded, so any v0.17 program is
behaviourally identical until it configures a bound. The mathematical core
(model + every preservation proof + the single-worker bridge) is kernel-checked
with **zero `sorry` and zero project axioms**.

- **Model.** New `MailboxPolicy` record (`{ capacity : Option Nat }`,
  `.unbounded := { capacity := none }`) and `RuntimeState.mailboxPolicy`
  (init `fun _ => .unbounded`). `StepResult` gains `.backpressured` (9
  constructors, before `.invalid`). `RuntimeOp` is unchanged (21 constructors).
  `send`/`inject` consult the policy **after** every validity guard; a full
  mailbox yields `.backpressured` with no state change and no occurrence-id
  consumption. Capacity zero is a documented reject-all policy.
- **Invariant.** `WellFormed` gains field **29**, `mailbox_within_capacity`
  ("no mailbox exceeds its configured capacity"), vacuous under the unbounded
  default. Carried through all three `Preservation/{Lifecycle,Messaging,Time}`
  proofs and projected by `reachable_mailbox_within_capacity`.
- **Headline theorems.** `step_backpressured_unchanged`,
  `backpressured_not_invalid`, `send_full_backpressured`,
  `inject_full_backpressured`, `send_unbounded_not_backpressured`,
  `inject_unbounded_not_backpressured`.
- **Bridge.** `toQOps` is capacity-aware (emits `[]` for a full mailbox);
  `bridge_send`/`bridge_inject` stay queue-stable under backpressure.
- **Profile.** New `boundedMailbox` `SemanticFeature`, added to `Profile.full`
  with `full_has_boundedMailbox`.
- **Conformance.** Nine new kernel-checked `BranchScenario`s under
  `branch_suite_passes` (cap-1 ok→backpressured, receive-frees, inject-full,
  capacity-zero send+inject, unbounded-never, and both full-mailbox-with-waiter
  variants — proving a Mesa waiter does not imply an empty mailbox); branch IDs
  registered in `coverage_complete`.
- **Docs.** New `docs/migration/v0.17-to-v0.18.md`; `Meta/Docs`, generated
  tables, the proof index, the trust/test matrix, the assurance case, the
  integration contract, the profile index, and the evidence ledger updated to
  the 29-field / 9-result model. Option B (park-policy / blocking senders) is
  explicitly out of scope.

## v0.17.7 — Model-to-Documentation Extraction (RFC 084 full, implements RFC 075)

The recurrently-drifting documentation tables are now generated from a single
checked source and diffed in the gate suite, removing the whole drift class
(the `doc_count_check.py` stopgap shipped earlier in v0.17.2 stays as a
hand-written-doc guard).

- **`Henret/Meta/Docs.lean`** (new `HenretMeta` lib, import-cheap per 084-5) is
  the checked descriptor source: `ConstructorDoc`/`FieldDoc` lists for the 21
  `RuntimeOp`s, 10 `TaskState`s, 8 `StepResult`s, and 28 `WellFormed` fields.
- **`scripts/extract_model_docs.py`** validates each metadata list against the
  real Lean declarations — every name resolves to an actual constructor/field,
  names are duplicate-free, the metadata count equals the real count (084-1) —
  before emitting any table.
- **`scripts/extract_theorem_docs.py`** emits the public-theorem index and the
  axiom budget from the gate-validated audit allowlist (62 theorems: 42 STD, 19
  STD_C, 1 native; the public-theorem source of truth, 084-4).
- **`scripts/extract_rfc_index.py`** emits the RFC index from RFC 085 front
  matter.
- **Committed `docs/generated/`** (seven files): the four model tables, the
  public-theorem index, the axiom budget, and the RFC index. Gate 7 regenerates
  and diffs them; divergence fails (084-2). All three generators are in the
  release manifest's policy hashes.

## v0.17.6 — Preservation Proof Ergonomics v2 (RFC 082, supersedes RFC 042)

Realises the goal RFC 042 set but did not finish: the eight `wf_*_pass`
preservation helpers the v0.17.0 audit found **dead** are now adopted, with a
durable gate so they cannot drift back to unused. No semantic model behavior
changed; `reachable_wf` and the public theorem surface are unchanged; no new
project axioms.

- **All eight A1 helpers adopted**: `wf_parent_spawned_pass` (replacing an
  eight-line `by_cases` bullet with two lines) and the bundled `wf_occ_pass` in
  the `sleep` preservation proof; the six RFC 040 `wf_timed_*_pass` helpers in
  the `send`/`inject` no-waiter case. Guards stay visible in each proof (082-C);
  no helper is `@[simp]`.
- **`scripts/helper_usage_check.py`** (gate stage 7) requires every exported
  `wf_*_pass` to be used — its identifier present outside `StepFields.lean`
  after stripping Lean comments and string literals (082-1) — or carry a valid
  `HENRET_HELPER_RESERVED: reason; rfc; expiry` annotation (082-2). The eight A1
  helpers must be used, never annotated-away. Added to the release manifest's
  policy hashes.
- **Metrics and the 082-D naming convention** recorded in
  `docs/proof-engineering.md`: 12/12 exported helpers used, A1 8/8, ~405 field
  bullets, `InvariantsPreservation` import count 6 (unchanged). The 15–25%
  line-reduction target is informative, not blocking (082-B); this pass
  establishes adoption and the gate, sequenced to precede RFC 056.
- **RFC 042 superseded**: moved to `rfcs/archive/`, status `Superseded by RFC
  082`. Its `StepFields.lean` helpers remain in use.

## v0.17.5 — Golden Conformance Coverage Expansion (RFC 083)

The golden conformance suite is back in line with the grammar. Alongside RFC
047's 10 trace scenarios, an executable **branch-coverage suite** pins the
exact `StepResult` sequence and an executable final-state predicate for every
operation/branch added since RFC 033, and a coverage registry ties every
executable `RuntimeOp` branch to a named scenario.

- **`Henret/Conformance/Branch.lean`** — 27 `BranchScenario` values (083-3):
  17 positive (receiveUntil ×4, selective receive ×4, fail, restartOne,
  closeActor, shutdown, stopWhenIdle ×2, wake, cancelTree, and the **Mesa
  re-park regression** `mesa_woken_task_can_repark`, 083-4) and 10
  negative/security scenarios (non-running/unowned/waiting-task rejections,
  closed-actor and shutdown rejections, cancelled-task non-schedulability,
  stale-timer non-wake). Every expected `StepResult` sequence was extracted
  from the model by evaluation; branch ids are stable and namespaced (083-2).
- **`Henret/Conformance/Coverage.lean`** — the coverage source of truth in
  Lean, not markdown (083-D): 44 branches across all 21 `RuntimeOp`s, each
  tied to a trace scenario (pre-RFC-033 ops) or a branch scenario. Closed-actor
  and shutdown rejections are explicit branches (083-5).
- **Two kernel-checked gates** (`by decide`, no `native_decide`):
  `branch_suite_passes` over the kernel-reducible scenarios and
  `coverage_complete` over the registry. `cancelTree` uses well-founded
  recursion that does not kernel-reduce, so it is runtime-checked by the
  executable suite and covered by the `Supervision.lean` cascade-cancel proofs.
  Both theorems are axiom-audited (62 allowlisted, up from 60).
- The **conformance executable** now runs the trace suite, branch suite, and
  coverage registry, exiting non-zero on any failure (RFC 080 gate stage 6).
- The axiom-audit parser now recognizes axiom-free theorems
  ("does not depend on any axioms") as an empty axiom set.

## v0.17.4 — Warning Hygiene and Public Lemma Tightening (RFC 086)

The full gate-scope build now emits **zero warnings**. No project axioms were
added and no semantic model behavior changed (the axiom audit over the 60
headline theorems is unchanged); some helper-lemma *types* were tightened by
dropping genuinely unused hypotheses, which is accepted pre-public-stability
(086-B).

- **`scripts/warning_budget.py`** — fills the RFC 080 stage-10 gate. Parses the
  gate's build log and enforces a total-warning budget of zero (086-1) and an
  unused-variable budget of zero, with an explicit, justification-bearing
  allowlist for any exception (086-D). It consumes the build/example/demo logs
  the earlier gates capture (086-4); authoritative on the fresh CI build.
- **Unused proof-local / pattern bindings underscored** (no type change):
  `isInSubtreeOf` (`_hp`, also in `decreasing_by`), `toQOps` `restartOne`
  (`_actor`), and the `send`/`inject` trace branches (`_m`).
- **Seven helper lemmas tightened** — genuinely unused hypotheses dropped
  (086-2 migration table):

  | lemma | dropped hypotheses | downstream | wrapper |
  |---|---|---|---|
  | `step_taskParent_stable` | `hfresh` | none (0 callers) | no |
  | `step_preserves_parent` | `hfresh` | 2 calls in `Restart.lean` (updated) | no |
  | `bridgeState_pop0` | `t`, `hq` | none (0 callers) | no |
  | `receiveByOccurrence_removes_matching` | `s,t,a,hrt,hts,how,hmb` | none | no |
  | `receiveFrom_source_matches` | `s,t,a,hrt,hts,how,hmb` | none | no |
  | `receiveByOccurrence_preserves_nonmatching_order` | `s,t,a,hmb` | none | no |
  | `receiveFrom_preserves_nonmatching_order` | `s,t,a,hmb` | none | no |

  Each was reviewed (086 formal-verification note): the lemma is genuinely
  stronger and no admission guard was lost. No `@[deprecated]` wrappers are
  needed — none of these is public-stable under RFC 070, so they are tightened
  directly (086-3).

## v0.17.3 — Package Boundary and Evidence Ledger (RFC 081)

Non-semantic release: documentation, governance, and tooling only. No Lean
model, proof, or axiom-budget change.

- **`docs/evidence-ledger.yaml`** — machine-readable source of truth (081-1)
  for every headline claim, recording its `tier`, `evidence_location`,
  `verified_by_this_tarball`, and `verified_by_ci` over a closed vocabulary
  (081-B). In-tree model proofs/tests are marked verified-here; the
  out-of-tree runtime harnesses (differential, linearizability, stress,
  executor) carry `evidence_location: sibling_runtime_package` and
  `verified_by_this_tarball: false` with an explicit null posture (081-2).
  `TRUSTED` (the FFI axioms) and `TESTED` are never collapsed.
- **`scripts/forbidden_claim_check.py`** — validates the ledger schema
  (namespaced stable `claim_id`s, in-tree⇔verified-here, out-of-tree
  coordinates-or-null), regenerates and diffs `docs/evidence-ledger.md`
  (081-1), and runs the forbidden-claim gate: a phrase list + allowed-context
  patterns + ledger validation (081-4) that rejects any live-doc claim
  implying this tarball verifies the out-of-tree runtime tests (081-C). Wired
  into the RFC 080 doc-consistency gate.
- **`docs/package-boundary.md`** — enumerates the model package and the
  sibling runtime package, their evidence locations, and the shared-toolchain
  link.
- **`docs/proof-trust-test-matrix.md`** — every row now carries an
  evidence-location and verified-here column; a legend note clarifies that
  `TESTED` here means in-tree checks, not the out-of-tree runtime harnesses.
- **`README.md`** — honesty-ledger wording points to the evidence ledger and
  package boundary and states the in-tree/out-of-tree posture; removed a
  stale running field-count.
- **`scripts/release_manifest.py`** — the manifest `runtime_package` block now
  references the evidence ledger, and `forbidden_claim_check.py` joins the
  hashed gate policy.

## v0.17.2 — Release Gate Integrity (RFC 080) + doc count-check stopgap (RFC 084)

Non-semantic release: tooling, gates, CI, and documentation only. No Lean
model, proof, or axiom-budget change; the kernel-proven build, the strict
axiom audit (60 theorems), and the golden conformance suite are unaffected.

**RFC 080 — Release Gate Integrity and Evidence Manifest.**
- `scripts/check.sh` rewritten with explicit `--fast` (local pre-check;
  skips the demo; emits no manifest) and `--release` (full suite + manifest)
  modes (080-A). Every gate runs through a `run_gate` wrapper that times,
  captures, and hashes its stdout/stderr.
- `scripts/check_selftest.py` is gate **stage 0** (080-3): it verifies gate
  ids are unique and named, the axiom-audit allowlist matches the
  `#print axioms` inputs exactly (the drift that silently broke the suite
  before v0.17.0), the doc-symbol and doc-consistency target sets are
  non-empty, and the warning-budget gate is wired.
- `scripts/release_manifest.py` emits `release/release-verification.json`, a
  non-manual, hashed manifest (080-B): schema, version, git commit/dirty,
  `tarball_sha256`, toolchain/lake hashes, `gate_policy` script hashes
  (080-2), per-gate status/duration/log hashes, and a `runtime_package`
  placeholder for RFC 081. The manifest is **external** to the source tarball
  whose hash it records (080-1); `--release` fails on a dirty source tree
  except for generated `release/` artifacts (080-4); when not in a git work
  tree the run is marked a local pre-check (CI is authoritative, 080-D).
- `.github/workflows/ci.yml` runs `--fast` on pull requests and `--release`
  on pushes/tags, uploading the manifest, `release/GATE-RUN.md`, and logs.
- Stages 4 (RFC 083 coverage) and 9 (RFC 086 warning budget) are wired as
  documented stubs, to be filled by their own RFCs.

**RFC 084 stopgap — `scripts/doc_count_check.py`.** Computes the current
`RuntimeOp` (21), `TaskState` (10), `StepResult` (8) constructor counts and
the `WellFormed` field count (28) from the Lean source of truth and fails the
doc-consistency gate when a live doc states a contradicting count;
historical-narrative lines and historical/generated files are excluded. Fixed
three live drift sites it found (`README.md` 19→28, `docs/proof-index.md`
`preserves_wf_spawnChild` 21→28-field, and a proof-matrix entry reworded to
"every `RuntimeOp`"). Partial RFC 084; the full generator remains deferred.

## v0.17.1 — RFC Metadata Normalization (RFC 085)

Non-semantic tooling/documentation release. No Lean model, proof, or
conformance behavior changed; the kernel-proven core, the zero-`sorry` /
zero-project-axiom invariant, and all 10/10 conformance scenarios are
unaffected.

- **Canonical RFC front matter.** All 87 RFCs (including the RFC 000 lifecycle
  policy) now carry a single machine-readable YAML front-matter block:
  `rfc`, `title`, `status` (`Draft | Proposed | Implemented | Withdrawn |
  Superseded`), `implemented_in` (`vX.Y.Z` when Implemented, else `null`),
  `supersedes`, `superseded_by`, `depends_on`, `blocks` (bare-integer RFC-number
  lists), and `category`. This replaces the three legacy status formats
  (YAML-ish front matter, `**Status.**`, `## Status`).
- **Linter (`scripts/rfc_metadata_check.py`).** Dependency-light (stdlib-only)
  checker enforcing the schema: per-file front-matter validity, `rfc`/filename
  agreement, closed status set, folder/status consistency, version-pattern for
  `implemented_in`, bare-integer cross-reference lists pointing to existing
  RFCs, and unique RFC numbers. Loose slug/title correspondence is advisory.
  Wired as `check.sh` gate 10/10.
- **One-shot migration (`scripts/migrate_rfc_frontmatter.py`).** Idempotent;
  folder is the source of truth for status (RFC 000).
- **RFC 000 mandates the schema** and moved to `rfcs/done/` (consistent with its
  own policy); `rfcs/README.md` and `CONTRIBUTING.md` references updated.

Known follow-up (deferred to RFC 084): the `rfcs/README.md` index still lists
implemented RFCs 040–055 under the "Proposed" table; RFC 084 will regenerate the
index from this front-matter metadata.

## v0.17.0 — Structured Cancellation and Shutdown (RFC 055)

The first true semantic-core extension since RFC 040, and deliberately
**safety-only**: it adds orderly-shutdown *admission control* without any
fairness, liveness, or guaranteed-quiescence claim.

### New surface (additive)

Two enums — `ActorStatus` (`active | closed`; `open` is a Lean keyword)
and `RuntimeStatus` (`running | shuttingDown | stopped`) — and two
`RuntimeState` fields, `actorStatus` and `runtimeStatus`. The operation
grammar grows to twenty-one constructors with `closeActor`, `shutdown`,
and `stopWhenIdle`. A computable `RuntimeQuiescent` predicate (no running
task, empty ready queue, no pending timers) is the idle condition
`stopWhenIdle` checks.

### Admission semantics

`closeActor a` flips actor `a` to `.closed` (invalid if it has no
mailbox) and never deletes mailbox contents — closing rejects *future*
`send`/`inject` to `a` while still allowing `receive` to drain queued
messages. `shutdown` rejects root `spawn` and environment `inject` while
letting in-flight work continue. `stopWhenIdle` reaches `.stopped` only
from a quiescent state. Subtree cancellation is the existing `cancelTree`
(RFC 039) — no new cancellation operation was added.

### Proofs

New `Henret/Proofs/Shutdown.lean` carries the safety theorems
(`closeActor_sets_closed`, `closeActor_preserves_mailboxes`,
`closed_actor_rejects_send`, `closed_actor_rejects_inject`,
`shutdown_rejects_spawn`, `shutdown_sets_status`,
`stopWhenIdle_requires_quiescent`, `stopWhenIdle_sets_stopped`, and
companions), all kernel-proven on `{propext, Quot.sound}`. The new
admission-status fields are `WellFormed`-irrelevant — the 28-field base
safety contract is byte-for-byte unchanged via the new
`WellFormed.status_irrel`, with `preserves_wf_{closeActor,shutdown,
stopWhenIdle}` and an outer guard `by_cases` wrapping the three guarded
operations' preservation. Bridge preservation (`bridge_closeActor` /
`bridge_shutdown` / `bridge_stopWhenIdle`) is queue-stable. Trace events
`actorClosed` / `shutdownBegun` / `stoppedWhenIdle` were added.

Zero `sorry`, zero project axioms. Example `16_structured_shutdown.lean`;
see `docs/shutdown-semantics.md` and `docs/migration/v0.16-to-v0.17.md`.



A semantic-profile vocabulary so a consumer can name the subset of
Henret's semantics it depends on, and a theorem can be labelled with the
minimum profile it requires. **Profiles are metadata** — they change no
existing theorem and no `step`/`run` behavior.

### Profile vocabulary (kernel-proven)

New `Henret/Profile.lean` defines `SemanticFeature` (nine features,
including reserved `schedulingPolicy`/`resourceLifetime` for future
RFCs), `SemanticProfile` (a duplicate-free feature set), and the named
profiles `Profile.core` ⊂ `Profile.actor` ⊂ `Profile.full`. The
inclusion chain is kernel-proven — `core_le_actor`, `actor_le_full`,
`core_le_full`, plus `SemanticProfile.le_refl`/`le_trans` — and each
named profile carries a `by decide` `nodup` proof. All depend only on
`propext` (kernel `decide`, no `Classical.choice`, no `native_decide`).

### Documentation

New `docs/profile-index.md` maps the headline theorems to their minimum
profile (core / actor / full) and the examples to their profiles. The
README gains a "Which Henret profile should I use?" section; the
proof/trust/test matrix points to the profile index rather than carrying
a per-row column (avoiding duplication). `examples/15_semantic_profiles.lean`
demonstrates the vocabulary and discharges the inclusion chain.

### Import behavior

`import Henret` now additively includes the profile vocabulary. No
existing theorem statement or model behavior changes; the profile facts
are an independent namespace.

### Axiom budget

The three inclusion theorems are added to the audit allowlist (propext
only). Otherwise unchanged.

---

## v0.15.4 — Assurance Case and External Review Playbook (RFC 053)

A reviewability release. **No new semantics, no new theorems, axiom
budget unchanged** — it turns Henret's existing proof/trust/test
discipline into a structured argument an external reviewer can audit.

### Assurance case

New `docs/assurance-case.md` states the top-level claim and decomposes it
into subclaims C1–C10, each linked to its headline theorem, file, axiom
set, and class (kernel-proven / trusted / tested / conditional /
out-of-scope). It links to the proof index and matrix rather than copying
them, and ships a release sign-off template.

### Review playbook and risk register

New `docs/review-playbook.md` is a falsification-oriented checklist for an
external reviewer (claim integrity, axiom budget, bridge honesty, grammar
migration, packaging). New `docs/risk-register.md` records seven
residual risks (R1–R7) with likelihood, impact, mitigation, and status —
including the bridge's single-worker scope, the trusted C boundary, and
the demo-codegen cost — and a never-delete retirement policy.

### Wiring

The README claims bullet now points to the assurance case, review
playbook, and risk register; the docs landing page indexes them under
maintainers; the release checklist requires the assurance C-table and
risk register to be updated each release.

---

## v0.15.3 — Semantic Extension Governance (RFC 052)

Governance for changing the semantic core. **No new semantics, no new
theorems, axiom budget unchanged** — process and documentation that keep
theorem, doc, and bridge claims from drifting apart.

### Governance doc and RFC template

New `docs/semantic-extension-governance.md` defines the eight
semantic-core files, the ten-point **Semantic Impact Checklist** required
for any change to them, theorem stability levels, the deprecation-alias
rule, the bridge-claim rule, and the stale-phrase registration process.
New `rfcs/TEMPLATE.md` carries the checklist so new RFCs include it.

### Theorem stability classification

`docs/proof-index.md` gains a stability table classifying public theorems
as **Stable** (the headline reachability contract — promised to remain or
deprecate with an alias), **Experimental** (newer bridge / restart /
progress / conformance / trace layers), or **Internal** (step-local and
preservation lemmas, no public stability).

### Bridge-claim rule, enforced

The rule — never call the bridge "complete" without the *single-worker*
qualifier — is now a stale-phrase gate. Applying it caught and fixed real
drift: `proof-index.md` described the bridge as complete without the
single-worker qualifier and still cited a 12-op grammar count (it is 18,
and the bridge is a single-worker projection). The gate also bans the
stale grammar-count phrasing.

### Gate

`scripts/check.sh` gains an RFC 052 stale-phrase block enforcing the
bridge-claim rule and grammar-count phrasing.

---

## v0.15.2 — Package, Documentation, and Release Maturity (RFC 051)

A consolidation release: **no new semantics, no new theorems, axiom
budget unchanged.** Library character and release habits.

### Documentation structure

New `docs/README.md` landing page indexed by persona (new users /
intermediate / maintainers). New `docs/release-policy.md` (conservative
pre-1.0 versioning + changelog policy), `docs/release-checklist.md` (the
gates that must pass before an archive is cut), and
`docs/theorem-naming.md` (the `step_`/`reachable_`/`preserves_wf_`/
`bridge_` conventions the corpus already follows).

### Migration notes

New `docs/migration/` with a template and `v0.14-to-v0.15.md` documenting
the RFC 049 grammar change (`TaskState.failed`, the `fail`/`restartOne`
operations, the `restartOf` field) — additive, with compiler-caught
`match` breaks only.

### Release gate runner

`scripts/check.sh` extended to nine gates run by one command: it now
builds the explorer library and runs the golden-trace conformance suite
(RFC 047), and the strict axiom audit now covers the RFC 049 restart
headlines. Building the comprehensive gate surfaced a latent
missing-`match` case in `Henret/Examples/Basic.lean` (`showState` lacked
`.waitingTimed`/`.failed`) that the library-only build had skipped — now
fixed.

### Package metadata

`lakefile.lean` carries a description, keywords, repository-URL
placeholder, and an explicit `version`. README hero gains license, Lean
version, sorry-free, and axiom-budget badges.

---

## v0.15.1 — Observability and Pedagogical Visualization (RFC 050)

Human-readable renderers for states, traces, and actor/task relations.
Pure `String` functions in `Henret/Render/` (`Trace`, `State`, `Diagram`)
with aggregator `Henret/Render.lean` — outside the proof-critical path,
adding **no theorems** and leaving the axiom budget unchanged.

### What it renders

- `TraceEvent.render` / `Render.traceTable` — one event / a numbered
  transition table (covers all 18 event constructors, including the new
  `failed`/`restarted`).
- `RuntimeState.render` / `Render.locationMap` — a one-screen state
  summary and a per-task location map that directly explains the
  `WellFormed` location invariants.
- `Render.mailboxView` — actor mailbox contents and waiter lists.
- `Render.parentTreeMermaid` / `mailboxMermaid` — Mermaid diagrams with
  restart provenance annotated; no external library needed.
- `Render.bridgeWorkerQueues` — the single-worker bridge projection.

### Examples and docs

`examples/13_trace_rendering.lean` renders a parking/wake/timer scenario;
`examples/14_state_diagrams.lean` renders a supervision tree as a
location map, Mermaid parent tree, mailbox diagram, and bridge
projection. `docs/observability.md` shows the rendered output and uses it
to explain a non-trivial scenario.

### Scope

Renderers are generated directly from the current data structures, so
they stay correct as the model evolves. Not a GUI; never enters the proof
kernel.

---

## v0.15.0 — Supervision Restart Policies (RFC 049)

A small semantic nucleus for failure and one-for-one restart, built on
the parenthood and cascade-cancel groundwork. This is the first model
addition since RFC 040, touching the core `step`, the 28-field
`WellFormed` preservation, parenthood, the trace ledger, and the bridge.

### Failure distinct from cancellation

New terminal task state `TaskState.failed`, distinct from `.cancelled`,
so supervisors can restart *failures* rather than intentional cancels.
New operation `fail t` performs the same cleanup as `cancel` (dequeue,
drop timer, remove from waiter lists) but lands in `.failed`.

### One-for-one restart

New operation `restartOne parent failedChild actor` creates a fresh
replacement child for a failed task, recording provenance in the new
`RuntimeState.restartOf` field (`restartOf new = some old`). Guards: the
parent is running, the failed child is parented by it and is `.failed`,
and a fresh id is available.

### Base invariant preservation

`preserves_wf_fail` mirrors `preserves_wf_cancel`. `preserves_wf_restartOne`
reduces to `preserves_wf_spawnChild` via the helper
`WellFormed.restartOf_irrel` — no `WellFormed` field mentions `restartOf`,
so the restart's state is the spawnChild state plus an irrelevant
provenance update. Both are wired into `step_preserves_wf`. The
`taskParent`-writer projection was honestly corrected: `restartOne` also
writes `taskParent`, so `step_taskParent_stable` now excludes it too.

### Provenance invariants (separate from WellFormed)

A separate `RestartWellFormed` structure keeps the base contract
untouched. Three facts hold in every reachable state:
`restart_parent_consistent` (replacement and failed task share a parent),
`restart_old_failed` (the replaced task is `.failed`), and
`restart_fresh` (`old < new`, restart acyclicity). Headlines:
`reachable_restart_fresh`, `reachable_restart_old_failed`,
`reachable_restart_parent_consistent`,
`restart_preserves_parent_acyclicity`, and `restarted_task_has_owner`.

### Trace, bridge, example, docs

Trace events `failed`/`restarted` (RFC 045). Bridge cases `bridge_fail`
(Filter) and `bridge_restartOne` (Push) keep the single-worker bridge
total. `examples/12_supervision_restart.lean` shows a supervisor → child
fails → restart flow with the invariants discharged.
`docs/supervision-restart.md` documents the design and non-goals.

### Axiom budget: unchanged

All new theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`. No project axioms.

---

## v0.14.1 — Bounded Model Explorer and Shrinker (RFC 048)

A development/testing tool that enumerates small `RuntimeOp` sequences,
checks executable property predicates over a bounded world, and shrinks
counterexamples by deletion. New module `Henret/Explore/` (`Gen`,
`Check`, `Shrink`) in the separate `HenretExplore` Lake library, plus a
`henret-explore` executable.

### Outside the verified model

The explorer lives **outside** the default `import Henret` path and adds
**no theorems** — it does not affect the verified model or its axiom
budget. The checkers are bounded *necessary* conditions, documented as
testing-only: they are deliberately not connected to soundness theorems
(which would be false, since `WellFormed` quantifies over infinite
domains). Their role is to confirm the proven invariants over a sample
and catch regressions.

### What it does

- `genOps`/`genPrograms` enumerate operation sequences over a tiny
  `SmallWorld` (default: 2 tasks, 2 actors, 1 message, 2 time points).
- `propWellFormed`, `propOccurrenceUnique`, `propBridge` confirm the
  proven invariants; `propReadyAlwaysEmpty` is a deliberately false
  property for the shrinker demo.
- `explore`/`confirms` search; `shrinkProgram`/`findAndShrink` minimize
  counterexamples by deletion to a fixed point.

### Executable

`lake exe henret-explore` confirms all three proven invariants over
25,260 programs (depth 3) and shrinks the false property to its minimal
counterexample `[spawn 0]`.

### Docs

`docs/model-explorer.md` documents the tool and its empirical scope.

---

## v0.14.0 — Fairness and Conditional Liveness Layer (RFC 046)

An **optional** policy layer for conditional progress reasoning. Henret's
core stays a safety model — nothing here is added to `WellFormed`, and no
unconditional liveness is claimed. New module `Henret/Progress/`
(`Policy`, `Examples`) with aggregator `Henret/Progress.lean`.

### The honesty story

The model's `readyQ` is **FIFO** (`schedule` takes the head; `yield`,
`spawn`, and wakeups append to the tail), so one progress fact is
genuinely unconditional and local:

```lean
theorem schedule_schedules_head : ... → (step s .schedule).2 = .scheduled t
```

But whole-program fairness is **not** unconditional. An op sequence that
stops issuing `schedule` starves runnable tasks — and this is
representable:

```lean
theorem unfairOps_not_bounded_fair_0 :
  ¬ BoundedReadyFair 0 RuntimeState.init unfairOps
```

### Conditional progress

`BoundedReadyFair k s ops` is the explicit scheduling assumption (a
property of the op sequence, not of `WellFormed`). Under it,
`ready_eventually_scheduled_under_bounded_fairness` gives bounded
progress. The theorem is deliberately close to tautological — its value
is making the assumption explicit and reusable.

### Fair / unfair witnesses

Kernel-checked (`by decide`): `fair_task0_scheduled`,
`fair_task1_scheduled` (a fair schedule), and `unfair_task1_runnable`,
`unfair_task1_never_scheduled` (a starving schedule).

### Docs

`docs/progress-policy.md` documents the layer and its honesty ledger:
unconditional local head-progress, conditional whole-task progress, and
representable starvation.

### Axiom budget: unchanged

All progress theorems depend only on `propext` and `Quot.sound` (the
`decide`-based ones use no `native_decide`). No project axioms.

---

## v0.13.1 — Golden Trace Conformance Suite (RFC 047)

A behavioral conformance suite built on the RFC 045 trace ledger.
External runtimes compare their observed `TraceEvent` traces against
Henret's canonical golden traces to certify conformance. New module
`Henret/Conformance/` (`Scenario`, `Golden`, `Export`) with aggregator
`Henret/Conformance.lean` and a `henret-conformance` executable.

### Scenario infrastructure

`GoldenScenario` pairs a named operation sequence with the canonical
`TraceEvent` trace Henret produces. `observe`/`checkScenario` run and
check; `firstMismatch` reports the first differing event; `TraceRefines`
is the refinement relation (exact equality in v1, per the RFC).

### Ten golden scenarios

`spawn_schedule_complete`, `yield_requeues`, `sleep_tick_wakes`,
`empty_receive_parks`, `send_wakes_waiter_mesa`,
`inject_wakes_waiter_mesa`, `cancel_ready_task`, `cancel_waiting_task`,
`spawn_child_parent_lt`, `occurrence_unique_two_mailboxes`.

### Kernel-checked regression gate

```lean
theorem conformance_suite_passes : allPass = true := by decide
```

Verified by `decide` (not `native_decide`, so no extra axioms). Any
change to `step` or `traceEvents` that alters observable behavior breaks
this proof — golden traces cannot silently drift from the semantics.

### Executable

`lake exe henret-conformance` prints a per-scenario PASS/FAIL report and
exits non-zero on any failure.

### Docs

`docs/conformance-suite.md` documents the suite, the refinement relation,
and the adapter contract for external runtimes (which need only expose
the observable event stream, not internal queues).

---

## v0.13.0 — Execution Trace Ledger (RFC 045)

Makes execution traces first-class. Each operation now emits, alongside
its ordinary `(state, result)` effect, a list of semantic `TraceEvent`s
— which task was scheduled, which envelope delivered, which task parked,
which timer fired. New module `Henret/Trace/` (`Event`, `Run`,
`Theorems`) with aggregator `Henret/Trace.lean`, wired into the top-level
`Henret` import.

### Event vocabulary

`TraceEvent` has one constructor per meaningful runtime observation:
`spawned`, `spawnChild`, `scheduled`, `yielded`, `completed`,
`cancelled`, `slept`, `timerWoke`, `directWoke`, `sent`, `injected`,
`received`, `parked`, `waiterWoke`, `invalid`, `noEffect`.

### Agreement by construction

`stepTrace` reuses `step` for its state and result and only *adds* a
separate `traceEvents` computation, so the agreement theorems are
definitional:

- `stepTrace_state_eq_step` — `(stepTrace s op).1 = (step s op).1` (`rfl`);
- `stepTrace_result_eq_step` — result agrees (`rfl`);
- `runTraceLedger_state_eq_run` — final state agrees with `run` (induction);
- `runTraceLedger_results_eq_runTrace` — result list agrees with `runTrace`.

There is no risk of the ledger drifting from the semantics, because it
never recomputes the state.

### Event soundness

Seven soundness theorems certify that an emitted event reflects a real
semantic fact: `event_received_sound`, `event_parked_sound`,
`event_directWoke_sound`, `event_timerWoke_sound`,
`event_spawnChild_sound`, `event_scheduled_sound`, and
`event_waiterWoke_send_sound`. Each is a guard-case analysis, since
`traceEvents` mirrors `step`'s guards exactly.

### Example and docs

`examples/11_trace_ledger.lean` prints a readable trace and discharges
the agreement and soundness theorems. `docs/trace-ledger.md` documents
the design.

### Axiom budget: unchanged

All trace theorems depend only on `propext` and `Quot.sound`. No project
axioms. Verified by `scripts/axiom_audit.py`.

---

## v0.12.1 — Runtime Integration Contract (RFC 044)

Documentation and ecosystem-maturity release. No model or proof changes;
the public surface is unchanged. Adds a stable boundary contract for
downstream consumers.

### New: `docs/integration-contract.md`

The boundary contract for projects using Henret as a semantic reference
model. Ten sections:

1. **Project role** — Henret is a reference model, not a runtime library.
2. **Stable imports** — stability levels per import (`Henret.Model` and
   `Henret.Proofs` are fully stable; `Henret.Native.*` is trusted;
   examples are unstable).
3. **Operation mapping** — external runtime events → all 16 `RuntimeOp`s.
4. **Mesa semantics contract** — wake-one, no atomic handoff, re-run
   receive; selective receive parks at mailbox level.
5. **Occurrence identity contract** — fresh ids, global uniqueness,
   `send`/`inject` source stamping.
6. **Supervision contract** — acyclic parenthood, cascade cancel
   (`cancelTree`) stable since v0.10.0; restart policies not yet modeled.
7. **Bridge contract** — single-worker (exact) and multi-worker
   (membership) levels; headline theorems; no native-concurrency claim.
8. **Theorem contract** — the public theorem table; warning not to depend
   on internal `preserves_wf_*` / `step_*` / `toQOps_*` helpers.
9. **Trust boundary** — kernel-proven / trusted / tested / out-of-scope.
10. **Versioning policy** — what counts as breaking vs non-breaking.

### New: `examples/10_integration_contract.lean`

A worked consumer trace: maps a small actor scenario to Henret ops, runs
it, and discharges `reachable_wf` and `reachable_occurrence_unique` on
the result — using only the public theorem surface.

### README

Adds a "Using Henret in your own project?" pointer to the integration
contract in the learning path.

---

## v0.12.0 — Multi-Worker Bridge Model Extension (RFC 043)

Generalises the bridge from a single-worker queue projection to a
**membership-based** multi-worker projection suitable for comparison with
`lean-runtime`'s work-stealing scheduler. New file
`Henret/Bridge/MultiState.lean`.

### `MultiBridgeState` (Option B — membership)

Relates henret's `readyQ` to the *union* of all worker queues by
membership, not order:

- `sound` — every queued task is ready;
- `complete` — every ready task is queued on some worker;
- `worker_nodup` — each worker queue is duplicate-free;
- `global_unique` — a task is queued on at most one worker.

Order is deliberately not preserved: a work-stealing scheduler does not
maintain a single global ready order, so a membership relation is the
right invariant — it survives `Steal` where list-equality would not.

### Multi-worker `Steal` semantics

`applyMQOp`'s `Steal src dst` actually moves the head of `src`'s queue to
`dst`'s tail (the single-worker `applyQOp` left `Steal` a no-op).
`Wake`/`Inject` target worker 0 (wake-to-worker-0 policy, deterministic
and compatible with the single-worker projection).

### Theorems

- `single_bridge_implies_multi_bridge` — the single-worker `BridgeState`
  is a strict special case (given `readyQ.Nodup`).
- `multi_bridge_push`, `multi_bridge_filter`, `multi_bridge_steal` —
  per-op membership preservation. `multi_bridge_steal` is the headline:
  work stealing moves a task between workers without changing the ready
  set.
- `reachable_multi_bridge` — every reachable state has a `WorkerQueues`
  witness satisfying `MultiBridgeState`, via the single-worker trace
  theorem and `reachable_wf.readyQ_nodup`.

### Design constraint honoured

No worker-placement field added to `RuntimeState`. Worker assignment
stays a bridge/refinement concern; the kernel remains actor/task
semantic, per RFC 043's design decision.

### Axiom budget: unchanged

`single_bridge_implies_multi_bridge` uses only `propext`;
`reachable_multi_bridge` adds `Classical.choice` and `Quot.sound`
(via `reachable_wf`). No project axioms. Verified by
`scripts/axiom_audit.py`.

---

## v0.11.1 — Selective Receive (RFC 041)

Adds `receiveByOccurrence (t : TaskId) (occ : MessageId)` and
`receiveFrom (t : TaskId) (src : ActorId)` as ops 15–16. Both use
**Option A (Mesa-style) blocking**: when no matching envelope is present
the task parks in the ordinary `mailboxWaiters` list. Any future
delivery wakes it; the task re-runs the selective receive. Blocking is
mailbox-level, not selector-level. Spurious wakeups are possible and
explicitly documented.

### Mailbox foundation: `listDequeueFirst`

New structural-recursion primitive in `Henret/Actor/Mailbox.lean`.
Removes the first list element satisfying a decidable predicate while
preserving the relative order of every other element. Properties:
`..._matches`, `..._mem`, `..._sublist`, `..._none` — all proved by
structural induction, avoiding index arithmetic entirely.

### Preservation

`preserves_wf_receiveByOccurrence` and `preserves_wf_receiveFrom` —
all 28 `WellFormed` fields. The occurrence-uniqueness bullets
(`occ_fresh`, `occ_nodup`, `occ_disjoint`) use `dequeueFirst_sublist`'s
`Sublist` relation instead of `dequeue_spec`'s head-removal `hcons`.

### Behavioral theorems (section `SelectiveReceive`)

- `receiveByOccurrence_removes_matching` — returned envelope has `occurrence = occ`
- `receiveFrom_source_matches` — returned envelope has `source = some src`
- `receiveByOccurrence_parks_on_miss` / `receiveFrom_parks_on_miss` — parks on no-match
- `receiveByOccurrence_preserves_nonmatching_order` / `receiveFrom_preserves_nonmatching_order` — `Sublist` order preservation

### Bridge and wiring

`toQOps` emits `[]` for both ops (no readyQ effect); `bridge_step_single_worker`
now covers all **16 `RuntimeOp`s**. `step_preserves_parent`,
`step_taskParent_stable`, `Timers`, `Ownership` all updated.

### Axiom budget: unchanged

No new axioms. All new proofs depend only on `propext`, `Quot.sound`,
and `Classical.choice`. Verified by `scripts/axiom_audit.py`.

---



Adds `receiveUntil (t : TaskId) (deadline : Nat)` as the 14th `RuntimeOp`,
completing the actor-system's timed-receive semantics. A task can park on an
empty mailbox with a hard deadline; `tick` wakes it when the timer expires.

### New `TaskState`: `.waitingTimed`

A sixth runnable variant. Tasks in `.waitingTimed` are registered in the
actor-local `timedMailboxWaiters` list **and** in the timer wheel with a
`waitDeadline` entry. Distinguished from `.waiting` (no deadline) and
`.sleeping` (no mailbox).

### `WellFormed` extended to 28 fields (+7)

Six new timed invariants (fields 22–27) describe the relationship between
`.waitingTimed` task state, `timedMailboxWaiters`, `timers`, and `waitDeadline`.
A seventh field, **`timed_waiters_exclusive`** (field 28), closes the
cross-actor uniqueness gap: a task appears in at most one `timedMailboxWaiters`
list. This exclusivity was required for `timed_waiters_valid` preservation
across `send`/`inject` timed-waiter wakeups.

### New and updated proofs (all zero `sorry`, all 28 fields)

- **`preserves_wf_receiveUntil`** (`Preservation/Messaging.lean`) — 28-field
  preservation proof across three sub-cases: immediate dequeue, past-deadline
  no-op, and park-with-deadline.
- **`preserves_wf_send`**, **`preserves_wf_inject`** — updated for the timed-waiter
  fallback path (when `mailboxWaiters b = []` but `timedMailboxWaiters b` is non-empty).
- **All six other operations** (Lifecycle, Time, Supervision) — 27→28 fields;
  `timed_waiters_exclusive` passes through cleanly for ops that don't modify
  `timedMailboxWaiters`.
- **`step_preserves_parent`** (`Parenthood.lean`) — `receiveUntil` added to the
  `taskParent`-stable match arm.

### Bridge layer updated

- **`toQOps`** (`Bridge/Grammar.lean`): `send`/`inject` now emit `Push 0 w` for
  the timed-waiter fallback; `tick` emits `Push 0 u` for both `.sleeping` and
  `.waitingTimed` woken tasks.
- New grammar lemmas: `toQOps_send_valid_timed_waiter`,
  `toQOps_inject_valid_timed_waiter`.
- `toQOps_tick_valid` updated to include both woken classes.
- **`bridge_step_single_worker`** now covers all **14 `RuntimeOp`s** including
  `receiveUntil` (emits `[]`; readyQ unchanged in all three branches).

### Axiom budget: unchanged

All new proofs depend only on `propext`, `Quot.sound`, and `Classical.choice`
(the last used by `by_cases` / `obtain`; present since RFC 013). Zero project
axioms added. Verified by `scripts/axiom_audit.py`.

---



Adds proof infrastructure in `StepFields.lean` that reduces the most repetitive
WellFormed preservation bullets to one-liners.

### New file: `Henret/Proofs/StepFields.lean` (147 lines, zero `sorry`)

Five helper theorems:

- **`wf_occ_fresh_pass`** — `occ_fresh` holds in `s'` when both `mailboxes` and
  `nextMsgId` are unchanged relative to `s`.
- **`wf_occ_nodup_pass`** — `occ_nodup` holds in `s'` when `mailboxes` is unchanged.
- **`wf_occ_disjoint_pass`** — `occ_disjoint` holds in `s'` when `mailboxes` is
  unchanged.
- **`wf_parent_lt_pass`** — `parent_lt` holds in `s'` when `taskParent` is unchanged.
- **`wf_parent_spawned_pass`** — `parent_spawned` holds in `s'` when `taskParent`
  is unchanged and spawned tasks stay spawned.

`OccFields` structure and `wf_occ_pass` bundle all three occurrence bullets for
cases where callers need the full package.

### Preservation files updated

- **`Preservation/Lifecycle.lean`**: 901 → 887 lines. `schedule`, `yield`,
  `complete`, `cancel` occ/parent bullets refactored. `spawnChild` occ_*
  bullets refactored. `spawn` `parent_lt` refactored.
- **`Preservation/Messaging.lean`**: 651 → 645 lines. `send` and `inject`
  `parent_spawned` bullets refactored using `step_preserves_spawned`.
- **`Preservation/Time.lean`**: already refactored during RFC 038/039 development.

### Caveat documented

`step_preserves_spawned hst _` only applies when the goal's LHS is in
`((step s op).1).taskState` form. When simp has reduced the step result to a
struct literal in the proof context (currently the `receive` parking branch),
the manual case split remains. This is documented in `docs/proof-engineering.md`.

### New documentation

`docs/proof-engineering.md` — full before/after diff examples, usage rules,
when-to-use guidance, and a template for new operations.

### Invariants maintained
- Zero `sorry`, zero project-specific axioms.
- `lake build Henret` passes cleanly (40 RFCs in `done/`).
- Doc-symbol check: 170 names verified.

---

## v0.10.0 — Supervision Semantics: Cascade Cancel (RFC 039)

Adds the first supervision operation: `cancelTree root`, which cancels a task
and every task in its subtree (all tasks whose `taskParent` chain reaches `root`).

### New `RuntimeOp`: `cancelTree (root : TaskId)` (13th constructor)

Always returns `.ok`. Cancels root and all descendants regardless of
`root`'s spawn status (no-op if the subtree is empty or already terminal).

### New infrastructure (in `Henret/Scheduler/Model.lean`)

- **`isInSubtreeOf s root t : Bool`** — computable parent-chain check.
  Well-founded by strict decrease (`p < t` enforced at each step); returns
  `false` conservatively for non-decreasing chains.
- **`descendantsOf s root : List TaskId`** — the cancellation set: all tasks
  in `[0, nextId)` that are spawned and whose parent chain reaches `root`.
- **`applyCancelTree s toCancel : RuntimeState`** — direct conditional
  state transformer: `if t ∈ toCancel then (cancel t) else (leave t)`.
  All five affected fields (`taskState`, `readyQ`, `running`, `timers`,
  `mailboxWaiters`) are defined directly from the original state.

### New file: `Henret/Proofs/Supervision.lean` (290 lines, zero `sorry`)

Twelve theorems including `preserves_wf_cancelTree` (all 21 `WellFormed`
fields) and the correctness lemmas:

- `cancelTree_cancels_task` — non-terminal subtree tasks → `.cancelled`
- `cancelTree_preserves_task_state` — outside-subtree tasks unchanged
- `cancelTree_cancels_root` — root itself cancelled (if non-terminal)
- `cancelTree_removes_from_readyQ / timers / waiters` — cleanup verified

### Bridge extended

`toQOps (.cancelTree root)` emits `(descendantsOf s root).map (.Filter 0 ·)`,
completing the bridge coverage for all 13 RuntimeOps. `bridge_cancelTree` is
proved using two helper lemmas: `applyQOps_filters0_at0` (worker-0 value) and
`applyQOps_filters0_other` (non-zero workers unchanged).

### Proof engineering notes

- Import cycle avoided by placing `preserves_wf_cancelTree` in `Supervision.lean`
  (imports `Invariants` + `Ownership` only; `InvariantsPreservation` imports
  `Supervision`, not vice versa through `Parenthood`).
- `decide_eq_decide.mpr` proved critical for `Bool` equality from `Prop ↔ Prop`
  without triggering `▸` motive errors.
- Explicit `rw [← Bool.decide_and]` + `decide_eq_decide.mpr` replaced all
  `simp`-loop-prone predicate equality proofs.

### Invariants maintained
- Zero `sorry`, zero project-specific axioms.
- All 95 proof-trust-test-matrix claims pass.
- Doc-symbol check: 170 names verified.
- Demo scenario 10 (cancelTree regression) added to `Main.lean`.

---



Strengthens `WellFormed` with two new exactness fields and generalizes
the `spawnChild` theorem family to properly separate parent actor from
child actor.

### New `WellFormed` fields (21 total, up from 19)

- **`owner_spawned`** (field 20) — every task with a `taskOwner` has a
  `taskState`; i.e., owned tasks are always spawned.
- **`parent_child_spawned`** (field 21) — every task with a `taskParent`
  has a `taskState`; i.e., tasks with parents are always spawned.

Both fields hold trivially in `init` (no owners or parents) and are
preserved by all 12 scheduler operations.

### Generalized `spawnChild` theorem family (`Henret/Proofs/Parenthood.lean`)

The `spawnChild` theorems previously conflated the parent task's actor
(`parentOwner`) with the child's actor (`childActor`), accepting only
the same-actor case. All four theorems now use separate `parentOwner` and
`childActor` parameters, accurately reflecting that a child may be owned
by any actor:

- `spawnChild_sets_parent` — child's `taskParent` = calling task id.
- `spawnChild_sets_owner` — child's `taskOwner` = `childActor` (not the
  parent's owner). *(RFC 038 key fix)*
- `spawnChild_queues_child` — child appended to `readyQ`.
- `spawnChild_child_spawned` — child's `taskState` = `some .new`. *(new)*

### New reachability corollaries

- `reachable_owner_spawned` — projects `WellFormed.owner_spawned` through
  `reachable_wf`.
- `reachable_parent_child_spawned` — projects `WellFormed.parent_child_spawned`
  through `reachable_wf`.

### Preservation updates

All three preservation files updated for the 2 new fields:
`Preservation/Lifecycle.lean`, `Preservation/Messaging.lean`,
`Preservation/Time.lean`. Each adds `import Henret.Proofs.Ownership`
for access to `step_preserves_spawned`.

### Invariants maintained
- Zero `sorry`, zero project-specific axioms.
- New fields depend only on Lean kernel axioms (`propext`, `Quot.sound`,
  `Classical.choice`).
- All 9 previous gate checks remain green.
- Doc-symbol check: 158 names verified (down 2 from 160 due to bare
  field names `owner_spawned`/`parent_child_spawned` correctly moved to
  IGNORE; their `WellFormed.X` fully-qualified forms remain checked).

---



Completes the single-worker queue-projection bridge and resolves all
v0.8.0 public claim issues identified in the architect review.

### RFC 037 — Public Claim Repair

- `docs/guided-tour.md` — replaced stale "Six scenarios" count with
  count-free prose matching the actual demo sequence.
- `scripts/check.sh` gate 6 — extended with v0.8.0 stale-phrase checks
  (hard-coded scenario count, parenthood field counts, provenance note,
  task-state claim, RFC 035 old title). All gates now green.
- All other RFC 037 edits (send provenance note, README messaging section,
  guided tour field counts, RFC 035 status) were already applied in the
  v0.8.0 working copy.

### RFC 036 — Bridge Claim Repair and Single-Worker Bridge Completion

#### QOp grammar (`Henret/Bridge/Grammar.lean`)
- `QOp.Filter` — new constructor for cancellation queue effect.
- `toQOps` rewritten to be fully guard-compatible: `toQOps s op = []`
  whenever `(step s op).2 = .invalid`, for all 12 operations.
  - `tick` now uses the argument `t` (not `s.now`).
  - `cancel` emits `[Filter 0 t]` for non-terminal tasks.
  - `send`/`inject` fully check running state, task state, owner, and
    mailbox existence before emitting queue effects.
  - `Wake` is no longer emitted (Design A per RFC 036); all wake effects
    are expressed as `Push 0 t`.
- New direct-effect lemmas: `toQOps_cancel_valid`,
  `toQOps_cancel_invalid_terminal`, `toQOps_cancel_invalid_unspawned`,
  `toQOps_send_valid_waiter`, `toQOps_send_valid_no_waiter`,
  `toQOps_inject_valid_waiter`, `toQOps_inject_valid_no_waiter`,
  `toQOps_inject_invalid`, `toQOps_tick_valid`, `toQOps_tick_invalid`,
  `toQOps_schedule_empty`, `toQOps_spawnChild_valid`.

#### BridgeState and queue model (`Henret/Bridge/State.lean`)
- `WorkerQueues.init` — empty initial worker-queue map.
- `bridgeState_filter0` — BridgeState is preserved by `Filter 0 t`.
- `applyQOp .Filter` — removes all occurrences of task `t` from a worker's queue.
- `toQOpsTrace` — state-threading trace translation for the trace theorem.

#### Bridge preservation (`Henret/Bridge/Preservation.lean`)
- New per-op theorems: `bridge_spawnChild`, `bridge_schedule`,
  `bridge_cancel`, `bridge_send`, `bridge_inject`, `bridge_tick`.
- `applyQOps_append` — `applyQOps wqs (as ++ bs) = applyQOps (applyQOps wqs as) bs`.
- **`bridge_step_single_worker`** — unified single-step bridge for all 12 `RuntimeOp`s.
- **`bridge_run_general`** — trace bridge from any starting `BridgeState`.
- **`bridge_run_tracks_single_worker`** — headline trace theorem:
  `BridgeState (run init ops) (applyQOps WorkerQueues.init (toQOpsTrace init ops))`.
- `reachable_bridge` now proved via `bridge_run_tracks_single_worker`.

#### Documentation
- `docs/bridge-architecture.md` — new document describing bridge scope,
  QOp grammar, translation table, headline theorems, and what is not claimed.
- `docs/proof-index.md` — bridge section updated for RFC 036 completion.
- `docs/proof-trust-test-matrix.md` — claims 80–84 added (all 12 bridge ops,
  bridge_step_single_worker, bridge_run_tracks_single_worker, scope notes).
- `scripts/check.sh` gate 5 — axiom audit extended with RFC 036 bridge theorems.
- `scripts/doc_symbol_check.py` — IGNORE list updated; 153 names now checked
  (up from 135); `open Henret.Bridge` added to preamble.

### Invariants maintained
- Zero `sorry`, zero project-specific axioms.
- All new bridge theorems depend only on `propext`, `Quot.sound`, and
  `Classical.choice` — the standard Lean 4 kernel axioms.
- `WellFormed` and all 19-field reachability proofs unchanged.

---

## v0.8.0 — Lean-Runtime Bridge (RFC 035)

Formally connects the henret model to the lean-runtime work-stealing scheduler.
Introduces the `Henret.Bridge` module: a `QOp` grammar translation, a
`BridgeState` relation, and per-operation preservation theorems covering spawn,
yield, wake, complete, receive, and sleep.

### New (`Henret/Bridge/Grammar.lean`)
- `QOp` — mirror of lean-runtime's queue-operation grammar (Push, Pop, Steal,
  Wake, Inject) as a henret-internal inductive type.
- `toQOps : RuntimeState → RuntimeOp → List QOp` — validity-aware translation;
  returns `[]` when `step` would return `.invalid` (guards are checked).
- Lemmas: `toQOps_spawn_valid/invalid`, `toQOps_yield_valid/invalid`,
  `toQOps_wake_valid/invalid`, `toQOps_complete/receive/sleep_nil`,
  `toQOps_schedule_nonempty`, `toQOps_send/inject_*_waiter`.
- `wake` emits `Push 0 t` (not `Wake t`), correctly reflecting that a waking
  sleeping task is appended to worker 0's ready queue.

### New (`Henret/Bridge/State.lean`)
- `WorkerQueues := WorkerIdx → List TaskId` — per-worker queue model.
- `BridgeState : RuntimeState → WorkerQueues → Prop` — `queue_eq` (worker 0
  equals henret's `readyQ`) + `other_empty` (single-worker model).
- `applyQOp`, `applyQOps` — queue-model application of QOp sequences.
- Structural constructors: `bridgeState_init`, `bridgeState_push0`,
  `bridgeState_pop0`, `bridgeState_readyQ_unchanged`.

### New (`Henret/Bridge/Preservation.lean`)
- `bridge_stable` — BridgeState is preserved by readyQ-stable steps.
- `reachable_bridge` — every reachable state has a `BridgeState` witness.
- `bridge_spawn`, `bridge_yield`, `bridge_wake` — Push-effect operations.
- `bridge_complete`, `bridge_receive`, `bridge_sleep` — readyQ-stable operations.

### Documented gaps (RFC 036 scope)
- `cancel` — filters `readyQ`; needs a `Filter` QOp.
- `send`/`inject` with waiter — append to readyQ on wake; needs `Push`.
- `tick` — wakes expired timers; needs `Push` per expiry.
- `schedule` — `Pop 0` case; building block `bridgeState_pop0` exists.

### Ecosystem
- `lean-runtime-workspace` confirmed buildable (all 37 targets) and all
  `runtimeTests` pass in the current sandbox environment.
- RFC 035 document moved from `rfcs/proposed/` to `rfcs/done/`.

---

## v0.7.0 — Message envelope and occurrence identity (RFC 033)

Delivers globally unique delivery identity: every envelope carried by `send`
or `inject` is stamped with a `MessageId` allocated from `nextMsgId`, and the
kernel proves that no two envelopes in any reachable state share the same id.

### Model changes

**`Henret/Actor/Mailbox.lean`**
- `MessageId := Nat` — occurrence-id type alias.
- `Envelope` (new structure) — `occurrence : MessageId`, `source : Option ActorId`,
  `body : Message`. The unit of in-transit storage; replaces bare `Message`.
- `Mailbox.messages : List Envelope` (was `List Message`).
- `Mailbox.enqueue : Mailbox → Envelope → Mailbox` (was `→ Message →`).
- `Mailbox.dequeue : Mailbox → Option (Envelope × Mailbox)`.

**`Henret/Scheduler/Model.lean`**
- `RuntimeState.nextMsgId : MessageId` (new field, init = 0).
- `send t b m` — stamps `env := ⟨s.nextMsgId, s.taskOwner t, m⟩`, bumps `nextMsgId`.
- `inject a m` — stamps `env := ⟨s.nextMsgId, none, m⟩`, bumps `nextMsgId`.
- `receive t` — dequeues an `Envelope`; `StepResult.received` now carries `Envelope`.

**`Henret/Core/Result.lean`**
- `StepResult.received` carries `Envelope` (was `Message`).

### New (`Henret/Proofs/Invariants.lean`)
- `WellFormed.occ_fresh` (field 17) — every envelope's occurrence id is
  strictly less than `nextMsgId`.
- `WellFormed.occ_nodup` (field 18) — within each mailbox all occurrence ids
  are distinct.
- `WellFormed.occ_disjoint` (field 19) — across different mailboxes all
  occurrence ids are distinct.
- `wf_init` extended to 19 fields.

### New (`Henret/Proofs/Occurrence.lean`)
- `reachable_occurrence_unique` — **headline**: in every reachable state, equal
  occurrence ids in any two (possibly equal) mailboxes imply the same envelope
  in the same mailbox. Globally unique delivery identity.
- `send_stamps_source` — the envelope delivered by `send t b m` carries
  `source = s.taskOwner t`.
- `inject_stamps_none` — the envelope delivered by `inject a m` carries
  `source = none`.

### Updated

**All three preservation files** — extended to 19 fields (3 new occ bullets per
refine block):
- `Henret/Proofs/Preservation/Lifecycle.lean` — 7 refine blocks.
- `Henret/Proofs/Preservation/Time.lean` — 3 refine blocks.
- `Henret/Proofs/Preservation/Messaging.lean` — 6 refine blocks;
  send/inject occ proofs use `send_appends` / `inject_appends` for
  the cons-waiter case.

**`Henret/Proofs/Messaging.lean`** — `send_appends`, `inject_appends`,
`receive_only_own`, `receive_consumes_one`, `receive_length` updated for `Envelope`.

**`Henret/Refinement/Contract.lean`** and **`ReferenceBackend.lean`** — updated:
`enqueue`/`dequeue`/`toList` now operate on `Envelope` (was `Message`).

**`Henret/Proofs.lean`** — exports `Henret.Proofs.Occurrence`.

### Demo and examples
- Scenarios 2 and 7 updated with exact `Envelope` constructor values (occurrence
  ids are deterministic and kernel-assigned).
- `examples/02_actor_mailbox.lean` — `#eval` comment updated; stale
  `spawn_sets_owner` reference replaced.

---

## v0.6.0 — Actor-scoped spawn and supervision groundwork (RFC 032)

Implements the actor-scoped spawn operation and its full kernel-proven
invariant structure. Extends `WellFormed` from 14 to 16 fields, adds the
`spawnChild` runtime operation, and delivers the acyclicity guarantee for
supervision trees.

### New (`Henret/Scheduler/Model.lean`)
- `RuntimeOp.spawnChild (t : TaskId) (a : ActorId)` — the running task `t`
  spawns a new child task owned by actor `a`.
- `RuntimeState.taskParent : TaskId → Option TaskId` — records each task's
  parent (set once at spawn, `none` for roots).

### New (`Henret/Proofs/Invariants.lean`)
- `WellFormed.parent_lt` (field 15) — every recorded parent has a strictly
  smaller `TaskId` than its child.
- `WellFormed.parent_spawned` (field 16) — every recorded parent is in some
  non-`none` state.
- `wf_init` extended to 16 fields.

### New (`Henret/Proofs/Parenthood.lean`)
- `spawnChild_sets_parent`, `spawnChild_sets_owner`, `spawnChild_queues_child`
  — direct effects of a valid spawn.
- `spawnChild_not_running_invalid`, `spawnChild_unowned_invalid` — guard
  theorems.
- `step_preserves_parent` — `taskParent` is immutable after creation; only
  `spawnChild` writes it and only to the fresh slot.
- `reachable_parent_lt` — headline: in every reachable state every parent has
  a smaller id than its child.
- `parent_chain_terminates` — acyclicity deliverable: every ancestor chain
  reaches a root in at most `t + 1` steps.

### New (`Henret/Proofs/StepProjections.lean`)
- `spawnChild_taskState_other`, `spawnChild_taskOwner_other`,
  `spawnChild_taskParent_other`, `step_taskParent_stable`.

### Extended (`Henret/Proofs/Preservation/`)
- `preserves_wf_spawnChild` (new) — all 16 WF fields for the new operation.
- All 11 existing preservation theorems extended to the 16-field `WellFormed`.

### Extended (`Henret/Proofs/InvariantsPreservation.lean`)
- `step_preserves_wf` dispatch extended with `spawnChild` case.

### Extended (`Henret/Proofs/Ownership.lean`)
- `step_preserves_spawned`, `step_preserves_terminal`, `step_invalid_unchanged`
  extended with `spawnChild` cases.

### Extended (`Henret/Proofs/Timers.lean`)
- `step_clock_monotone`, `run_preserves_sorted` extended.

### New (`Henret/Examples/Basic.lean`)
- Demo scenario 8: `spawnChild` round-trip (3 `native_decide` checks).

### Updated docs
- `docs/proof-trust-test-matrix.md` rows 57–63.
- `docs/proof-index.md` RFC 032 section.
- `docs/guided-tour.md` section 9b.
- `scripts/check.sh` and `scripts/axiom_audit.py` updated.


## v0.5.1 — release-gate repair and RFC 031 completion (RFC 035)

Resolves all six release-blockers from the v0.5.0 architect review.
Zero public-surface semantic change to the model; proof additions only.

### Added (theorems)
- `receive_blocked_parks` — result-driven form of the parking theorem:
  from an observed `.blocked` result alone, reconstructs all four guards
  (running, `.running` state, owned, empty own mailbox) and the complete
  post-state (task `.waiting`, running cleared, task in `mailboxWaiters`,
  other actors' lists and mailboxes unchanged). Mirrors `receive_only_own`.
- `reachable_waiters_exact` — exact waiter characterization: in every
  reachable state, `t ∈ mailboxWaiters a ↔ taskState t = .waiting ∧
  taskOwner t = a`. Mirrors `reachable_queue_exact` (RFC 031 acceptance
  criterion, previously deferred).
- `reachable_waiter_actor_unique` — a task is in at most one waiter list;
  list membership determines the actor via ownership.
- `reachable_waiting_is_queued` — every reachable `.waiting` task is
  in its own actor's `mailboxWaiters` list (thin corollary of the WF field).

### Added (demo)
- Demo scenario 7 replaced with the full RFC 031 round trip: park →
  inject → wake head waiter → re-schedule → re-receive → consume
  (12 runtime checks). Includes Mesa-semantics check that the message
  remains in the mailbox until the re-issued receive consumes it.

### Fixed (release gates — RB-01)
- `scripts/check.sh`: removed `step_blocked_unchanged`; added
  `receive_empty_parks`, `receive_blocked_parks`, `reachable_waiters_exact`,
  `reachable_waiter_actor_unique`.
- `scripts/axiom_audit.py`: same allowlist update.

### Fixed (examples — RB-02)
- `examples/04_send_receive.lean`: replaced `receive_empty_blocked` with
  `receive_empty_parks` / `receive_blocked_parks`; added `#eval` demos
  for the parking and wake-one round trip; updated StepProjections
  reference to RFC 031 scope.
- `examples/README.md`: updated example 04 theorem list.

### Fixed (docs — RB-03, RB-04, Task 6)
- `README.md`: replaced stale no-op blocked claim with parking claim;
  updated StepProjections description to RFC 031 scope.
- `docs/proof-trust-test-matrix.md`: rows 9, 10, 42, 47, 48 rewritten.
- `docs/proof-index.md`: stale `receive_empty_blocked` /
  `step_blocked_unchanged` replaced; StepProjections description scoped.
- `docs/test-index.md`: scenario 7 row updated to park/deliver/consume.
- `docs/guided-tour.md`: new section 8 explaining `mailboxWaiters` as a
  notification queue, Mesa semantics, and the exactness theorem.

### Axiom audit
All new theorems depend only on `[propext, Quot.sound]`. No `sorryAx`.

## v0.5.0 — blocked waiting state + preservation-proof modularity (RFCs 031, 034)

Turns the transitional "blocked receive" result from v0.4.0 into real
execution-management state: a blocked receive parks the running task
(`TaskState.waiting`), and each subsequent `send`/`inject` to that actor's
mailbox wakes exactly one head waiter.

### Added
- `TaskState.waiting` — a parked task; not in the ready queue, not running.
  Distinct from `.sleeping` (timer-blocked).
- `RuntimeState.mailboxWaiters : ActorId → List TaskId` — per-actor FIFO
  wait queue, invariant-backed.
- Four new `WellFormed` fields (fields 11–14): `waiters_waiting`,
  `waiters_owned`, `waiting_queued`, `waiters_nodup`.
- `wf_init` proves all 14 WF fields for the initial state.
- `receive` (empty-mailbox, valid branch): parks the running task
  (`TaskState.waiting`), clears `running`, appends to `mailboxWaiters a`.
- `send`/`inject` (valid branch, wake-one): if the target actor has a
  non-empty wait queue, dequeues the head waiter to `.ready` and
  appends it to `readyQ`; nil branch unchanged.
- `cancel` removes the task from its owner actor's `mailboxWaiters`.
- `showState` in `Examples/Basic.lean` handles `| waiting =>`.

### Changed (proof layer)
- All three preservation files (`Lifecycle`, `Messaging`, `Time`) prove all
  14 WF fields per operation (up from 10).
- `Messaging.lean` preservation: full case-trees for nil/cons wake-one
  branches of send/inject; nil/dequeue/parking branches of receive.
- `Time.lean` preservation: four new waiter fields — time ops do not touch
  `mailboxWaiters`, so all four close by pass-through.
- `preserves_wf_cancel` extended with taskOwner-case-split waiter proofs.
- `preserves_wf_inject` added (was inadvertently dropped in v0.5.0 split).

### Axiom audit
All new theorems depend only on `[propext, Quot.sound]`. No `sorryAx`.

### Changed (RFC 034 — preservation-proof modularity)
- `Henret/Proofs/InvariantsPreservation.lean` split from 780 to 102
  lines (assembly only). Per-operation WellFormed preservation proofs
  moved to:
  - `Henret/Proofs/Preservation/Lifecycle.lean` (spawn/schedule/yield/
    complete/cancel)
  - `Henret/Proofs/Preservation/Messaging.lean` (send/receive/inject)
  - `Henret/Proofs/Preservation/Time.lean` (sleep/tick/wake)
- `step_preserves_wf` body is a dispatch table.
- Each per-op lemma is self-contained; adding an operation or invariant
  field now touches one focused file.


## v0.4.1 — public claim cleanup (RFC 030)

Resolves all five release-blockers of the v0.4.0 review; the reviewer's
prerequisite for public v0.4.x tagging.

### Fixed
- README "model in one minute" operation list includes `inject` (RB-01).
- Proof index: flagship case analysis described over the eleven-operation
  grammar (RB-02); `WellFormed` described by its current ten-field
  surface (RB-03).
- `Henret.Proofs` barrel docstring made count-free (RB-04).
- README proof summary gains the v0.4.0 headlines: schedulable
  completeness and blocked receive (RB-05).
- Example 04 separates the non-running guard demo from the ownership
  guard theorem (SF-02).

### Added
- Demo scenario 7: blocked vs invalid receive, split from scenario 6;
  test index updated (SF-03).
- Gate 6 current-surface phrases for stale operation/field counts (SF-01).
- Transitional framing for `blocked` in README and matrix: a no-op
  result, not a waiting-state transition (SF-04).


## v0.4.0 — schedulable completeness + blocked receive (RFCs 028–029)

The two semantic priorities named by the v0.3.0 review.

### Added
- `WellFormed.runnable_queued` (tenth field): every runnable task is in
  the ready queue. Headlines `reachable_runnable_is_queued` and
  `reachable_queue_exact` (queue membership ⟺ runnable) — the runtime
  provably never loses a runnable task (RFC 028).
- `StepResult.blocked`; empty own-mailbox receive now blocks instead of
  being invalid; `receive_empty_blocked`; mirror theorem
  `step_blocked_unchanged` (RFC 029).
- Demo checks distinguishing blocked (legal wait) from invalid
  (protocol violation).
- Sleep past-deadline policy made explicit in the grammar docs: legal,
  wakes at next valid tick (SF-03 resolved by documented decision).

### Changed
- `receive_empty_invalid` renamed/restated as `receive_empty_blocked`.


## v0.3.1 — public-claim repair (RFCs 026–027)

Resolves all five release-blockers of the v0.3.0 review; first release the
external reviewer's criteria would tag as public-quality.

### Fixed
- Stale pre-RFC-024 theorem references in the proof index and matrix
  replaced with the `StepProjections` lemma family (RB-01).
- Guided tour shows the eleven-operation grammar and `receive_only_own`
  (RB-02).
- `Mailbox.lean` message-ownership overclaim reworded to per-operation
  value semantics (RB-03); matrix row 7 scoped.
- `Henret.Model` documented as a light import, not definition-only (RB-04;
  decision recorded in RFC 027).
- `lakefile.lean` import comment matches RFC 025 (RB-05).
- `send` docstring: existence provenance, not message provenance (SF-04).

### Added
- Gate 7: `scripts/doc_symbol_check.py` — every backticked theorem name in
  the proof docs must `#check` (99 names verified); gate 6 phrase list
  extended (SF-05).


## v0.3.0 — actor-scoped operations (RFCs 024–025)

Breaking: the operation grammar changes. `send`/`receive` are now
task-scoped; `inject` is the new environment delivery path.

### Added
- `send t b m` (running task → actor), `receive t` (task receives from
  its **own** actor's mailbox, derived from `taskOwner`), `inject a m`
  (environment → actor). Eleven operations total (RFC 024).
- **`receive_only_own`** — actor-local receive discipline, the RFC 024
  headline, kernel-checked and audit-allowlisted.
- Guard theorems: `send_not_running_invalid`, `send_unowned_invalid`,
  `receive_unowned_invalid`.
- `Henret.Proofs.StepProjections` — messaging touches only `mailboxes`,
  21 `@[simp]` projection lemmas proved once.
- Mailbox monotonicity: `send/receive/inject_mailbox_isSome`.
- Import barrels `Henret.Model`, `Henret.Proofs`, `Henret.Refinement`;
  root `Henret` no longer imports examples (RFC 025).

### Changed
- All invariant/preservation proofs re-proved over the new grammar.
- Examples 02 (environment `inject`) and 04 (actor-scoped messaging with
  guard-failure demos) rewritten; demo mailbox scenario schedules a task
  and messages through it.


## v0.2.1 — review-hardening release (RFCs 019–023)

Resolves all five must-fixes of the v0.2.0 follow-up review.

### Added
- `WellFormed` strengthened to nine fields: `timers_sorted`,
  `spawned_has_owner`, `owned_has_mailbox`; preservation re-proved for all
  ten operations; new headlines `reachable_spawned_has_owner`,
  `reachable_owner_has_mailbox`, `reachable_timers_sorted` (RFC 019).
- `scripts/axiom_audit.py` — exact per-theorem axiom allowlist; rejects any
  unexpected project axiom; negative cases validated (RFC 020).
- `scripts/check.sh` gate 6 — documentation-consistency grep (RFC 021).
- Demo scenario 6 rebuilt: arbitrary-state stale-timer entry, asserting the
  tick filter consumes it and wakes nothing (RFC 021).
- `wakeOne_none` / `wakeMany_none` — waking never spawns.

### Changed
- `drivePopB` renamed `driveStackB` with an explicit orientation note
  relative to `DequeModel.toList`; `execDemo` framing removed (RFC 023).
- Message non-duplication claims scoped to per-operation value semantics;
  occurrence identity recorded as future work (RFC 022).
- Scenario counts and changelog history corrected (RFC 021).


## v0.2.0 — invariant discipline (review-resolution release)

Resolves all seven must-fix findings of the v0.1.0 architecture review
(`docs/reviews/v0.1.0-review-resolution.md`). Model changes: `RuntimeState`
gains `taskOwner` (RFC 014) and `now` (RFC 015); `tick` is guarded monotone
and wakes only genuinely sleeping tasks.

### Added
- `WellFormed` reachability invariant; `step/run_preserves_wf`,
  `reachable_wf`; ownership-location disjointness corollaries (RFC 013).
- `taskOwner` field; `spawn_sets_owner`, `step/run_preserves_owner`,
  `step_preserves_spawned` (RFC 014).
- `now` field; monotonic tick guard; `tick_advances_clock`,
  `tick_backwards_invalid`, `step_clock_monotone` (RFC 015).
- `step_invalid_unchanged` (RFC 016).
- `scripts/check.sh` five-gate release script + GitHub Actions CI (RFC 017).
- Documentation consistency sweep: accurate lifecycle transition tables,
  standardized native-boundary wording (RFC 018).
- Demo scenario 6: seven regression checks for the v0.2.0 model.
- Examples 02/05 extended (`taskOwner`, monotone clock).

### Changed
- `tick now` filters its woken list to tasks whose state is `.sleeping`,
  keeping the ready queue clean in arbitrary states (review must-fix 4).
- Timer theorems take a `s.now ≤ now` validity hypothesis.


## v0.1.0 — 2026-06-04

First public release: the Lean-only actor/task model.

### Added
- `Henret` Lean-only core package (Lean 4.15.0 / Lake; no native deps).
- Actor/task model: `TaskId`/`ActorId`, `TaskState` lifecycle with terminal
  `completed`/`cancelled`, `Message`/`Mailbox`/`ActorState` (RFC 004).
- Scheduler semantics: `RuntimeOp` grammar, total executable
  `step`/`run`/`runTrace`, invalid ops are guaranteed no-ops (RFC 005).
- Message/wake semantics with ownership and exactness proofs (RFC 006).
- Logical-time timers: sorted queue, `sleep`/`tick`/`wake`, no-early-wake and
  expired-wake proofs, sortedness preservation (RFC 007).
- Drivers: op-level fueled `driveOps` (tested) and model-level `drain` with
  proven liveness `drain_completes`.
- Refinement: `MailboxBackend` contract and two proven reference backends (RFC 008).
- Proof/trust/test matrix and proof/assumption/test indexes (RFC 009).
- `henret-demo` executable with five self-checking scenarios.
- Docs: README, positioning, naming/scope, prior-art, guided tour,
  refinement-contract pattern.
- RFC lifecycle directories per RFC 000 (`proposed/`, `done/`, `archive/`).

### Trust status
- 0 `sorry`, 0 custom axioms, 0 `native_decide`; `#print axioms` reports only
  `propext`/`Quot.sound` for all exported theorems.

### Added (continued — examples and full RFC closure)
- `examples/` directory with 9 self-contained educational examples
  (`01_task_lifecycle` through `09_optional_ffi_boundary`), each teaching one
  concept, all verified with `lake env lean`.
- `examples/README.md` learning-order index.
- RFC 011 (Examples and Guided Tour) → `rfcs/done/`.
- RFC 012 (Release, Docsite, and Community) → `rfcs/done/`; all 11 of 12 RFCs
  now done; RFC 010 (optional FFI boundary) landed later within v0.1.0
  (see the dedicated section below).

### Added (RFC 010 — Optional Native Backend Boundary)
- `Henret/Native/DequeModel.lean` — `DequeModel` abstract contract (6 laws,
  `toList` observation, analogous to `MailboxBackend`); `listDeque` reference
  implementation (laws by `rfl`); `qRun_tracks` (whole-program refinement,
  PROVEN, `propext` only); `drivePopB_complete` (LIFO driver liveness, PROVEN).
- `Henret/Native/Assumptions.lean` — 6 typed axioms for `NativeDeque`; 
  `nativeDequeModel : DequeModel`; `nativeDequeModel_qRun_tracks` (PROVEN given
  the 6 axioms); axiom audit: `#print axioms` lists exactly 6 named axioms.
- `lakefile.lean` — `HenretNative` lib target (`lake build HenretNative`).
- `docs/native-backend-boundary.md` — the trust discipline, audit script,
  OUTSCOPE claims, conformance testing plan.
- `docs/assumption-index.md` — updated with 6 `NativeDeque` axioms.
- `docs/proof-trust-test-matrix.md` — rows 18–28 for native layer.
- `docs/proof-index.md` — native theorem inventory.
- `examples/09_optional_ffi_boundary.lean` — updated to use real modules.
- RFC 010 → `rfcs/done/`. All 12 RFCs now done.
