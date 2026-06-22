---
rfc: 97
title: Release Gate Profiles and Validation Split
status: Implemented
implemented_in: v0.34.4
supersedes: []
superseded_by: []
depends_on: [80, 95]
blocks: []
category: release-process
---

# RFC 097 — Release Gate Profiles and Validation Split

## Status

Implemented in v0.34.4. Approved by architect review of the CI release-gate
capacity issue (verdict: keep CI authoritative; split release-blocking evidence
from executable validation).

Architect checkpoint review: **conditionally accepted**. Documentation/manifest
items §4–§7 (gate registry naming, `--release` alias policy, `validation_reports`
immutability rule, precise `ci-core-v1` consumer verifier recipe) are folded in.
**Closure condition 1 met:** the v0.34.4 CI release-core run completed green and
published the sidecar (`henret-0.34.4.release-verification.json`, profile
`ci-core-v1`, `git_dirty: false`, real commit pinned, all 8 required gates pass,
advisory gates honestly `not_run_in_release_core`). The dirty-tree blocker was a
stray `elan-init` installer binary dropped in the checkout, and the 403 at the
publish step was a read-only `GITHUB_TOKEN`; both fixed (elan installs in `/tmp`;
workflows declare `permissions: contents: write`).

**Closure condition 2 automated:** the release-gate workflow now re-downloads the
published assets and runs `verify_release_manifest.py` against them (tarball
sha256, GATE-RUN binding, required-gate pass), so post-upload verification runs on
every tagged release. With both conditions satisfied, RFC 097 is fully closed. Post-upload verification
was confirmed empirically against the live published artifacts
(`verify_release_manifest.py` vs the downloaded tarball + sidecar + GATE-RUN:
OK, hashes match, 8 required gates pass) and is automated for future releases.
The dirty-tree exception was tightened (architect review §3) to excuse only
untracked artifacts — a tracked source edit stays dirty even if its path resembles
an excluded cache/tool path (verified by test).

## Summary

`scripts/check.sh --release` was one monolithic gate that natively compiled the
`henret-demo` and `henret-conformance` executables. That native compilation
(C codegen for ~80 modules + link) cannot complete on the only acceptable runner
(GitHub-hosted `ubuntu-latest`, 2 vCPU / 7 GB; larger runners ruled out for cost):
it OOM-killed, and with swap it ran ~1 h to the job timeout. Interpreting the
executables avoids the native build but the exhaustive conformance *run* is also
slow. The result: the RFC 095 sidecar — the evidence iotakt/jemmet need — never
got published, blocked by a CI-capacity problem, not a proof problem.

This RFC splits the release gate into two profiles by **gate criticality**:

- **release-core** (`check.sh --release-core`, alias `--release`): CI-authoritative,
  sidecar-publishing. The cheap, kernel-checked evidence — self-test, library/proof
  build (which kernel-checks everything), examples, doc-symbol, axiom audit,
  doc/metadata consistency, warning budget — plus canonical tarball and hashed
  manifest. Completes in minutes. **Blocks** sidecar publication.
- **release-validation** (`check.sh --release-validation`): advisory executable
  regression — the demo and exhaustive conformance, run interpreted, emitted as a
  separate `validation-report.json`. **Non-blocking**: a slow or failing
  validation never blocks the sidecar.

CI authority is preserved (RFC 080-D unchanged): the published manifest still
comes from CI on the exact release commit/tag. What changes is *what the sidecar
certifies* — and the manifest now says so honestly.

## Design

### D1 — Gate criticality

Gates carry a `criticality`: `required` (release-core, blocking) or `advisory`
(executable validation, non-blocking). Required: 0 self-test, 1 build, 3 examples,
5 doc-symbol, 6 axiom audit, 7 doc consistency, 8 RFC metadata, 9 warning budget.
Advisory: 2 demo, 4 exhaustive conformance.

### D2 — Manifest honesty

`release-verification.json` (still `manifest_schema 1`, additive) gains:
`release_profile` (e.g. `ci-core-v1`), `required_gates_passed`, per-gate
`criticality`, and `validation_reports` (optional references). Under the
`ci-core-v1` profile the advisory gates are **not silently dropped**: they appear
as `status: not_run_in_release_core` with a reason pointing to the validation
workflow. `verify_release_manifest.py` requires only `required` gates to pass. The manifest also carries `gate_registry: rfc097-ci-core-v1` so the
current 10-gate (0–9) registry is named explicitly and cannot be confused
with older RFC 080 stage lists (architect review §4); RFC 097 did not
renumber gates, only added `criticality`.

### D3 — Validation report

`check.sh --release-validation` runs the advisory gates and emits
`henret-X.Y.Z.validation-report.json` + `.validation-GATE-RUN.md`
(`scripts/validation_report.py`), hash-bound the same way as the manifest. Its
per-gate timings double as the architect's §4 diagnostic (which of demo /
conformance is slow). A separate `release-validation.yml` workflow runs it
non-blocking on tags and on manual dispatch.

### D4 — What the sidecar certifies (consumer-facing)

The RFC 095 sidecar certifies: the source archive, exact commit, toolchain/manifest
pins, the Lean kernel build (the proofs), the strict axiom audit, doc/generated-doc
checks, the warning budget, the gate-policy hashes, and packaging integrity — under
CI. Exhaustive executable conformance is reported separately as advisory validation
when available. iotakt/jemmet pin the sidecar manifest hash (RFC 096), and may also
record a validation-report hash if they require executable-regression evidence.

## What this RFC explicitly does not do

- It does **not** relax RFC 080-D (no maintainer-local authoritative manifest).
- It does **not** rely on cache-warmed long native builds as the release path.
- It does **not** drop demo/conformance — they run, just not as release blockers.

## Acceptance criteria

- `check.sh` has explicit `--release-core` and `--release-validation` behavior;
  `--release` aliases `--release-core`.
- Only release-core (CI) publishes `release-verification.json`.
- The manifest records `release_profile`, `required_gates_passed`, and per-gate
  `criticality`, with honest `not_run_in_release_core` advisory placeholders.
- A separate non-blocking workflow runs release-validation and emits a report.
- `integration-contract.md` states exactly what the sidecar certifies.
- The release checklist uses RFC 095 post-upload verification.

## Open questions

- **Smoke promotion (diagnostic-gated).** Once the validation workflow reports
  per-gate timings, a cheap demo and/or conformance *smoke* subset may be promoted
  back into release-core as a blocking gate. Deferred until the timing data exists;
  default is executables-in-validation.
- **`--fast` scope.** `--fast` currently runs the core gates (no executables); if
  the diagnostic shows the interpreted conformance is cheap, a smoke subset could
  return to `--fast` for local coverage.
- **`-O0` native experiment.** Whether compiling the executables with `-O0`
  (`moreLeancArgs`) makes a native validation tier cheap enough is an open
  experiment, not part of this RFC.
