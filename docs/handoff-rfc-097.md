# Checkpoint handoff — RFC 097 release-gate split (v0.34.4)

**For:** architect review
**Release:** `henret-v0.34.4.tar.gz` (dev artifact; published assets are no-`v`)
**Scope:** release-process / CI only — no model, proof, or theorem change. Axioms
unchanged; public theorem surface unchanged (101 names). `manifest_schema` stays 1.
Gate-0 self-test, `--fast`, and the docs gate green.

## What I implemented (your verdict: keep CI authoritative; split B + D)

- **`check.sh` two-tier modes.** `--release-core` (alias `--release`) runs the
  required, CI-authoritative gates (0 self-test, 1 build/proofs, 3 examples,
  5 doc-symbol, 6 axiom audit, 7 doc consistency, 8 RFC metadata, 9 warning
  budget) + canonical tarball + manifest, and publishes the sidecar.
  `--release-validation` runs the advisory executables (2 demo, 4 exhaustive
  conformance) interpreted and emits a separate report. The refactor keeps each
  `run_gate <id>` exactly once (gate-0 self-test invariant verified: still 10
  gates, 156/156 axioms).
- **Manifest honesty (RFC 097 D2).** `release_manifest.py` adds `release_profile`,
  `required_gates_passed`, per-gate `criticality`, and `validation_reports`. Under
  `ci-core-v1` the advisory gates appear as `not_run_in_release_core` with a reason
  — not silently dropped. `verify_release_manifest.py` now requires only `required`
  gates to pass (validated: passes a core manifest, still fails on a required-gate
  failure or tampered tarball).
- **Validation report + workflow.** New `scripts/validation_report.py` emits
  `henret-X.Y.Z.validation-report.json` + `.validation-GATE-RUN.md` (hash-bound).
  New `.github/workflows/release-validation.yml` runs `--release-validation`
  non-blocking on tags + manual dispatch, attaching the report; its per-gate
  timings are the §4 diagnostic.
- **`ci.yml`** now runs `--release-core` (swap step removed — no native build
  remains, so it was vestigial), keeps the tag-gated release-asset upload, and the
  earlier fixes (no-`v` tag filter, no-`v` publish naming, asset upload).
- **RFC 097** in `rfcs/done/` (Implemented v0.34.4); README + rfc-index updated.
  Docs updated: `release-manifest-schema.md` (profile + criticality + validation
  fields), `integration-contract.md` (exactly what the sidecar certifies),
  `release-checklist.md` / `release-policy.md` (publish when release-core required
  gates pass; validation non-blocking).

## Honest validation status

I cannot run Lean here — the toolchain host (`releases.lean-lang.org`) returns 403
in this sandbox (only `release.lean-lang.org` is allowlisted). So:

- **Verified directly:** the manifest/report/verifier behavior on synthetic gate
  records (profile, criticality, advisory placeholders, GATE-RUN binding,
  required-only pass logic); gate-0 self-test passes against the refactored
  `check.sh`; all Lean-free gates green; both workflows are valid YAML;
  `check.sh` parses.
- **Needs a CI run:** that `--release-core` completes green end-to-end on the
  runner (it should — it's the ~82 s olean build + Python gates + tarball, no
  native compile), and the actual timing of `--release-validation` (the §4
  diagnostic — which of demo/conformance is the slow pole).

## Deferred (diagnostic-gated, per your review)

- **Smoke promotion.** Once release-validation reports timings, a cheap demo
  and/or conformance *smoke* subset can be promoted into release-core as a blocking
  gate. Default until then: executables stay in validation. (RFC 097 open
  questions.)
- **`-O0` native experiment** and **`--fast` smoke** left as open items.

## For you

1. Push `0.34.4`: `release-gate` should now go green and publish the sidecar;
   `release-validation` runs separately and reports demo/conformance timings.
2. Read those timings and decide on smoke promotion.
3. Version call: this lands a new RFC + gate model under the existing v0.34.4
   (the ongoing release-CI version, never published). If you'd rather mark it
   v0.35.0 for history, say so and I'll rename.
