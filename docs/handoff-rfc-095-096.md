# Checkpoint handoff — RFC 095 implemented, RFC 096 revised (v0.34.2)

**For:** architect review
**Release:** `henret-v0.34.2.tar.gz`
**Scope:** release-process only — no model, proof, or theorem change. Axioms
unchanged; public theorem surface unchanged (101 names). `check.sh --fast` and
the docs gate green.

## RFC 095 — Published Release-Verification Manifest (Implemented)

All six required amendments incorporated:

- **§3.1 post-upload verification** — new `scripts/verify_release_manifest.py`
  re-checks a published tarball against its manifest (tarball hash,
  `source_archive`, gate-pass, GATE-RUN.md binding), non-zero on mismatch.
  Validated locally: passes on a good release, fails on a tampered tarball with
  precise errors. `release-checklist.md` adds the post-upload re-download step.
- **§3.2 named/sized archive** — `release_manifest.py` adds `source_archive`
  `{name, sha256, size_bytes}`; `tarball_sha256` retained (additive,
  `manifest_schema` stays 1).
- **§3.3 GATE-RUN.md integrity** — `release_manifest.py` now renders GATE-RUN.md
  from the *core* manifest, then binds it via `human_summary.sha256`; the summary
  is added after rendering, so the bound hash can't go stale (no circular hash).
  `check.sh` delegates GATE-RUN.md generation to the script. Verified: the bound
  hash matches the file on disk.
- **§3.4 log retention** — GATE-RUN.md carries the per-gate id/name/status/ms
  table so a reviewer has self-contained gate evidence even if CI log URLs are
  ephemeral; stable log hosting is left to CI config, documented as such.
- **§3.5 consumer recipe** — `integration-contract.md` §11 gives the exact
  `sha256sum`/`jq` commands and the bundled checker.
- **Signing** — kept a named follow-up; no `signatures` field emitted, so
  `manifest_schema` stays 1 and hash-only verification trusts the publication
  channel (§D5).

RFC 095 moved to `rfcs/done/` (Implemented v0.34.2).

### Note on in-sandbox verification

I validated the manifest schema, the GATE-RUN.md hash binding, and the verifier
**directly** (synthetic gate records + a test archive), because a full
`check.sh --release` can't complete in this sandbox — the `henret-demo` (`Main`)
executable's compile exceeds the per-command budget. The library builds clean;
this is a resource limit, not a regression. The `--release` manifest path
(`release_manifest.py` + the `check.sh` wiring) is exercised by the synthetic run
and is unchanged in shape for CI.

## RFC 096 — Stack Release Contract (revised, still Proposed)

"Revise before approval" — folded in all seven amendments, kept `Proposed`:

- **§4.1** per-package manifests keep `manifest_schema` (no rename of the RFC 080
  field); the stack manifest uses a distinct `stack_manifest_schema`.
- **§4.2/§4.3** added `dependency_edges` (stack) cross-checked against
  per-package `dependencies` declarations.
- **§4.4** `scripts/verify_stack_release.py` named as the validation tool /
  follow-up; schema designed to be mechanically checkable.
- **§4.5** `depends_on` now `[80, 81, 95]` — trust-inventory fields cited from
  RFC 081, not redefined.
- **§4.6** peer-governance wording (henret hosts `manifest_schema 1`; breaking
  changes need cross-project coordination once adopted).
- **§4.7** mirror semantics — hash is identity, URL is location.

RFC 096 stays in `rfcs/proposed/` awaiting re-approval; nothing from it is
implemented yet (no schema doc, no `verify_stack_release.py`).

## Evidence

`lakefile.lean` → v0.34.2; CHANGELOG v0.34.2 entry. `rfc_metadata_check` clean
(97 files); rfc-index regenerated; README rows updated (095 Implemented, 096
revised/Proposed). No matrix/proof-index change — release-process RFCs
(080/081/095) are not proof-trust-test claim rows, by existing precedent.

## For your review

- RFC 095's open questions remain: signing mechanism, and per-version-prefixed
  filenames vs a bare name + version field.
- RFC 096 is ready for a re-approval pass; if you approve, implementation is the
  `release-manifest-schema.md` doc plus `verify_stack_release.py`, and the
  per-package `dependencies` emission would be coordinated with iotakt/jemmet.
