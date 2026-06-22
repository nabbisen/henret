---
rfc: 95
title: Published Release-Verification Manifest
status: Implemented
implemented_in: v0.34.2
supersedes: []
superseded_by: []
depends_on: [80, 81]
blocks: [96]
category: release-process
---

# RFC 095 — Published Release-Verification Manifest

## Status

Implemented in v0.34.2. Approved with amendments (architect review); the required
amendments are incorporated below and recorded in *As built* at the end. Raised
by the jemmet team (HTTP server consumer, via iotakt) who want to anchor henret
provenance at fetch time rather than trusting a CI log.

## Summary

RFC 080 already assembles a `release-verification.json` manifest — gate
evidence, per-script and per-artifact SHA-256, `tarball_sha256`,
`lake_manifest_sha256`, `lean_toolchain_sha256`, the `runtime_package` block,
and the RFC 081 evidence-ledger link. Today `check.sh --release` writes it to
the git-ignored `release/` directory: a **release-run record**, not a consumer
artifact. It is excluded from the published tarball and never published beside
it.

This RFC makes the manifest (and its human summary `GATE-RUN.md`) a
**first-class published artifact**, fetchable alongside each release tarball, so
a downstream consumer can verify the integrity and gate-provenance of the exact
archive it downloaded — without trusting an out-of-band CI log.

## Motivation

A consumer pinning henret (iotakt, and through it jemmet) wants to answer, at
the moment it fetches a release: *is this the archive henret published, and did
it pass henret's gates?* The manifest already contains the answer
(`tarball_sha256` over the canonical archive plus per-gate pass evidence), but
because it lives only in a CI-side `release/` directory there is nothing for the
consumer to fetch and compare against. The provenance exists but is not
**addressable**.

## Design

### D1 — The published tarball is the canonical archive

The artifact whose hash the manifest records MUST be the reproducible archive
built by `check.sh --release` (`--sort=name`, fixed `--mtime`, `--owner=0
--group=0 --numeric-owner`, and — as of v0.34.1 — the full build/cruft exclude
set). Ad-hoc tarballs with nondeterministic ordering or included build artifacts
are not publishable, because their hash would not match the manifest.

### D2 — Publish the manifest beside the tarball

Each release publishes, together:

```
henret-vX.Y.Z.tar.gz                      # canonical archive
henret-X.Y.Z.release-verification.json   # the RFC 080 manifest
henret-vX.Y.Z.GATE-RUN.md                 # human-readable gate summary
```

The manifest is **not** inside the archive it hashes (RFC 080-1,
non-self-referential). The `.json` is the machine artifact; the `.md` is for
humans browsing a release page.

### D3 — Integrity artifact, not a secret-bearing one

The manifest carries only hashes, gate records, the git commit, version, and the
build environment (`os`, `runner`). It contains no credentials. Publishing it
widens no attack surface beyond what a release page already exposes.

### D4 — Consumer verification recipe (documented)

```
1. Fetch henret-vX.Y.Z.tar.gz and …release-verification.json from the same
   release.
2. Recompute sha256(tarball); compare to manifest.tarball_sha256.
3. Confirm every gate record has status "pass".
4. Optionally pin manifest.git_commit / manifest.version.
```

This recipe is added to `integration-contract.md` so it is part of the stable
consumer surface.

### D5 — Trust anchor and its limit

The trust anchor is the publication channel (e.g. a GitHub release page served
over TLS): the consumer trusts that the `.json` published next to the tarball is
authentic. This RFC does **not** add cryptographic signing — an attacker who can
replace both the tarball and the manifest on the channel defeats hash-only
verification. Signing (minisign / sigstore over the manifest) is deliberately
left to a follow-up so this RFC can ship the addressable-provenance step now.

## Acceptance criteria

- `check.sh --release` continues to emit `release/release-verification.json` and
  `release/GATE-RUN.md` over the canonical archive.
- The manifest carries a `source_archive` block (`name`, `sha256`, `size_bytes`)
  beside the retained `tarball_sha256` (§3.2), and binds `GATE-RUN.md` by hash in
  `human_summary` (§3.3) so the human summary cannot drift.
- **Post-upload verification (§3.1):** after publishing, the release procedure
  re-downloads the published tarball and manifest and confirms the recomputed
  SHA-256 matches `tarball_sha256` — catching a wrong-file upload.
- `scripts/verify_release_manifest.py` performs the consumer / post-upload check
  (tarball hash, `source_archive`, gate-pass, `GATE-RUN.md` binding), exiting
  non-zero on mismatch; `integration-contract.md` gives the exact commands.
- The release procedure (`docs/src/release-checklist.md`, release-policy)
  requires publishing both files beside the tarball, with the published tarball
  being the canonical `--release` archive.
- `integration-contract.md` documents the consumer verification recipe (D4) as
  stable surface.
- No secret material appears in the manifest (existing controls re-verified).

## As built (v0.34.2)

- **§3.1 post-upload verification** — `scripts/verify_release_manifest.py` is the
  re-download check; the release checklist requires it after upload.
- **§3.2 named/sized archive** — `release_manifest.py` adds `source_archive`
  `{name, sha256, size_bytes}`; `tarball_sha256` is retained at `manifest_schema`
  1 (additive change, no schema bump).
- **§3.3 GATE-RUN.md integrity** — `release_manifest.py` now renders GATE-RUN.md
  from the *core* manifest and then binds it via `human_summary.sha256`; because
  the summary is added after rendering, the bound hash cannot become stale (no
  circular hash). `check.sh` delegates GATE-RUN.md generation to the script.
- **§3.4 log retention** — the manifest hashes gate stdout/stderr (RFC 080);
  GATE-RUN.md carries the per-gate id/name/status/ms table so a reviewer has
  self-contained gate evidence even if CI log URLs are ephemeral. Stable
  log-archive hosting is left to the CI configuration, not this RFC.
- **§3.5 consumer recipe** — exact `sha256sum`/`jq` commands and the bundled
  checker are documented in `integration-contract.md` §11.
- **Signing** stays a follow-up: it will be an additive optional field in a
  future `manifest_schema`; hash-only verification trusts the publication channel
  (§D5). No `signatures` field is emitted now, to keep `manifest_schema` 1 stable.

## Open questions

- **Signing.** minisign vs sigstore; whether the henret release key is
  documented in the integration contract. Follow-up RFC.
- **Filename convention.** Resolved in v0.34.4: published GitHub release
  assets are no-`v` (`henret-X.Y.Z.*`); local/dev tarballs keep the `v`-prefix.
  (Originally posed as per-version-prefixed vs bare
  `release-verification.json` plus a version field inside. Prefixed names are
  unambiguous when several releases are mirrored in one directory.
- **Mirroring.** Whether a stack consumer (RFC 096) re-hosts the henret manifest
  or references the upstream release URL by hash.
