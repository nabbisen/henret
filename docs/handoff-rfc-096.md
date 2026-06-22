# Checkpoint handoff — RFC 096 implemented (v0.34.3)

**For:** architect review
**Release:** `henret-v0.34.3.tar.gz`
**Scope:** release-process / stack-integration only — no model, proof, or theorem
change. Axioms unchanged; public theorem surface unchanged (101 names).
`check.sh --fast` and the docs gate green.

## RFC 096 — Stack Release Contract (Implemented)

Approved with minor amendments; all of §4.1–4.6 and the §5 acceptance additions
are folded in.

- **§4.1 verifier ships with the RFC.** `scripts/verify_stack_release.py` is a
  minimal local-file verifier: it resolves each package's manifest by **hash**
  (not URL, RFC 096 D6) from a manifest directory, checks package
  name/version/uniqueness and (optionally) tarball hashes, then checks each edge's
  consumer/provider resolution, `provider_manifest_sha256`, and that the edge
  matches the consumer manifest's `dependencies`. Validated on a synthetic
  two-package stack: passes a consistent stack, and fails (exit 1, precise error)
  when an edge claims a provider version the consumer never declared.
- **§4.2 consumer resolution.** Normative rule: each edge's `consumer`/`provider`
  resolves to exactly one package entry; the consumer manifest is the one that
  entry's `manifest_sha256` identifies — no duplicate `consumer_manifest_sha256`.
- **§4.3 provider tarball.** Stated explicitly: edges pin providers by manifest
  hash; the provider tarball hash comes from the provider package entry and is
  verified against the provider manifest, not duplicated on the edge.
- **§4.4 uniqueness.** `packages[].package` unique; edges identified by
  `(consumer, provider, surface)`; each edge resolves to exactly one consumer and
  one provider; a consumer dependency matches at most one edge per surface.
- **§4.5 exact pins only.** v1 pins exact releases; compatibility ranges are out
  of scope (consumer docs / a future RFC). Recorded as design point D8.
- **§4.6 trust inventory optional.** RFC 081 fields are optional per package; if
  present they MUST follow RFC 081; stack verification does not require validating
  downstream trust inventories.

New normative doc `docs/src/release-manifest-schema.md` describes both schemas
(`manifest_schema 1` per-package, `stack_manifest_schema 1` stack), the rules,
and what the contract does/does not protect against. `integration-contract.md`
points consumers at it and states henret does not verify downstream packages.

RFC 096 moved to `rfcs/done/` (Implemented v0.34.3); README row and rfc-index
updated.

### In-sandbox verification note (unchanged from v0.34.2)

The schema additions and both verifiers (`verify_release_manifest.py`,
`verify_stack_release.py`) were validated directly with synthetic fixtures,
because a full `check.sh --release` cannot finish here — the `henret-demo`
(`Main`) compile exceeds the sandbox per-command budget. The library builds
clean; this is a resource limit, not a regression.

## Evidence

`lakefile.lean` → v0.34.3; CHANGELOG v0.34.3 entry. `rfc_metadata_check` clean
(97 files); rfc-index regenerated; docs gate at 58 pages / 204 links / build OK.
No matrix/proof-index change — release-process RFCs (080/081/095/096) are not
proof-trust-test claim rows, by existing precedent.

## State for next cycle

The RFC 095/096 provenance thread is closed on the henret side. Remaining
follow-ups are cross-project: signing (RFC 095 follow-up), and iotakt/jemmet
emitting conforming per-package manifests + the stack manifest. The henret model
roadmap (Phase 2B-2 pilot, RFC 068, the bridge spine) is untouched and ready when
you want to resume it.
