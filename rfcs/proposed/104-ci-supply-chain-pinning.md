---
rfc: 104
title: CI Supply Chain Pinning and Package Metadata
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [98, 99, 102]
blocks: [79]
category: security
---

# RFC 104 — CI Supply Chain Pinning and Package Metadata

## Status

Proposed. Release-blocking for the v0.34.6 integrity milestone.

## Summary

Pin CI actions and downloaded tool artifacts to immutable identities, verify
tool checksums before execution, record those identities in release evidence,
and finish repository metadata needed for public package publication.

## Motivation

The reviewed baseline used movable action tags, let elan download the selected
Lean toolchain without a retained archive digest, and discovered mdBook through
`latest`. This is inconsistent with Henret's hash-oriented provenance posture.

## Non-goals

- Do not vendor Lean, mdBook, or GitHub Actions into the repository.
- Do not claim checksum pinning proves the upstream tool is trustworthy.
- Do not block the focused B-01 through B-07 repair on broader publication
  polish.

## Proposed design

1. Pin each GitHub Action to a full commit SHA, with a nearby human-readable
   version comment and an update procedure.
2. Pin the Lean toolchain and mdBook versions and expected SHA-256 values.
   Verify before extraction/execution. Invoke the verified Lean distribution
   directly rather than allowing elan to perform an unverified second-stage
   toolchain download.
3. Record action/tool identities and hashes in release evidence or a hashed CI
   policy file.
4. Add a scheduled/manual dependency-refresh workflow that proposes reviewed
   pin updates without mutating release runs.
5. Replace repository metadata placeholders with canonical values.

The tracked source of truth is `ci/supply-chain.json`. RFC 104 introduces
`release-core-v4` / `rfc104-release-core-v4` rather than changing retained v3
semantics. Workflows spell out
each action commit (with a version comment) because GitHub Actions expressions
cannot safely provide a dynamic `uses` ref. `scripts/ci_supply_chain.py` checks
quoted, spaced-colon, and canonical `uses` spellings against policy. The policy
also pins each complete workflow file by SHA-256: those exact reviewed bytes
are the executable-acquisition allowlist. A deliberate workflow-hash update
still permits only the registered repository Python entrypoints and Henret's
scoped self-release `gh` operations, each explicitly bound to the literal
repository `nabbisen/henret`. Repository/host overrides or reassignment,
prefixed or unparsed `gh`, interpreter snippets, and direct HTTP clients are
rejected. Downloaded tools go through
`scripts/install_ci_tool.py`, which downloads the versioned URL, verifies the
policy digest before extraction, rejects unsafe archive members, and only then
exposes the binary. Release manifests retain the full policy and its hash.
Current-profile verification binds that policy to the source archive and
requires explicit GitHub-hosted workflow provenance. A local run is always a
non-authoritative precheck, even from a clean worktree.

## Implementation tasks

1. Inventory all external workflow inputs.
2. Pin and checksum them.
3. Add policy validation and negative checksum tests.
4. Document the refresh and incident process.
5. Complete `lakefile.lean` repository metadata.

The repository metadata is already canonical at implementation time; the RFC
104 gate checks that it does not regress to a placeholder.

## Acceptance criteria

- No release/docs workflow executes an action or downloaded binary identified
  only by a movable major/latest tag.
- A checksum mismatch fails before extraction or execution.
- Pin identities are included in hashed release policy evidence.
- Updating a pin requires a reviewable source change.
- Any workflow-byte change requires a matching reviewed policy-hash update,
  and alternate YAML `uses` spellings cannot bypass action validation.
- Package repository metadata has no placeholder.
- The Lean selector and checksum-pinned archive version agree.
- Current-profile verification rejects missing/drifted supply-chain evidence
  and non-hosted provenance while retaining v1/v2/v3 compatibility.

## Risks

Pinned artifacts can disappear or require platform-specific hashes. The refresh
process must fail visibly and must not fall back to `latest`.
