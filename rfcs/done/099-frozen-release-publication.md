---
rfc: 99
title: Frozen Release Publication Immutability
status: Implemented
implemented_in: v0.34.6
supersedes: []
superseded_by: []
depends_on: [95, 96]
blocks: [102]
category: release-process
---

# RFC 099 — Frozen Release Publication Immutability

## Status

Implemented in v0.34.6. Publication now fails closed instead of clobbering an
existing tagged release or asset; closed through the review chain in
`.git-exclude/reviewed/004`–`005`.

## Summary

Make the frozen-release policy technically enforceable. Publication must fail
when a release or any canonical asset for the version already exists; routine
workflow reruns must never overwrite a tarball, sidecar, gate record, or
validation report.

## Motivation

Consumers pin the release-verification manifest hash. The current workflow uses
`gh release upload --clobber`, so a rerun can replace assets for a frozen tag.
Post-upload hash agreement proves only that the replacement set is internally
consistent, not that the release remained immutable.

## Non-goals

- Do not provide an in-place correction mechanism for a published version.
- Do not weaken post-upload verification.
- Do not change the manifest schema unless an additive field is useful.

## Proposed design

1. Before publication, query the tag, release, and canonical asset names.
2. Fail closed if the release already exists or any canonical asset name is
   present.
3. Create the release once and upload without `--clobber`.
4. Keep post-upload download and verification as a distinct integrity check.
5. Document an incident path: mark the bad release, cut a new patch version,
   generate a new sidecar, and notify pinned consumers. Never reuse the version.
6. Keep optional validation attachment immutable as well; late supplemental
   evidence must use a uniquely named, hash-addressed artifact or a new release.

## Implementation tasks

1. Move publication checks into a small testable shell/Python helper.
2. Remove every normal-path `--clobber` use for canonical release assets.
3. Add mocked or fixture-driven tests for first publish, rerun, partial asset
   presence, and release-without-assets cases.
4. Update the release policy, checklist, manifest schema, and incident notes.

## Acceptance criteria

- A first publication succeeds and a rerun for the same version fails before
  uploading bytes.
- Presence of any canonical asset fails publication.
- No normal release workflow contains overwrite authorization.
- Post-upload verification still validates the newly created immutable assets.
- The documented recovery path always uses a new version.

## Risks

Concurrent workflow runs can race between preflight and upload. The design must
also rely on the hosting API's create/upload exclusivity and treat any conflict
as failure, never as permission to overwrite.
