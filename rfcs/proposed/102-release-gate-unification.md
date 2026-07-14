---
rfc: 102
title: Release Gate Unification After Validation Repair
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [97, 98, 99, 100, 101]
blocks: [103]
category: release-process
---

# RFC 102 — Release Gate Unification After Validation Repair

## Status

Proposed. Release-blocking for the v0.34.6 integrity milestone.

## Summary

Revise RFC 097 using the v0.34.5 timing evidence: interpreted demo and
conformance become required release-core gates, and the mdBook integrity gate
must certify the exact release commit. Timeouts remain, but timeout or failure
is release-blocking.

## Motivation

RFC 097 made executable validation advisory because native code generation and
an interpreted demo compile blowup exceeded CI capacity. The tuple-pattern cause
was fixed in v0.34.5; current interpreted runs are sub-second after the library
build. Publishing semantic-reference evidence without these cheap regression
checks is no longer a sound tradeoff. Release instructions and CI behavior also
disagree, and the docs workflow does not match bare version tags.

## Non-goals

- Do not require native compilation of demo/conformance executables.
- Do not remove timeout protection.
- Do not weaken CI authority or post-upload verification.

## Proposed design

1. Run gates 2 (demo) and 4 (conformance) interpreted in release-core with
   required criticality.
2. Retain bounded timeouts; timeout and nonzero exit both fail release-core.
3. Run `check_docs.sh` in the release job or make publication depend on a
   successful docs result for the exact commit. Use the same bare `X.Y.Z` tag
   convention everywhere.
4. Keep a separate timing/diagnostic workflow only as supplemental evidence.
5. Introduce a new gate registry/profile identifier rather than silently
   changing `rfc097-ci-core-v1` semantics. Keep manifest schema changes additive
   and update the consumer verifier.
6. Make the release checklist, contributing guide, workflows, and script
   comments describe the same profiles.

## Implementation tasks

1. Refactor gate criticality and timeout handling with self-tests.
2. Integrate the mdBook exact-commit result.
3. Update manifest generation, verification, schema docs, and consumer recipes.
4. Correct stale workflow comments and release documentation.
5. Measure cold and cache-warm timings on the standard runner.

## Acceptance criteria

- Release-core fails on demo failure, conformance failure, either timeout, docs
  structure/link failure, or mdBook build failure.
- A bare version tag runs both proof/release and docs requirements on the same
  commit before publication.
- The manifest names the new registry/profile and records every required gate.
- The verifier rejects a sidecar missing any newly required result.
- The diagnostic workflow is not the only executor of a release requirement.
- All release instructions match observed script behavior.

## Risks

Cold CI timing, not local cached timing, controls timeout selection. The gate
must preserve an escape path for diagnosis without allowing publication.
