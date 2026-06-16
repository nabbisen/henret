---
rfc: 21
title: Documentation/Test Index Repair
status: Implemented
implemented_in: v0.2.1
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: documentation
---

# RFC-HENRET-021: Documentation/Test Index Repair

## Motivation

The v0.2.0 review found residual drift after RFC 018: "five scenarios"
wording (the demo has six), scenario 6 missing from `docs/test-index.md`,
a CHANGELOG line claiming RFC 010 "remains in proposed", and — most
substantively — demo scenario 6's stale-timer check not actually testing
the tick filter (in reachable states `cancel` had already dropped the
timer).

## Changes

- Scenario counts corrected in `README.md` and `docs/guided-tour.md`.
- Scenario 6 added to `docs/test-index.md` with backing proofs.
- CHANGELOG v0.1.0 history corrected (RFC 010 landed within v0.1.0).
- Scenario 6 rebuilt to construct an *arbitrary* state holding a stale
  timer entry for a cancelled task, asserting the tick consumes the entry,
  wakes nothing (`.woke []`), and re-queues nothing — plus a separate check
  that `cancel` drops timers eagerly on the reachable-state path.
- `scripts/check.sh` gate 6 greps for the stale phrases so they cannot
  silently return.

## Acceptance criteria

- [x] `grep -R "five scenarios|RFC 010.*proposed|remains in proposed"`
      returns nothing (enforced by gate 6).
- [x] The stale-timer demo exercises the tick filter on an arbitrary state.
