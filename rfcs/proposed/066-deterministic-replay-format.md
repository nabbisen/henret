---
rfc: 66
title: Deterministic Replay Format
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [65]
blocks: []
category: observability
---

# RFC 066 — Deterministic Replay Format

## Status

Proposed strategic RFC.

## Summary

Define a stable, versioned replay format for Henret traces. A replay file records semantic profile, initial state assumptions, operation sequence, expected step results, and optional final-state predicates.

## Motivation

Henret is becoming a semantic ledger. External runtimes, examples, docs, and future adapters need a common way to say: "this execution should behave like this." A deterministic replay format provides that common language.

It also supports bug reports, regression tests, golden traces, conformance suites, and educational examples.

## Goals

- Define a human-readable replay file format.
- Make replay format versioned and profile-aware.
- Support both exact expected states and predicate-based expectations.
- Prepare for adapter conformance tests.

## Non-goals

- Do not require JSON parser integration in Lean immediately.
- Do not encode arbitrary Lean propositions in external files.
- Do not replace Lean examples.
- Do not require external runtimes to implement the format before RFC 061/073.

## Proposed format

Use TOML or JSON Lines. TOML is easier for humans; JSON Lines is easier for streaming. This RFC recommends TOML for the first version.

Example:

```toml
version = "henret-replay-v1"
profile = "mesa-unbounded-single-worker"
name = "park-deliver-rereceive"

[initial]
kind = "default"

[[steps]]
op = { spawn = { actor = 7 } }
expect = { result = { spawned = 0 } }

[[steps]]
op = { schedule = {} }
expect = { result = "ok" }

[[steps]]
op = { receive = { task = 0 } }
expect = { result = "blocked" }

[[steps]]
op = { inject = { actor = 7, body = 100 } }
expect = { result = "ok" }

[[steps]]
op = { schedule = {} }
expect = { result = "ok" }

[[steps]]
op = { receive = { task = 0 } }
expect = { result = { receivedBody = 100 } }

[final]
predicates = [
  "wellFormed",
  "readyQueueExact",
  "occurrenceUnique"
]
```

## Replay semantics

A replay file should specify:

- replay format version;
- semantic profile;
- initial state;
- ordered operations;
- expected public results;
- optional state predicates;
- optional exact final state for small examples;
- optional negative expectations.

## Lean-side representation

Add a Lean representation independent of the external parser:

```lean
structure ReplayStep where
  op : RuntimeOp
  expect : ExpectedResult

structure Replay where
  version : String
  profile : SemanticProfile
  initial : RuntimeState
  steps : List ReplayStep
  finalPredicates : List FinalPredicate
```

## Design note

The replay format should not expose every internal implementation detail. It should record stable public semantics. Internal proof helper changes must not invalidate replay files unless public behavior changes.

## Concerns

- Parser implementation could distract from proof work.
- Versioning must be strict enough to prevent silent misinterpretation.
- Expected result matching for envelopes must be careful: occurrence ids may be deterministic now, but future profiles might abstract them.

## Implementation tasks

1. Add `docs/replay-format-v1.md`.
2. Add Lean datatypes for replay specification if useful.
3. Add at least five canonical replay files under `conformance/replay/`.
4. Add a small script or Lean executable to check replay files if practical.
5. Define how replay format handles unknown future fields.
6. Update adapter-contract docs to require replay support eventually.

## Acceptance criteria

- Replay format is versioned.
- At least one parking/wake/receive scenario is representable.
- At least one negative scenario is representable.
- Public docs explain that replay files check semantic behavior, not performance.
