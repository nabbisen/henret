# RFC 060 — Trace-Based Refinement Certification

## Status

Proposed.

## Summary

Define a trace artifact format and checker so external runtimes can provide evidence that their behavior conforms to Henret.

## Motivation

Henret already has traces and a bridge direction. To make it useful beyond proofs, external runtime implementers need a concrete certification path: emit a trace, normalize it, replay it against Henret, and classify mismatches.

## Non-goals

- Do not claim trace replay proves all possible behaviors.
- Do not require native runtimes to embed Lean.
- Do not standardize binary trace formats in the first RFC.
- Do not include concurrency proof obligations.

## Design

Define a textual trace schema:

```text
version: henret-trace-v1
events:
  - op: spawn
    actor: 7
    result: spawned 0
  - op: schedule
    result: scheduled 0
```

Add a Lean-side parser or a simpler JSON-lines checker if practical. The first version may use generated Lean test files rather than a full parser.

Define mismatch classes:

- invalid result mismatch,
- state projection mismatch,
- trace event unsupported,
- non-deterministic runtime event requiring normalization.

## Formal model changes

- Add `TraceEvent` and `TraceReplayResult`.
- Define replay against `RuntimeState`.
- Define projection fields relevant to external runtimes: ready queue, running, task state, mailbox contents or occurrence ids.

## Proof obligations

- `traceReplay_sound`: if replay accepts, each event matches Henret step semantics.
- `traceReplay_preserves_wf`: accepted traces produce reachable/well-formed states.
- Theorems may be partial if parsing is outside Lean.

## Tests and examples

- Golden accepted trace.
- Golden rejected trace for invalid state transition.
- Golden trace with Mesa wake/re-receive semantics.
- CI runner for trace suite.

## Documentation updates

- Add certification guide.
- Add trace schema documentation.
- Add “trace conformance is testing evidence, not full proof” warning.

## Acceptance criteria

- External trace can be replayed.
- Rejected trace has useful diagnostics.
- At least one trace covers parking, wake, and receive.
- Proof/trust/test matrix classifies certification correctly.

## Risks and review questions

- Should trace schema include full state snapshots or only operations/results?
- How should concurrent runtime histories be linearized before replay?
- Should trace replay live in Henret or a companion package?
