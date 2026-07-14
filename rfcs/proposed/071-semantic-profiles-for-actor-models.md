---
rfc: 71
title: Semantic Profiles for Actor Models
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [70]
blocks: []
category: model-semantics
---

# RFC 071 — Semantic Profiles for Actor Models

## Status

Proposed strategic RFC.

## Summary

Define actor-model semantic profiles for Henret, such as Mesa mailbox semantics, Hoare handoff semantics, bounded mailbox semantics, selective receive, priority mailbox, and Erlang-like supervision. Profiles make Henret extensible without implying that one actor model is universal.

## Motivation

Actor systems differ. Henret currently leans toward Mesa-style mailbox semantics: delivery may wake a waiter, but the message is not atomically transferred to that waiter. Future features such as bounded mailboxes, selective receive, priority, timeout, and supervision can create semantic variants.

A profile system helps Henret say:

- this theorem applies to base Mesa/unbounded profile;
- this theorem applies only to bounded mailbox profile;
- this runtime adapter claims conformance to profile X.

## Goals

- Define a profile vocabulary.
- Separate base semantics from optional extensions.
- Make conformance and replay files profile-aware.
- Avoid uncontrolled feature flags.

## Non-goals

- Do not implement all profiles now.
- Do not make every existing theorem polymorphic over profiles immediately.
- Do not encode complex dependent profile constraints before needed.

## Proposed profiles

### Base profile: `mesa-unbounded-single-worker`

Current Henret semantics:

- unbounded mailboxes;
- Mesa wake-one;
- no fairness/liveness guarantee;
- single ready queue;
- deterministic logical clock.

### Optional profile: `bounded-mailbox`

Adds capacity and send blocking/drop semantics.

### Optional profile: `selective-receive`

Adds receive predicates and mailbox scanning semantics.

### Optional profile: `receive-timeout`

Adds waiting for message or deadline.

### Optional profile: `priority-scheduler`

Adds priority order to ready queue.

### Optional profile: `supervision-tree`

Adds parent-scoped cascade cancel/restart semantics.

## Lean representation

Start with documentation-only plus a simple data representation:

```lean
structure SemanticProfile where
  mailboxBounded : Bool
  selectiveReceive : Bool
  receiveTimeout : Bool
  priorityScheduling : Bool
  supervisionRestart : Bool
  workerCount : Option Nat
```

Later, profile-specific theorem namespaces can be added:

```lean
namespace Henret.Profile.MesaUnbounded
namespace Henret.Profile.BoundedMailbox
```

## Design note

Profiles should clarify semantics, not multiply proof obligations prematurely. The base profile remains the default.

## Concerns

- Too many profiles can fragment the theorem corpus.
- Boolean profile flags can express invalid combinations unless constrained.
- Polymorphic profile proofs may be much harder than separate profile modules.

## Implementation tasks

1. Add `docs/semantic-profiles.md`.
2. Declare base profile explicitly in README/guided tour.
3. Add profile field to replay format and conformance suites.
4. Add compatibility table for RFC features.
5. Defer Lean-level profile polymorphism until at least two implemented profiles exist.

## Acceptance criteria

- Current semantics are named as a base profile.
- Future features can state which profile they extend.
- Replay and adapter docs mention profile compatibility.
