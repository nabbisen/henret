# RFC 054 — Semantic Profiles and Capability Sets

## Status

Implemented (v0.16.0).

## Summary

Introduce explicit semantic profiles so Henret can grow without forcing every user and every theorem to depend on every feature.

## Motivation

Henret now includes lifecycle, actor messaging, parking, timers, parenthood, occurrence identity, and bridge semantics. The project needs a way to say which subset a consumer is using. Without profiles, optional features become ambiguous: is a theorem about the core model, the actor model, the timer model, or the full model?

## Non-goals

- Do not remove the current full model.
- Do not make profiles a runtime feature flag.
- Do not weaken existing theorems.
- Do not introduce build-time conditional compilation that changes theorem statements silently.

## Design

Add a small profile vocabulary:

```lean
inductive SemanticFeature where
  | lifecycle
  | actorMessaging
  | timers
  | parking
  | supervision
  | occurrenceIdentity
  | bridge
  | schedulingPolicy
  | resourceLifetime

structure SemanticProfile where
  features : List SemanticFeature
  nodup    : features.Nodup
```

Define named profiles:

```lean
def Profile.core : SemanticProfile

def Profile.actor : SemanticProfile

def Profile.full : SemanticProfile
```

Profiles should initially be documentation and theorem-index metadata, not a different `RuntimeState`. Later RFCs may use profiles to group imports or derive specialized theorem bundles.

## Formal model changes

No immediate `RuntimeState` change is required. Add metadata modules:

```text
Henret/Profile.lean
Henret/Profile/Core.lean
Henret/Profile/Actor.lean
Henret/Profile/Full.lean
```

Add a mapping from public theorems to their minimum required profile.

## Proof obligations

- Prove named profiles have no duplicate features.
- Prove feature inclusion facts such as `Profile.core ≤ Profile.actor ≤ Profile.full`.
- Add theorem metadata tables in documentation; kernel proofs are desirable but not mandatory in the first implementation.

## Tests and examples

- Add examples showing which profile each example needs.
- Add a script that checks every live proof-index entry has a profile field.

## Documentation updates

- Update README with “Which Henret profile should I use?”
- Add `docs/profile-index.md`.
- Update proof/trust/test matrix with a `Profile` column.

## Acceptance criteria

- Named profiles exist.
- Live theorem docs classify the minimum profile.
- No existing theorem is weakened.
- Root import behavior is unchanged unless explicitly documented.

## Risks and review questions

- Should profiles become real module barrels now, or remain documentation metadata first?
- How much profile information should be kernel-checked versus doc-checked?
