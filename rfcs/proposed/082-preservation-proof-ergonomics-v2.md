---
rfc: 82
title: Preservation Proof Ergonomics v2
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: proofs
---

# RFC 082 — Preservation Proof Ergonomics v2

## Status

Proposed strategic RFC. Approved in the v0.17.0 audit review (items A2 and
A1, decision **B + A**, priority **P1**); amendments 082-A..D applied from
the RFCs 080-086 review. **Supersedes RFC 042.**

## Summary

Realise the goal RFC 042 set but did not achieve: reduce repetitive
`WellFormed` preservation code so the invariant can keep growing without
per-field proof drift. Adopt the helper lemmas RFC 042 shipped but left
unused, add operation-family "unchanged-field" lemmas with a stable naming
convention, and record before/after metrics — without letting line count
become the success metric or hiding admission guards behind helpers.
Lemma-first compression only; no heavy metaprogramming in the first pass.

## Motivation

RFC 042 shipped `Henret/Proofs/StepFields.lean` helper lemmas but the
preservation proofs remained large and copy-paste-heavy. RFC 055 is direct
evidence: closing one semantic-core extension required hand-threading
admission guards through hundreds of lines of per-field bullets across ~6
proof files. The audit also found eight of RFC 042's own `wf_*_pass` helpers
used **zero** times. Preservation maintainability now gates the cost and
safety of every future semantic feature.

## Goals

- The eight currently-dead `wf_*_pass` helpers become used, not deleted.
- A guard-wrap or unchanged-field discharge becomes ~one line per field.
- Refactored proofs stay locally inspectable; guards stay visible.
- `reachable_wf` and the public theorem surface stay unchanged.

## Non-goals

- Opaque custom tactics in this pass (defer until the lemma API is stable;
  lemma-first protects auditability — Henret's brand).
- Adding or removing any `WellFormed` field.
- New project-specific axioms.

## Scope

Adopt the existing helpers (the A1 dead set):

```text
wf_parent_spawned_pass   wf_occ_pass
wf_timed_has_deadline_pass   wf_deadline_is_timed_pass
wf_timed_has_timer_pass   wf_timed_is_waiter_pass
wf_timed_waiters_valid_pass   wf_timed_waiters_nodup_pass
```

Add operation-family unchanged-field lemmas, e.g.:

```lean
step_lifecycle_unchanged_mailboxes   step_lifecycle_unchanged_occurrences
step_time_unchanged_mailboxWaiters   step_time_unchanged_parentOf
step_messaging_unchanged_timers      step_shutdown_terminal_preservation
```

Refactor `Preservation/{Lifecycle,Messaging,Time}.lean` and, where they
hand-write matching bullets, `Restart.lean` and `Shutdown.lean`, to use them.

## 082-A — Define "used" precisely

```text
A helper is adopted iff its identifier appears outside
Henret/Proofs/StepFields.lean in a source file that is part of the library
build. (Crude but mechanical; a future rule may use Lean env introspection.)
```

A script gate enforces: every exported `wf_.*_pass` is used (by the above
rule) or explicitly annotated. The eight A1 helpers must be *used*; the
"reserved for future RFC" annotation is not permitted for them.

## 082-B — Line reduction is informative, not hard-blocking

```text
- Before/after line count and repeated-bullet count are recorded.
- Target reduction 15-25%, but release is NOT blocked solely on missing the
  target if the helper-adoption and drift-reduction gates pass.
```

## 082-C — Readability / guard-visibility rule

```text
No helper may hide a semantic branch condition that should be visible at the
operation-family proof level. Invalid / blocked / admission guards remain
visible in each operation-family preservation proof.
```

## 082-D — Helper naming convention

```text
wf_<field>_pass      field unchanged by operation
wf_<field>_update    field updated in a standard way
wf_<field>_filter    field preserved by filter/remove operation
wf_<field>_append    field preserved by append/wake operation
```

## Formal-verification concern

Do not let helper adoption make `simp` too powerful. Helpers are **not**
marked `@[simp]` unless proven non-looping and genuinely projection-like;
prefer explicit use in preservation files otherwise.

## Final-pass amendments (RFCs 080-086 v2 review)

**082-1 — Usage checker resists comments/strings.**
`scripts/helper_usage_check.py` strips Lean line/block comments and string
literals before matching (or uses a Lean-side `#check`/environment
inventory). A naive grep that comments/strings could satisfy is not
acceptable.

**082-2 — Exception-annotation syntax (for genuinely-reserved helpers).**

```lean
/-- HENRET_HELPER_RESERVED: reason; target RFC; expiry condition. -/
```

The checker rejects expired or reasonless annotations. The eight A1 helpers
must be *used*, never annotated-away.

**082-3 — Public-name stability.** No public theorem is removed or renamed
unless explicitly listed in a migration table (proof-ergonomics refactors
easily destabilize helper names).

**082-4 — Import-cost metric.** Record the number of modules imported by
`Henret.Proofs.InvariantsPreservation`, to ensure the refactor doesn't
shrink lines by pushing complexity into broader imports.

## Acceptance criteria

```text
- helper_usage_check.py strips comments/strings (or uses env inventory);
  every exported wf_.*_pass is used or HENRET_HELPER_RESERVED-annotated.
- The eight A1 helpers are used, not annotated-away.
- No public theorem removed/renamed except via a migration table.
- Guard/admission logic remains visible in each operation-family proof.
- Helpers not marked @[simp] unless proven non-looping and projection-like.
- Metrics recorded: line count, field-bullet count, hand-written field
  proofs, AND InvariantsPreservation import count. Target reduction 15-25%
  (informative, not a hard block).
- reachable_wf statement unchanged; zero new project axioms.
```

## Priority and sequencing

P1. Per the review's order it lands near the end of the wave, **but it must
precede the next large semantic feature** (RFC 056 bounded mailboxes), so
that feature is the first to benefit from the reduced per-field cost.

## References

- v0.17.0 audit review items A2/A1; RFCs 080-086 review amendments 082-A..D
  and additional recommendation 4 (lemma-first).
- Supersedes RFC 042 (preservation proof automation). RFC 042's Status flips
  to `Superseded by RFC 082` when this RFC is implemented.
- Related: RFC 062 (proof ergonomics library), RFC 068 (invariant
  dependency graph).
