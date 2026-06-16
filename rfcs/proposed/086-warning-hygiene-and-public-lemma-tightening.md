---
rfc: 86
title: Warning Hygiene and Public Lemma Tightening
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [80]
blocks: []
category: tooling
---

# RFC 086 — Warning Hygiene and Public Lemma Tightening

## Status

Proposed strategic RFC. Approved in the v0.17.0 audit review (item A8,
decision **B — drop genuinely unused public hypotheses, underscore
proof-local bindings**, priority **P2**); amendments 086-A..D applied from
the RFCs 080-086 review.

## Summary

Drive the build's unused-variable warning count to zero, tighten public
lemmas whose statements carry hypotheses they don't use, and add a robust
warning-budget gate so the count stays at zero. Each dropped hypothesis is
reviewed to confirm the lemma is genuinely stronger and that no admission
guard disappeared by accident.

## Motivation

The audit found five `unused variable` warnings. Individually trivial, but
in a formal library an unused hypothesis is often the first sign of a stale
theorem shape — a lemma claiming to need more than it does, or a guard that
quietly stopped being used after a semantic change. A zero-warning policy
makes that signal visible instead of buried.

Current warnings:

```text
Henret/Scheduler/Model.lean:133          hp
Henret/Proofs/StepProjections.lean:126   hfresh
Henret/Proofs/Messaging.lean:365-367     hrt, hts, how  (over-specified hyps)
```

## Goals

- Zero unused-variable warnings on a full build.
- Public lemmas state only the hypotheses they use.

## Non-goals

- Suppressing the linter globally (hides future real warnings).
- Broad refactoring of proof internals beyond the flagged sites.

## Scope

```text
- Rename proof-local unused bindings to _hp, _hfresh, etc.
- For the Messaging.lean lemma(s), drop the genuinely unused hypotheses if
  the statement stays meaningful and no downstream import breaks badly.
- Add a warning-budget gate: expected unused-variable warnings = 0.
```

## 086-A — Warning detector

Lean/Lake warning output is noisy and environment-dependent; specify
detection:

```text
lake build Henret 2>&1 | tee build.log
python3 scripts/warning_budget.py build.log --unused-variables 0
```

If the project's toolchain has a reliable warning-as-error option, use it;
otherwise parse logs conservatively. This is RFC 080 gate stage 10.

## 086-B — Removed hypotheses ARE API tightening

Removing an unused hypothesis changes the theorem type (a strengthening).
Wording:

```text
No semantic model behavior changes. Some public lemma types may be tightened
by removing unused hypotheses; because Henret is pre-public-stability, this
is accepted.
```

## 086-C — Deprecation only if a stability policy requires it

```text
If a lemma is marked public-stable under RFC 070, add a @[deprecated] wrapper
pointing to the tighter replacement. Otherwise tighten directly (preferred,
since Henret is pre-public-stability).
```

## 086-D — No global suppression (acceptance-level)

```text
No file-level or global linter suppression is added unless justified by a
local comment and approved in review.
```

## Formal-verification note

Each dropped hypothesis is reviewed: is the theorem truly stronger, or did
an admission/guard condition disappear accidentally after a semantic change?
The former is the intended outcome; the latter would be a regression to
catch here.

## Final-pass amendments (RFCs 080-086 v2 review)

**086-1 — Total warning budget, not only unused-variables.** Unused
variables must be zero; the gate targets *all* warnings with an explicit
allowlist for justified exceptions:

```text
warning_budget.py build.log --all-warnings 0
  [--allow <category/file/line + justification>]
```

This prevents new warning classes accumulating while unused-vars stay zero.

**086-2 — Record theorem-statement migrations.** For each public lemma whose
hypotheses are dropped:

```text
lemma | old hypotheses | new hypotheses | downstream breakage | wrapper needed?
```

**086-3 — Compatibility-wrapper policy.**

```text
No wrapper for non-public-stable lemmas (tighten directly).
Public-stable lemmas (RFC 070): add @[deprecated] wrapper, removed at the
next declared breaking window.
```

**086-4 — Warning budget covers the full gate build scope.** It runs over the
same scope the gate builds (Henret + examples + demo), not just
`lake build Henret`. RFC 080 defines the exact build command; RFC 086
consumes that log:

```text
lake build Henret <examples-targets> <demo-targets> 2>&1 | tee build.log
```

## Acceptance criteria

```text
- warning_budget.py enforces --all-warnings 0 (with an explicit, justified
  allowlist if any), over the full gate build scope (086-4); it is RFC 080
  stage 10.
- lake build (full gate scope) emits zero unused-variable warnings.
- Each dropped hypothesis is recorded in a migration table (086-2) and
  reviewed (theorem genuinely stronger, no guard lost).
- Wrapper policy per 086-3; no global/file-level suppression (086-D).
- No new project axioms; no semantic model behavior changed.
```

## Priority and sequencing

P2. Per the review, batched early (right after RFC 081) because the
warning-budget gate plugs into RFC 080 stage 10.

## References

- v0.17.0 audit review item A8 and additional recommendation 5
  ("warning budget = zero"); RFCs 080-086 review amendments 086-A..D.
- RFC 080 (release gate integrity) — hosts the warning-budget gate.
- RFC 070 (public theorem API stability) — gates the deprecation path.
