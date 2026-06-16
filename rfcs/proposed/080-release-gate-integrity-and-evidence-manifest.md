---
rfc: 80
title: Release Gate Integrity and Evidence Manifest
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [85, 84]
blocks: [81, 83, 86]
category: release-process
---

# RFC 080 — Release Gate Integrity and Evidence Manifest

## Status

Proposed strategic RFC. Approved in the v0.17.0 audit review (item A7,
decision **A+B**, priority **P0 — blocks the next release**); amendments
080-A..D applied from the RFCs 080-086 review.

## Summary

Make the release gate a trusted, enforced, and auditable part of Henret's
engineering process. Define explicit fast (developer) and release (full)
gate modes, wire the full suite into CI as the *authoritative* source of
release evidence, add a self-test for the gate's own internal consistency,
and have the gate script emit a hashed, non-manual verification manifest
for every release.

## Motivation

The v0.17.0 audit established that `check.sh` could not have been passing
end-to-end before the audit: the axiom-audit gate referenced a
non-existent theorem (`run_preserves_owner`), its allowlist had drifted
~26 entries out of sync with the heredoc, and two examples had been broken
since RFCs 031/033. These accumulated silently — the suite was being run
partially or not at all (consistent with the demo target's OOM in
constrained environments).

In a formal-verification project the release gate is part of the trusted
process and a supply-chain assurance boundary. If gate drift accumulates,
a consumer cannot distinguish "the theorem holds" from "the theorem was
not checked in the expected release configuration." A bad release manifest
would itself be a supply-chain integrity failure.

## Goals

- Every gate runs on every change, in CI, and fails the build on drift.
- A constrained developer mode that can never masquerade as a release.
- The gate suite validates its own internal consistency.
- Each release carries a hashed, CI-generated, auditable evidence manifest.

## Non-goals

- Verifying the out-of-tree runtime package's tests (see RFC 081).
- Changing what any individual gate checks semantically.

## Deliverables

```text
scripts/check.sh                  --fast / --release modes; numbered stages
scripts/check_selftest.py         gate-suite internal-consistency self-test
.github/workflows/ci.yml          runs --release on a sufficient runner
release/GATE-RUN.md               human-readable per-release gate log
release/release-verification.json machine-readable manifest (schema below)
                                  EXTERNAL release artifact — NOT inside the
                                  source tarball whose sha256 it records (080-1)
```

Stable gate stages (self-test runs first, 080-3):

```text
0.  check_selftest.py (gate-suite internal consistency; before all semantic gates)
1.  lake build Henret.Model
2.  lake build Henret.Proofs
3.  lake build Henret
4.  henret-demo (release mode only; --fast may skip)
5.  examples build + eval
6.  golden conformance suite + coverage gate (RFC 083)
7.  doc-symbol check
8.  strict axiom audit
9.  stale / generated-doc consistency checks (RFC 084 count-check)
10. linter warning budget (RFC 086)
```

## 080-A — Fast vs release modes (explicit)

```text
check.sh --fast      local/constrained developer mode
                     may skip heavyweight demo / runtime-adjacent checks
                     NEVER valid for release; emits no manifest

check.sh --release   full gate suite; includes the demo
                     emits release/release-verification.json
                     required for release
```

Acceptance: **only `--release` can produce a release manifest.** Staging
the demo (so `--fast` completes in constrained envs) must never let a
*release* run skip it.

## 080-B — Non-manual, hashed manifest

The manifest is produced by the gate script, never hand-written:

```json
{
  "manifest_schema": 1,
  "generated_by": "scripts/check.sh --release",
  "package": "henret",
  "version": "0.x.y",
  "timestamp_utc": "...",
  "git_commit": "...",
  "git_dirty": false,
  "tarball_sha256": "...",
  "lake_manifest_sha256": "...",
  "lean_toolchain_sha256": "...",
  "os": "...",
  "runner": "...",
  "gates": [
    {"id": 1, "name": "lake build Henret.Model", "command": "...",
     "status": "pass", "duration_ms": 1234,
     "stdout_sha256": "...", "stderr_sha256": "..."}
  ],
  "runtime_package": {"included": false, "version_or_commit": null, "evidence": "..."}
}
```

Logs need not be inline, but the manifest hashes them or points to retained
CI artifacts. If the release artifact is rebuilt, the manifest must be
regenerated.

## 080-C — Self-test coverage

`check_selftest.py` must verify, at minimum:

```text
- every gate id appears exactly once and has a stable name
- axiom-audit allowlist matches the #print-axioms inputs exactly
- the doc-symbol check has a non-empty target file set
- the stale-phrase / generated-doc check has a non-empty target file set
- the warning-budget gate is wired and active
```

## 080-D — CI is authoritative

```text
A release is valid only if its release-verification.json was generated by CI
from the exact release commit/tag, not by a local run alone.
```

Local `--release` runs are useful for pre-checks; authoritative release
evidence comes from controlled CI.

## Final-pass amendments (RFCs 080-086 v2 review)

**080-1 — Non-self-referential hashing.** `release-verification.json` is an
*external* release artifact, not inside the tarball whose `tarball_sha256`
it records. (`tarball_sha256` = the source archive, which excludes the
`release/` manifest.)

**080-2 — Hash the gate policy.** The manifest records the gate-script
hashes so it states *which gate policy* passed:

```json
"gate_policy": {
  "check_sh_sha256": "...", "check_selftest_py_sha256": "...",
  "axiom_audit_py_sha256": "...", "doc_symbol_check_py_sha256": "...",
  "warning_budget_py_sha256": "..."
}
```

**080-3 — Self-test is a numbered gate (stage 0).** Run before all semantic
gates so it can never be silently skipped.

**080-4 — Dirty-tree handling.** `--release` fails if `git_dirty = true`,
except for generated release artifacts written *after* the source-tree
cleanliness check and excluded from the source archive (so manifest
generation cannot dirty the tree it certifies).

**080-5 — Log retention.** Each stdout/stderr hash must correspond to a
retained artifact path or URL (a hash without the log is weak for review).

## Acceptance criteria

```text
- check_selftest.py is gate stage 0; CI runs all --release gates on a runner
  that builds the demo without OOM.
- release-verification.json is external to the source tarball; tarball_sha256
  records the source archive excluding release/.
- The manifest includes gate_policy script hashes and per-gate log hashes,
  each pointing to a retained artifact.
- --release fails on a dirty source tree (except post-check generated
  release artifacts).
- Only --release produces a manifest; --fast never does.
- A release is not cut unless CI generates the manifest from the exact
  release commit/tag with all --release gates passing.
```

## Priority and sequencing

P0. Per the v2 review's revised order, RFC 080 lands **third** — after
RFC 085 (metadata) and RFC 084's `doc_count_check.py` stopgap, so all the
hooks it needs exist: stage 9 consumes 084's count-check, stage 10 is
RFC 086's warning budget, stage 6 is RFC 083's coverage gate. 080's
framework is implemented with those later stages stubbed, then each later
RFC fills its stub.

## References

- v0.17.0 audit review item A7; RFCs 080-086 review amendments 080-A..D
  and the security/supply-chain note.
- RFC 017 (release gate and CI), RFC 020 (strict axiom audit) — hardened
  and enforced here.
- RFC 081 (evidence ledger) populates the manifest's `runtime_package` field.
