# Checkpoint handoff — RFC 097 CI fix + architect items (v0.34.4)

**For:** architect
**Release:** `henret-v0.34.4.tar.gz` (dev artifact; published assets are no-`v`)
**Scope:** CI config + release-process docs only. No model/proof/theorem change;
axioms unchanged; public surface 101 names; `manifest_schema` stays 1. All
Lean-free gates green (self-test: 10 gates, 156/156 axioms); both workflows valid.

## The release-core failure — root cause and fix

The v0.34.4 run reached the manifest step (every gate passed) and died only on
`FAIL: --release-core on a dirty source tree (080-4)`. Root cause: the CI "Install
elan" step ran `curl … | tar xz` **in the checkout**, dropping the `elan-init`
installer binary into the repo. It was untracked (not gitignored) and also not in
the tarball excludes — so it both dirtied the tree and would have polluted the
archive. Earlier runs died at gate 2 (demo) before ever reaching the dirty check,
so this is a newly-exercised path.

Fixed at three layers (so it cannot recur):

1. Both workflows install elan in `/tmp` — the binary never enters the checkout
   or the tarball.
2. `.gitignore` ignores `/elan-init` (+ `/elan.tar.gz`); the tarball excludes
   `./elan-init`.
3. `release_manifest.py`'s dirty-tree exception now ignores tooling/cache paths
   (mirrors the tarball excludes: `.lake/`, `__pycache__`, `*.pyc`, `docs/book/`,
   `.elan/`, `.cache/`, `elan-init`), not just `release/`. The manifest records
   `git_dirty_paths` and `check.sh` now prints the offending paths + raw
   `git status --porcelain` on failure, so any future dirt is self-diagnosing.

Verified in an isolated git repo: a tree carrying only elan-init + `.lake` +
`__pycache__` + `release/` reads `git_dirty: false`; a real source edit still reads
`true`. (`lake-manifest.json` is tracked and stable with no external deps; if it
ever shows up dirty, the new diagnostic print will name it.)

## Architect review items folded (§4–§7)

- **§4 gate registry.** Manifest now carries `gate_registry: rfc097-ci-core-v1`.
  RFC 097 did **not** renumber — it kept the existing 10-gate (0–9) registry and
  added `criticality`. The full 0–9 mapping is documented in
  `release-manifest-schema.md`; consumers key off `gate_registry` +
  `release_profile`, not raw IDs.
- **§5 alias policy.** Documented: since RFC 097 `--release` ≡ `--release-core`;
  `generated_by` is `scripts/check.sh --release-core` and `release_profile` is the
  contract, not the command name.
- **§6 `validation_reports` immutability.** Documented rule: the core manifest is
  not mutated post-publication; a later validation run publishes its own separate
  sidecar, linked from the release page, never by rewriting the manifest.
- **§7 consumer recipe.** `integration-contract.md` now gives the exact `ci-core-v1`
  verification steps (profile + gate_registry, `required_gates_passed`, required
  gates pass, advisory may be `not_run_in_release_core`, validation supplemental) —
  which is exactly what `verify_release_manifest.py` enforces.

## release-validation "long run"

Expected, and working as designed: the interpreted exhaustive conformance is the
slow pole (the §4 timing diagnostic confirming it). It is **non-blocking** — a long
or timed-out validation never blocks the sidecar. I trimmed its timeout 120 → 45
min to bound the waste; demo runs before conformance and each gate is timed live,
so even a timeout yields the diagnostic ("demo: Xs; conformance: still running").
That data is what drives the deferred smoke-promotion decision.

## Still CI-confirmable only (your closure conditions 1–2)

1. release-core completes green and publishes tarball + sidecar + GATE-RUN.
2. post-upload verification passes against the downloaded artifacts.

I can't run these here (Lean toolchain host is 403-blocked in this sandbox), but
the dirty-tree blocker that stopped (1) is now fixed. Re-push `0.34.4`. Staying
v0.34.4 (unpublished); say the word if you'd rather mark it v0.35.0.
