# Checkpoint handoff — v0.34.4: release CI fix + provenance publication

**For:** architect / maintainer
**Release:** `henret-v0.34.4.tar.gz` (dev artifact; published GitHub asset will be
`henret-0.34.4.tar.gz`)
**Scope:** CI / release-process only — no model, proof, or theorem change. Axioms
unchanged; public theorem surface unchanged (101 names). `check.sh --fast` and the
docs gate green.

## What broke and why

The tag push of `0.34.3` produced an empty release page (only GitHub's auto
source archives), and the CI release gate failed at **gate 2 (demo) with exit
143 = SIGTERM**. Reading `ci.yml` showed three distinct problems, all fixed here.

### 1. Gate 2 (demo) + gate 4 (conformance): native exe build was the cost

`gate_demo` ran `lake build && lake exe henret-demo` and `gate_conformance` ran
`lake exe henret-conformance` — both natively compile an executable, i.e. C
codegen for the whole project (~80 modules) + link. On a stock runner that first
OOM-killed (SIGTERM/143); adding swap stopped the kill but left the native build
grinding ~1 h until the 60-minute job timeout. Note gate 1 (the full library to
**oleans**) finished in ~82 s — only the native executable compilation was slow.

Fix: run both suites **interpreted** off the gate-1 oleans, eliminating native
compilation entirely:

- `gate_demo` -> `lake env lean --run Main.lean`
- `gate_conformance` -> `lake env lean --run Conformance.lean`

`Conformance` imports only `Henret.Conformance` (already in gate 1). `Main` also
imports `Henret.Examples.Basic`, which the default `import Henret` omits; a new
`HenretExamples` lean_lib (globbing `Henret.Examples`) is added so gate 1 builds
that olean without the executable. Every scenario still runs and asserts
(non-zero exit on failure) — the demos are reference artifacts, not shipped
binaries, so only the incidental native-compile step is dropped. The swapfile and
`timeout-minutes` from earlier iterations are kept as harmless defensive headroom.

### 2. Tag trigger never fired

`on.push.tags` filtered `["v*"]`, but the release tags are bare-numeric
(`0.34.3`). `0.34.3` doesn't match `v*`, so tag pushes never triggered the
authoritative release/publish path — the run you saw came from the push to
`main`. Filter is now `["[0-9]*.[0-9]*.[0-9]*"]`.

### 3. The sidecar was never attached to the release

The old "Upload release evidence" step used `actions/upload-artifact`, which
attaches to the *workflow run* (auth-gated, ~90-day expiry) — not to the GitHub
Release. And nothing built/attached the canonical tarball. That is exactly why
iotakt found no sidecar. A new **tag-gated** step now uploads the canonical
tarball + `release-verification.json` + `GATE-RUN.md` to the Release via
`gh release upload`, so the RFC 095 sidecar is fetchable beside the tarball.

## Filename convention (resolves RFC 095 open question)

Per your decision: **published GitHub assets are no-`v`**
(`henret-X.Y.Z.tar.gz`, `henret-X.Y.Z.release-verification.json`,
`henret-X.Y.Z.GATE-RUN.md`); **local/dev tarballs keep the `v`-prefix**.
`check.sh` gained a `HENRET_PUBLISH_NAME=1` toggle (set by CI) that names the
tarball no-`v`, so the manifest's `source_archive.name` records the exact
published asset name. Docs (integration-contract §11, release-checklist,
release-manifest-schema) now show the no-`v` consumer recipe; RFC 095's filename
open question is marked resolved.

## Honest caveat — what I could and couldn't verify

Validated here: `ci.yml` is valid YAML; `check.sh` parses (`bash -n`); the
no-`v`/`v` naming toggle produces the right tarball name in both states; `--fast`
and the docs gate are green.

**Not validated here:** that gate 2 now fits in memory. I cannot run Actions, and
I cannot run `check.sh --release` in this sandbox (the same demo compile exceeds
the budget). Only a CI run on the new workflow can confirm the swap
fix clears gate 2. (Update: the first CI run confirmed swap clears gate 1's full
build; gate 2 then failed only on an invalid `lake -j` flag, now removed.)

## For iotakt (once 0.34.4 CI is green)

Push the `0.34.4` tag; CI will publish
`…/releases/download/0.34.4/henret-0.34.4.release-verification.json` (sidecar,
no-`v`) beside the tarball, with `git_commit` bound. iotakt then fetches it
first-hand, confirms `git_commit`, and derives the two hashes — exactly their
ask.

One coordination point: **0.34.3 still has no sidecar**, and iotakt currently
pins henret at the 0.34.3 commit. Either republish 0.34.3's assets through the
new flow (run `--release` at that commit and `gh release upload`), or have iotakt
move their pin to 0.34.4 once it lands with a proper sidecar. Your call.
