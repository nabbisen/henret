# Release Checklist

Every item must pass before an archive is cut. The mechanical gates are
bundled into a single command:

```bash
bash scripts/check.sh --fast          # local developer pre-check
bash scripts/check.sh --release-core  # all required gates + hashed manifest
bash scripts/check_docs.sh            # standalone documentation pre-check
```

`--fast` runs the gate-suite self-test, build, examples, doc-symbol, axiom
audit, doc-consistency, RFC-metadata, and warning gates. `--release-core`
additionally requires bounded interpreted demo, exhaustive conformance, the
bounded explorer, and `check_docs.sh`, then emits `release/release-verification.json` (a
hashed, non-manual evidence manifest) plus `release/GATE-RUN.md`. Per RFC 080,
authoritative release evidence comes from **CI** running `--release-core` on the
exact release commit/tag; a local `--release-core` is a pre-check only. The
remaining items are reviewed by hand. The documentation gate `scripts/check_docs.sh`
(mdBook build + SUMMARY-orphan + local-link checks, RFC 094) is not part of
`--fast`, but is required inside `--release-core` at the same commit. The book
targets the mdBook 0.5 line;
`.github/workflows/docs.yml` installs the checksum-pinned mdBook release from
`ci/supply-chain.json`, and
`check_docs.sh` reports the detected version.

## Automated gates (`scripts/check.sh`)

- [ ] `lake build` — the Lean-only core and all proofs compile
      (kernel-checked).
- [ ] `lake build HenretNative` — the optional native-boundary layer
      compiles.
- [ ] `lake build HenretExplore` — the optional bounded model checker
      compiles.
- [ ] interpreted `lake env lean --run Main.lean` — the demo's regression
      scenarios pass and the command exits zero (`lake exe henret-demo` is
      standalone).
- [ ] every `examples/NN_*.lean` compiles.
- [ ] interpreted `lake env lean --run Conformance.lean` — all golden-trace
      scenarios pass (RFC 047; `lake exe henret-conformance` is standalone).
- [ ] bounded interpreted `lake env lean --run Explore.lean` — its executed
      machine result supplies the world/depth and outcomes; result, duration,
      and output hash are retained under semantic gate
      `test.explorer`; this is TESTED evidence, not proof.
- [ ] strict axiom audit — every headline theorem depends only on
      `propext`, `Classical.choice`, `Quot.sound` (no project axioms in
      `import Henret`).
- [ ] stale-phrase gate — no superseded doc phrases remain.
- [ ] doc-symbol checker — every backticked theorem name in the docs
      resolves.
- [ ] `scripts/check_docs.sh` green — mdBook builds, every `docs/src` page is
      reachable from `SUMMARY.md`, and every local Markdown link resolves
      (RFC 094; run separately, not in `check.sh --fast`).

## Manual review

- [ ] zero `sorry` anywhere in `Henret/`.
- [ ] `docs/src/proof-trust-test-matrix.md` updated with the release's new
      claims, each classified.
- [ ] `docs/src/proof-index.md` updated with new public theorems and their
      file locations.
- [ ] `CHANGELOG.md` updated (descending order; semantics vs docs/tooling
      separated; axiom-budget impact stated).
- [ ] migration note added under `docs/src/migration/` if the grammar
      (`RuntimeOp` / `RuntimeState` / `StepResult` / `TaskState`) changed.
- [ ] the implemented RFC moved from `rfcs/proposed/` to `rfcs/done/`
      with its `Status` field updated to `Implemented (vX.Y.Z)`, and the
      two RFC indexes regenerated with `scripts/extract_rfc_index.py`.
- [ ] new headline theorems added to the `scripts/axiom_audit.py`
      allowlist; new doc-referenced names added to the
      `scripts/doc_symbol_check.py` IGNORE set as appropriate.
- [ ] assurance case (`docs/assurance-case.md`) C-table updated if a
      top-level claim was added; risk register reviewed and any new
      residual risk recorded; release sign-off template completed.

## Archive hygiene

- [ ] the archive contains exactly the Git-tracked entries at the candidate
      commit; ignored and untracked local material is absent.
- [ ] the archive unpacks to the extraction root with no intermediate
      parent directory (layout inside the tar is the project files
      directly).
- [ ] the version number is appended to the archive name
      (`henret-vX.Y.Z.tar.gz`).

```bash
python3 scripts/source_archive.py henret-vX.Y.Z.tar.gz --commit HEAD
python3 scripts/source_archive.py --check henret-vX.Y.Z.tar.gz --commit HEAD
```

The builder uses `git archive` with repository-independent `tar.umask=0022`,
validates every member and its Git-derived mode, rejects internal paths and
gitlinks/submodules, and requires two builds to be byte-identical.

## Release profiles (RFC 102 / RFC 103)

- [ ] the published sidecar is produced by **`check.sh --release-core`** in CI
      (the `release-core-v3` profile): gates 0–11, canonical tarball, and
      manifest. Demo, conformance, explorer, and mdBook are required; executable
      timeouts are failures. Publish only when `required_gates_passed: true`.
- [ ] the manifest names `gate_registry: rfc103-release-core-v3` and contains
      one passing `required` record for every gate ID 0–11, with the registered
      semantic `evidence_id` on each record.

## Publishing & provenance (RFC 095)

- [ ] publication preflight proves the version has no existing GitHub Release;
      release creation and canonical asset upload then run without overwrite
      authorization. Any rerun or partial prior publication fails closed.
- [ ] an invalid published version is never repaired in place: record the
      incident, cut a new patch version, and notify pinned consumers.

- [x] **Post-upload verification is automated** — the release-gate workflow
      re-downloads the published tarball + sidecar + GATE-RUN and runs
      `verify_release_manifest.py` against them. A failure means the release is
      invalid even if the pre-upload artifacts were correct (retract/patch).

- [ ] the **published** tarball is the canonical reproducible archive built by
      `check.sh --release` (sorted, fixed mtime/owner, full exclude set) — the
      one whose hash `release-verification.json` records. Do not publish an
      ad-hoc repackaging; its hash will not match the manifest.
- [ ] `release-verification.json` and `GATE-RUN.md` are published **beside** the
      tarball on the release page (consumer-fetchable, RFC 095 §D2), with
      no-`v` version-prefixed names (`henret-X.Y.Z.tar.gz`,
      `henret-X.Y.Z.release-verification.json`, `henret-X.Y.Z.GATE-RUN.md`).
      CI builds these by running the release gate with
      `HENRET_PUBLISH_NAME=1`; local/dev tarballs keep the `v`-prefix.
- [ ] **post-upload verification (RFC 095 §3.1):** after publishing, re-download
      the published tarball and manifest from the release page and confirm they
      match — catching "CI built the right file but the wrong one was uploaded":

```bash
python3 scripts/verify_release_manifest.py --require-current \
    henret-X.Y.Z.release-verification.json henret-X.Y.Z.tar.gz henret-X.Y.Z.GATE-RUN.md
# exits 0 only if tarball sha256, source_archive, GATE-RUN.md hash, and all gates match
```

## Note on the demo executable

`lake build` includes C code generation for the `henret-demo`
executable, which is memory-intensive. On constrained CI runners this
step can be the bottleneck; the *library* proofs (`lake build Henret`)
and the conformance executable (`lake exe henret-conformance`) are far
lighter and verify the proof corpus and golden traces independently of
the demo's codegen. The demo's correctness is exercised by its own
regression scenarios when it does run; its build is not a proof gate.
