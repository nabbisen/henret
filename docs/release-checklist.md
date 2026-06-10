# Release Checklist

Every item must pass before an archive is cut. The mechanical gates are
bundled into a single command:

```bash
bash scripts/check.sh
```

which runs the build, the demo, all examples, the conformance suite, the
strict axiom audit, the stale-phrase gate, and the doc-symbol checker. The
remaining items are reviewed by hand.

## Automated gates (`scripts/check.sh`)

- [ ] `lake build` — the Lean-only core and all proofs compile
      (kernel-checked).
- [ ] `lake build HenretNative` — the optional native-boundary layer
      compiles.
- [ ] `lake build HenretExplore` — the optional bounded model checker
      compiles.
- [ ] `lake exe henret-demo` — the demo's regression scenarios pass and
      it exits zero.
- [ ] every `examples/NN_*.lean` compiles.
- [ ] `lake exe henret-conformance` — all golden-trace scenarios pass
      (RFC 047).
- [ ] strict axiom audit — every headline theorem depends only on
      `propext`, `Classical.choice`, `Quot.sound` (no project axioms in
      `import Henret`).
- [ ] stale-phrase gate — no superseded doc phrases remain.
- [ ] doc-symbol checker — every backticked theorem name in the docs
      resolves.

## Manual review

- [ ] zero `sorry` anywhere in `Henret/`.
- [ ] `docs/proof-trust-test-matrix.md` updated with the release's new
      claims, each classified.
- [ ] `docs/proof-index.md` updated with new public theorems and their
      file locations.
- [ ] `CHANGELOG.md` updated (descending order; semantics vs docs/tooling
      separated; axiom-budget impact stated).
- [ ] migration note added under `docs/migration/` if the grammar
      (`RuntimeOp` / `RuntimeState` / `StepResult` / `TaskState`) changed.
- [ ] the implemented RFC moved from `rfcs/proposed/` to `rfcs/done/`
      with its `Status` field updated to `Implemented (vX.Y.Z)`, and the
      `rfcs/README.md` row updated.
- [ ] new headline theorems added to the `scripts/axiom_audit.py`
      allowlist; new doc-referenced names added to the
      `scripts/doc_symbol_check.py` IGNORE set as appropriate.

## Archive hygiene

- [ ] the archive excludes `.lake/` and any generated build output.
- [ ] the archive unpacks to the extraction root with no intermediate
      parent directory (layout inside the tar is the project files
      directly).
- [ ] the version number is appended to the archive name
      (`henret-vX.Y.Z.tar.gz`).

```bash
tar --exclude='./.lake' -czf henret-vX.Y.Z.tar.gz \
    --transform 's|^\./||' -C <project-root> .
```

## Note on the demo executable

`lake build` includes C code generation for the `henret-demo`
executable, which is memory-intensive. On constrained CI runners this
step can be the bottleneck; the *library* proofs (`lake build Henret`)
and the conformance executable (`lake exe henret-conformance`) are far
lighter and verify the proof corpus and golden traces independently of
the demo's codegen. The demo's correctness is exercised by its own
regression scenarios when it does run; its build is not a proof gate.

