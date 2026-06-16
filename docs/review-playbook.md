# External Review Playbook

A checklist for an external reviewer auditing Henret. It is organized so a
reviewer can falsify the assurance case quickly: each item is a question
whose "no" answer is a finding. Pair it with
[`docs/assurance-case.md`](assurance-case.md).

## Claim integrity

- Does any public claim (README, docstring, release note) exceed what its
  named theorem actually states?
- Is every top-level claim (C1–C10) in the assurance case backed by a
  theorem name, a file path, and an explicit axiom set?
- Are kernel-proven, trusted, and tested claims kept separate — never
  presented as interchangeable?
- Does the proof/trust/test matrix classify every user-facing correctness
  claim, with none silently upgraded from TESTED/ASSUMED to PROVEN?

## Axiom budget

- Does any theorem reachable from `import Henret` depend on a
  project-specific axiom? (It must not.)
- Does the axiom audit allowlist contain every headline theorem, and only
  the expected `propext` / `Classical.choice` / `Quot.sound`?
- Are the native FFI axioms confined to `import Henret.Native.*` (opt-in),
  and documented in the assumption index?

## Bridge honesty

- Is every bridge claim qualified **single-worker** wherever completeness
  is implied (RFC 052 bridge-claim rule)?
- Are bridge exclusions (multi-worker, wake-placement policy) described in
  the *same* place as the bridge claims, not hidden elsewhere?
- Does `toQOps` stay validity-aware for the operations it claims to cover?

## Grammar and migration

- Does every change to `RuntimeOp` / `RuntimeState` / `StepResult` /
  `TaskState` have a migration note under `docs/migration/`?
- Did the change answer the Semantic Impact Checklist
  (`docs/semantic-extension-governance.md`)?
- Are exhaustive `match`/`cases` sites over the changed types all updated
  (the compiler enforces this, but examples and renderers are easy to
  miss — see the RFC 051 `showState` finding)?

## Packaging and examples

- Are examples (`examples/NN_*.lean`) standalone and never pulled into
  `import Henret`?
- Do the import tiers (`Henret.Model` / `.Proofs` / `.Refinement` /
  `.Bridge` / `.Trace` / `Henret`) build independently?
- Does the archive exclude `.lake/` and unpack to the root with no
  intermediate parent directory?

## Semantics-specific

- Do docs distinguish the *blocked-as-no-op* result from *waiting-state
  parking* semantics where the distinction matters (Mesa wake)?
- Is the `failed` vs `cancelled` distinction (RFC 049) preserved wherever
  terminal states are discussed?
- Are conditional claims (e.g. progress under bounded fairness) never
  stated as unconditional?

## Process

- Does `scripts/check.sh` run green end-to-end (modulo the documented
  demo-codegen memory cost on constrained runners)?
- Is the release sign-off template
  ([`assurance-case.md` §10](assurance-case.md)) completed for the
  release under review?
- Is the risk register reviewed and current?
