# Release manifest schema

Normative description of the two provenance artifacts in the Henret stack
contract: the **per-package manifest** (`manifest_schema 1`, RFC 080/081/095) and
the **stack manifest** (`stack_manifest_schema 1`, RFC 096). The hash, not the
URL, is identity throughout: any copy whose bytes match a declared SHA-256 is the
referenced artifact.

This is the single normative reference for consumers (iotakt, jemmet) adopting
the schema. Henret hosts and versions `manifest_schema 1` as the originating
reference implementation; once peers adopt it, breaking changes are coordinated
across adopting projects (RFC 096 D7).

## Per-package manifest (`manifest_schema 1`)

Produced by `scripts/release_manifest.py`, published beside the release tarball
per RFC 095. Published GitHub release assets use **no-`v`** names —
`henret-X.Y.Z.tar.gz`, `henret-X.Y.Z.release-verification.json`,
`henret-X.Y.Z.GATE-RUN.md` — and `source_archive.name` records that exact
tarball name. (Local/dev tarballs keep a `v`-prefix; identity is the hash, so
the filename is only a fetch convenience — RFC 096 D6.) Core fields (RFC 080):

| field | meaning |
|---|---|
| `manifest_schema` | `1` |
| `release_profile` | gate profile that produced it; current authoritative value is `release-core-v3` (RFC 103) |
| `required_gates_passed` | bool — every required gate passed |
| `package` | package name, e.g. `"henret"` |
| `version` | release version |
| `generated_by` | the command that produced it |
| `git_commit`, `git_dirty`, `local_precheck` | source provenance |
| `tarball_sha256` | SHA-256 of the canonical release archive (retained) |
| `source_archive` | `{ name, sha256, size_bytes }` (RFC 095 §3.2) |
| `human_summary` | `{ name, sha256 }` binding `GATE-RUN.md` (RFC 095 §3.3) |
| `lake_manifest_sha256`, `lean_toolchain_sha256` | toolchain pins |
| `os`, `runner` | build environment |
| `gate_policy` | per-gate-script SHA-256 plus the RFC 104 supply-chain policy hash |
| `supply_chain` | exact GitHub Action commits and downloaded-tool versions, URLs, and SHA-256 digests governed by `ci/supply-chain.json` |
| `gates` | gate records: `id`, stable `evidence_id`, `name`, `status`, `duration_ms`, log hashes, and `criticality`. Under `release-core-v3`, IDs 0–11 must all be present, `required`, and `pass`. |
| `validation_reports` | retained additive field for supplemental diagnostic reports; never substitutes for a required gate |
| `runtime_package` | out-of-tree runtime posture (RFC 081) |

Optional fields:

- **Trust inventory** — RFC 081 evidence-ledger / tier fields are optional per
  package. *If present*, they MUST follow RFC 081. Stack verification does not
  require a consumer to validate another package's trust inventory.
- **`dependencies`** — what this package was built against, declared by hash:

  ```json
  "dependencies": [
    { "package": "henret", "version": "0.34.2",
      "manifest_sha256": "…", "tarball_sha256": "…",
      "surface": "task/runtime model API" }
  ]
  ```

  A consumer package (iotakt declaring henret; jemmet declaring iotakt) carries
  this; a leaf package (henret) omits it.

`manifest_schema` bumps only on breaking changes; new optional fields are
additive and do not bump it. Cryptographic signing is a planned additive field
(RFC 095 follow-up); until then verification is hash-only and trusts the
publication channel.

### Dirty-tree exception invariant (RFC 097, architect review §3)

`git_dirty` reflects modified/added **source**, not generated/tool/cache
residue. The exception that excuses such residue applies **only to untracked**
entries (`git status` code `??`). A tracked modification (M/A/D/R/C/T, staged or
not) stays dirty even if its path resembles an excluded cache/tool path — path
exclusions are safe for untracked artifacts but must never hide tracked source
edits. `git_dirty_paths` lists exactly what counted as dirty.

### Gate registry (RFC 102 / RFC 103)

Gate IDs appear in retained release evidence, so consumers key off
`gate_registry` + `release_profile`, not raw IDs. RFC 102 introduced the
retained `rfc102-release-core-v2` mapping for gates 0–10. RFC 103 adds, rather
than redefines it, with current registry `rfc103-release-core-v3`. Its stable
semantic IDs are the targets used by `docs/evidence-ledger.yaml`:

| id | evidence_id | gate | criticality |
|----|-------------|------|-------------|
| 0 | `gate.selftest` | gate-suite self-test | required |
| 1 | `build.lean` | build libraries (kernel-checks all proofs) | required |
| 2 | `test.demo` | demo regression scenarios (bounded interpreted) | required |
| 3 | `build.examples` | examples compile + eval | required |
| 4 | `test.conformance` | golden conformance suite (bounded interpreted) | required |
| 5 | `docs.symbols` | doc-symbol checker | required |
| 6 | `proof.axiom-audit` | strict axiom audit | required |
| 7 | `docs.consistency` | documentation and evidence-ledger consistency | required |
| 8 | `rfc.metadata` | RFC metadata schema | required |
| 9 | `lint.warning-budget` | linter warning budget | required |
| 10 | `docs.mdbook` | mdBook documentation integrity | required |
| 11 | `test.explorer` | bounded interpreted model explorer | required |

The registry also assigns evidence capabilities. Ledger validation permits
`PROVEN/in_tree_model_proof` only on `kernel-build`,
`TRUSTED/in_tree_model_proof` only on `axiom-audit`, and
`TESTED/in_tree_model_test` only on `executable-test`. Existence of a semantic
ID alone is not sufficient.

Since RFC 097, `check.sh --release` is an alias for `--release-core`; the
manifest's `release_profile` (and `generated_by: scripts/check.sh
--release-core`) is the contract, not the command name (§5).

**`validation_reports` immutability.** The release-core manifest is the
exact CI-generated sidecar for the source archive. It is **not** mutated after
publication to append validation reports. A release-validation run that
finishes later retains a separate workflow artifact
(`henret-X.Y.Z.validation-report.json` + `.validation-GATE-RUN.md`) and never
writes to the frozen release. Its results are diagnostic only; gates 2 and 4
must already have passed in the current release core.

### Release profiles (RFC 102 / RFC 103)

The CI-authoritative, sidecar-publishing profile is `release-core-v3`. It runs
all required gates 0–11 at the exact candidate commit, including bounded
interpreted demo/conformance/explorer and mdBook. The explorer record carries
the canonical world `{maxTask: 2, maxActor: 2, maxMsg: 1, maxTime: 2}` at
depth 3, plus its result, duration, and output hash. Different or shallower
bounds are not authoritative v3 evidence. `explorer_result.py` derives both
`parameters` and `result` from the executed machine-readable line; the
generator and verifier reject missing/false outcomes or disagreement between
executed and recorded parameters. The explorer parser, manifest generator, and
verifier apply the same strict schema: exact object keys, JSON boolean/integer
types without Python-style coercion, and no duplicate object keys at any depth.
`verify_release_manifest.py` rejects a v3 sidecar with the wrong registry or
semantic IDs, an incomplete gate set, any non-passing result, malformed
explorer evidence, a dirty tree, a local-only run, or a non-exact commit.
Legacy `ci-core-v1` and `release-core-v2` manifests retain their historical
interpretations.

### Verifying a per-package release

`scripts/verify_release_manifest.py --require-current <manifest.json> <tarball> [GATE-RUN.md]`
recomputes the tarball SHA-256, compares it to `tarball_sha256` and
`source_archive`, confirms every gate is `pass`, and (when given) checks the
`GATE-RUN.md` hash binding. `--require-current` prevents an older profile from being
accepted where the current authoritative profile is required. For versioned
v2/v3 profiles, the
exact candidate commit must be a full 40-character lowercase hexadecimal SHA-1
object ID; abbreviations and arbitrary labels are rejected. Non-zero exit on
any mismatch.

Unflagged verification accepts only explicitly recognized legacy/current
profiles; unknown profile strings are rejected. The explicit
`--require-current` flag remains mandatory in the authoritative workflow and
current consumer recipe.

## Stack manifest (`stack_manifest_schema 1`)

Produced by the top consumer (jemmet) to compose a release of the whole stack.

```json
{
  "stack_manifest_schema": 1,
  "stack": "jemmet",
  "stack_version": "x.y.z",
  "packages": [
    { "package": "henret", "version": "0.34.2",
      "tarball_sha256": "…", "manifest_sha256": "…",
      "manifest_url": "…", "manifest_urls": ["…", "…mirror…"] }
  ],
  "dependency_edges": [
    { "consumer": "iotakt", "provider": "henret", "provider_version": "0.34.2",
      "provider_manifest_sha256": "…", "surface": "task/runtime model API",
      "declared_by": "iotakt release manifest" }
  ]
}
```

### Rules

- `packages[].package` MUST be unique within a stack manifest.
- Each package entry pins a constituent by **both** `tarball_sha256` and
  `manifest_sha256`. `manifest_url` (or `manifest_urls`) gives locations; the
  hash is identity.
- Each edge's `consumer` and `provider` MUST each resolve to **exactly one**
  package entry. The consumer manifest used to check the edge is the one
  identified by that consumer entry's `manifest_sha256` (no duplicate
  `consumer_manifest_sha256` field).
- An edge pins its provider by `provider_manifest_sha256`, which MUST equal the
  provider package entry's `manifest_sha256`. The provider **tarball** hash is
  *not* duplicated on the edge — it is taken from the provider package entry and
  verified against the provider manifest.
- Each edge MUST match a `dependencies` entry in the resolved consumer manifest
  (same `package`, `version`, `manifest_sha256`).
- Edges are identified by `(consumer, provider, surface)`; a consumer dependency
  matches at most one edge unless multiple surfaces are intentionally declared.
- **Exact pins only.** v1 pins exact releases; compatibility ranges are out of
  scope (consumer docs / a future compatibility-matrix RFC).

### Verifying a stack release

`scripts/verify_stack_release.py <stack-release.json> <manifest-dir> [tarball-dir]`
resolves each package's manifest by matching `manifest_sha256` against the files
in `manifest-dir` (hash-is-identity), checks name/version, optionally checks
`tarball_sha256` against files in `tarball-dir`, then for each edge checks
provider/consumer resolution, `provider_manifest_sha256`, and that the edge
matches the consumer manifest's `dependencies`. Non-zero exit on any mismatch.

## What this contract does and does not protect

It protects against: a stack manifest that is a mere bundle list; untracked
dependency substitution; a mismatch between a claimed stack edge and the
consumer's actual build input; schema drift from RFC 080; URL-based mirror
ambiguity.

It does **not** protect against: compromise of all referenced release channels;
a malicious release from a compromised package project; false gate evidence from
a compromised CI; or cryptographic substitution where both an artifact and its
unsigned manifest are replaced. Those are accepted non-goals pending the RFC 095
signing follow-up.
