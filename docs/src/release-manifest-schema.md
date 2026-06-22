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
per RFC 095. Core fields (RFC 080):

| field | meaning |
|---|---|
| `manifest_schema` | `1` |
| `package` | package name, e.g. `"henret"` |
| `version` | release version |
| `generated_by` | the command that produced it |
| `git_commit`, `git_dirty`, `local_precheck` | source provenance |
| `tarball_sha256` | SHA-256 of the canonical release archive (retained) |
| `source_archive` | `{ name, sha256, size_bytes }` (RFC 095 §3.2) |
| `human_summary` | `{ name, sha256 }` binding `GATE-RUN.md` (RFC 095 §3.3) |
| `lake_manifest_sha256`, `lean_toolchain_sha256` | toolchain pins |
| `os`, `runner` | build environment |
| `gate_policy` | per-gate-script SHA-256 (RFC 080 §2) |
| `gates` | gate records (`id`, `name`, `status`, `duration_ms`, log hashes) |
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

### Verifying a per-package release

`scripts/verify_release_manifest.py <manifest.json> <tarball> [GATE-RUN.md]`
recomputes the tarball SHA-256, compares it to `tarball_sha256` and
`source_archive`, confirms every gate is `pass`, and (when given) checks the
`GATE-RUN.md` hash binding. Non-zero exit on any mismatch.

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
