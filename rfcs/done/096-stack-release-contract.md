---
rfc: 96
title: Stack Release Contract
status: Implemented
implemented_in: v0.34.3
supersedes: []
superseded_by: []
depends_on: [80, 81, 95]
blocks: []
category: integration
---

# RFC 096 — Stack Release Contract

## Status

Implemented in v0.34.3. Approved with minor amendments across two review rounds;
all amendments (§4.1–4.6 and the §5 acceptance additions of the updated review)
are folded in below. Raised by the jemmet team: align the henret → iotakt →
jemmet stack to the RFC 080 manifest schema instead of a parallel format.

## Summary

Reuse the RFC 080 `release-verification.json` schema (implemented, published per
RFC 095) as the **per-package** provenance contract, and add a thin **stack
manifest** that composes per-package manifests *and pins the dependency edges
between them*. henret, iotakt, and jemmet each publish a conforming package
manifest; the top consumer (jemmet) publishes a `stack-release.json` whose
`dependency_edges` are checked against each package's own declared
`dependencies`. No parallel format; the closed `tier` vocabulary and
TRUSTED/TESTED distinction (RFC 080/081) carry up unchanged.

The normative schema lives in `docs/src/release-manifest-schema.md`; a minimal
local-file verifier ships as `scripts/verify_stack_release.py`.

## Motivation

jemmet found henret's RFC 080 manifest and RFC 081 evidence ledger *more* mature
than the parallel format jemmet had begun, and asked to standardize on them. A
layered stack needs more than per-package integrity: it must prove *which* henret
release iotakt built against and *which* iotakt jemmet built against, with each
edge anchored by hash — otherwise a stack manifest is only a bundle list, not a
release contract.

## Design

### D1 — Schema-field compatibility

Per-package manifests **keep** RFC 080's `manifest_schema: 1` (no rename). The
stack manifest uses a **distinct** field, `stack_manifest_schema: 1`, so package
and stack schemas version independently and the implemented RFC 080 manifest is
unchanged.

### D2 — Per-package manifest is the RFC 080 manifest (published, RFC 095)

Each package publishes its own `release-verification.json` per RFC 095.
Trust-inventory fields (the closed `tier` vocabulary, TRUSTED/TESTED,
`verified_by_this_tarball`) originate in **RFC 081**. They are **optional** per
package: a conforming manifest *may* include them, and *if present* they MUST
follow RFC 081. Stack verification does **not** require henret to validate
downstream trust inventories; it checks manifest and artifact hashes plus
declared dependency edges only (review §4.6).

### D3 — Per-package dependency declarations

A consumer package's manifest declares what it built against, by hash:

```json
"dependencies": [
  { "package": "henret", "version": "0.34.2",
    "manifest_sha256": "…", "tarball_sha256": "…",
    "surface": "task/runtime model API" }
]
```

(iotakt declares henret; jemmet declares iotakt.) This is the ground truth a
stack manifest is checked against.

### D4 — Stack manifest composes by reference *and* edge

```json
{
  "stack_manifest_schema": 1,
  "stack": "jemmet",
  "stack_version": "x.y.z",
  "packages": [
    { "package": "henret", "version": "0.34.2",
      "tarball_sha256": "…", "manifest_sha256": "…",
      "manifest_url": "…", "manifest_urls": ["…", "…mirror…"] },
    { "package": "iotakt", "version": "…", "tarball_sha256": "…",
      "manifest_sha256": "…", "manifest_url": "…" },
    { "package": "jemmet", "version": "x.y.z", "tarball_sha256": "…",
      "manifest_sha256": "…", "manifest_url": "…" }
  ],
  "dependency_edges": [
    { "consumer": "iotakt", "provider": "henret", "provider_version": "0.34.2",
      "provider_manifest_sha256": "…", "surface": "task/runtime model API",
      "declared_by": "iotakt release manifest" }
  ]
}
```

Resolution and uniqueness rules (review §4.2, §4.4):

- `packages[].package` values MUST be unique within a stack manifest.
- Each edge's `consumer` and `provider` MUST each resolve to **exactly one**
  `packages` entry. The consumer manifest used to check declared dependencies is
  the one identified by that consumer entry's `manifest_sha256` (so no separate
  `consumer_manifest_sha256` field is duplicated).
- Edges are identified by `(consumer, provider, surface)`; a consumer dependency
  matches at most one edge unless multiple surfaces are intentionally declared.

Provider hashing (review §4.3): edges pin providers by
`provider_manifest_sha256`. The provider **tarball** hash is *not* duplicated on
the edge — it is obtained from the provider's `packages` entry and verified
against the provider manifest, which itself binds the tarball hash. This avoids
inconsistent duplicate fields.

### D5 — Validation rule + verifier (review §4.1)

A conforming stack is one the verifier can check. `scripts/verify_stack_release.py`
ships with this RFC and, given a `stack-release.json` plus a directory of package
manifests (resolved by hash — D6), checks:

```text
packages:  package names unique; each package.manifest_sha256 resolves to a
           manifest in the dir; manifest.package/version match the entry;
           (optionally) package.tarball_sha256 if a tarball dir is supplied.
edges:     consumer and provider each resolve to exactly one package entry;
           provider_manifest_sha256 == provider entry's manifest_sha256;
           the edge matches a `dependencies` entry in the consumer manifest
           (package, version, manifest_sha256).
```

Non-zero exit on any mismatch. Network fetching is optional; local-file
validation is sufficient for v1.

### D6 — Mirror semantics: hash is identity

`manifest_url` may be a single URL or `manifest_urls` a list of mirrors. The
**hash, not the URL, is the identity**: any mirror whose bytes match
`manifest_sha256` is valid. The verifier resolves manifests by matching
`manifest_sha256` against local files, not by URL.

### D7 — Schema evolution & peer governance

`manifest_schema` / `stack_manifest_schema` bump only on breaking changes;
additive fields do not bump. henret hosts and versions `manifest_schema 1` as the
originating reference implementation; once iotakt and jemmet adopt the schema the
relationship is peer-to-peer — breaking schema changes require coordination across
adopting projects, not a henret-unilateral decision.

### D8 — Exact pins only (review §4.5)

RFC 096 v1 stack manifests pin **exact** releases. Compatibility ranges
("tested-against") belong in consumer documentation or a future
compatibility-matrix RFC; they are not used for stack verification. Exact pins
are what make the release contract auditable.

## Acceptance criteria

- A normative schema description (`docs/src/release-manifest-schema.md`) covers
  `manifest_schema 1` (per-package, from RFC 080/081) and `stack_manifest_schema 1`
  (stack, this RFC).
- Per-package manifests keep `manifest_schema`; the stack manifest uses
  `stack_manifest_schema`. No rename of the RFC 080 field.
- `packages[].package` is unique; every dependency edge resolves to exactly one
  consumer and one provider package entry.
- The verifier resolves the consumer manifest from the consumer package entry and
  checks the edge against that manifest's `dependencies`.
- Edges pin providers by `provider_manifest_sha256`; provider tarball integrity is
  checked through the provider package entry and provider manifest.
- RFC 096 v1 pins exact releases only; compatibility ranges are out of scope.
- `scripts/verify_stack_release.py` ships with the schema (minimal local-file
  validation), exiting non-zero on mismatch.
- Trust-inventory fields are optional per package, cited from RFC 081, not
  redefined; `integration-contract.md` points consumers at the schema doc and
  states henret does not verify downstream packages.

## Open questions

- **Hosting.** Where `stack-release.json` lives (jemmet's release page) and
  whether henret/iotakt manifests are mirrored or referenced upstream by hash.
- **Network-fetching verifier.** Whether a later revision adds URL fetching to
  `verify_stack_release.py` (v1 is local-file only).
- **Schema-doc graduation.** Whether `release-manifest-schema.md` stays in henret
  permanently or graduates to a stack-shared location once peers adopt it (D7).
