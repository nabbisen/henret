---
rfc: 96
title: Stack Release Contract
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [80, 81, 95]
blocks: []
category: integration
---

# RFC 096 — Stack Release Contract

## Status

Proposed — **revised per architect review, awaiting re-approval before
implementation**. The review accepted the direction but required the stack
manifest to become a dependency-*graph* contract, not a flat package list, and
to stay schema-compatible with the already-implemented RFC 080 manifest. This
revision folds in all seven amendments (§4.1–4.7 of the review). Raised by the
jemmet team: align the henret → iotakt → jemmet stack to the RFC 080 manifest
schema instead of a parallel format.

## Summary

Reuse the RFC 080 `release-verification.json` schema (already implemented, and
published per RFC 095) as the **per-package** provenance contract across the
stack, and add a thin **stack manifest** that composes per-package manifests
*and pins the dependency edges between them*. henret, iotakt, and jemmet each
publish a conforming package manifest; the top consumer (jemmet) publishes a
`stack-release.json` whose `dependency_edges` are checked against each
package's own declared dependencies. No parallel format; the closed `tier`
vocabulary and TRUSTED/TESTED distinction (RFC 080/081) carry up unchanged.

## Motivation

jemmet found henret's RFC 080 manifest and RFC 081 evidence ledger *more* mature
than the parallel format jemmet had begun, and asked to standardize on them. A
layered stack needs more than per-package integrity: it must prove *which* henret
release iotakt built against and *which* iotakt jemmet built against, with each
edge anchored by hash — otherwise a stack manifest is only a bundle list, not a
release contract (review §6).

## Design

### D1 — Schema-field compatibility (review §4.1)

The RFC 080 manifest already carries `manifest_schema: 1`. Per-package manifests
**keep that field name** — this RFC does not rename it. The stack manifest uses a
**distinct** field, `stack_manifest_schema: 1`, so the per-package and stack
schemas version independently and the implemented RFC 080 manifest is not
silently changed.

### D2 — Per-package manifest is the RFC 080 manifest (published, RFC 095)

Each package publishes its own `release-verification.json` per RFC 095:
`manifest_schema`, `package`, `version`, `tarball_sha256` / `source_archive`, the
gate records, and (where applicable) `runtime_package`. Trust-inventory fields
(the closed `tier` vocabulary, TRUSTED/TESTED, `verified_by_this_tarball`)
originate in **RFC 081**; this RFC depends on RFC 081 and cites that shape rather
than redefining it (review §4.5). No package verifies another's internals.

### D3 — Per-package dependency declarations (review §4.3)

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

### D4 — Stack manifest composes by reference *and* edge (review §4.2)

The top consumer publishes `stack-release.json`:

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
      "declared_by": "iotakt release manifest" },
    { "consumer": "jemmet", "provider": "iotakt", "provider_version": "…",
      "provider_manifest_sha256": "…", "surface": "IotaktLoopOps byte-level API",
      "declared_by": "jemmet release manifest" }
  ]
}
```

Each package entry pins a constituent by *both* tarball hash and manifest hash;
each edge pins the provider by `provider_manifest_sha256`.

### D5 — Validation rule + tool (review §4.4)

A conforming stack is one a verifier can check. The contract is designed for a
`scripts/verify_stack_release.py` (implementation a named follow-up if not
shipped with the schema doc) that, for each package, checks `manifest_sha256` and
`tarball_sha256`; and for each edge, checks that the provider appears in
`packages`, that `provider_manifest_sha256` matches the provider's published
manifest, and that the edge **matches the consumer manifest's own `dependencies`
declaration** (D3). Without that cross-check a stack could claim iotakt uses one
henret release while iotakt's manifest was produced against another (review §4.3).

### D6 — Mirror semantics: hash is identity (review §4.7)

`manifest_url` may be a single URL or `manifest_urls` a list of mirrors. The
**hash, not the URL, is the identity**: any mirror whose bytes match
`manifest_sha256` is valid; URLs are locations.

### D7 — Schema evolution & peer governance (review §4.6)

`manifest_schema` / `stack_manifest_schema` bump only on breaking changes;
additive fields do not bump. henret **hosts and versions** `manifest_schema 1`
as the originating reference implementation. Once iotakt and jemmet adopt the
schema the relationship is peer-to-peer: breaking schema changes require
coordination across adopting projects, not a henret-unilateral decision.

## Acceptance criteria

- A normative schema description is published under `docs/src/` (e.g.
  `release-manifest-schema.md`) covering `manifest_schema 1` (per-package, from
  RFC 080/081) and `stack_manifest_schema 1` (stack, this RFC).
- Per-package manifests keep `manifest_schema`; the stack manifest uses
  `stack_manifest_schema`. No rename of the RFC 080 field.
- The stack manifest carries `dependency_edges`; consumer manifests carry
  `dependencies`; the validation rule (D5) cross-checks them.
- `scripts/verify_stack_release.py` exists, or is named as an explicit follow-up
  RFC; the schema is designed so it can be validated mechanically.
- Trust-inventory fields are cited from RFC 081, not redefined here.
- `integration-contract.md` points consumers at the schema doc and states that
  henret does not verify downstream packages.
- Mirror semantics (hash is identity) are documented; no parallel stack format is
  introduced.

## Open questions

- **Hosting.** Where `stack-release.json` lives (jemmet's release page) and
  whether henret/iotakt manifests are mirrored or referenced upstream by hash.
- **Version-compatibility range.** Whether an edge should also carry a declared
  "tested-against" range, or leave that to each consumer's docs.
- **verify_stack_release.py home.** Whether it ships in henret (schema owner) or
  in the top consumer that assembles the stack manifest.
- **Schema-doc graduation.** Whether `release-manifest-schema.md` stays in henret
  permanently or graduates to a stack-shared location once peers adopt it (D7).
