# CI supply-chain policy

RFC 104 makes CI executable inputs reviewable source. The authoritative file
is `ci/supply-chain.json`:

- GitHub Actions are identified by full commit SHA. Workflow comments retain
  the human-readable major version.
- Lean v4.15.0 and mdBook use versioned GitHub release URLs and SHA-256
  digests. The older Lean release predates GitHub's asset-digest metadata, so
  its retained digest was independently computed from the official versioned
  asset. Release workflows invoke this verified Lean distribution directly
  and do not permit elan to fetch a second-stage toolchain.
- `scripts/install_ci_tool.py` verifies the downloaded archive before any
  extraction or execution and rejects traversal, links/special files,
  normalized-path aliases/duplicates, and unsupported archive types.
- Every complete `.yml`/`.yaml` workflow is raw-byte SHA-256 pinned in policy.
  This byte allowlist is the primary control: any workflow command, syntax, or
  line-ending change requires a matching reviewed policy change.
- `scripts/ci_supply_chain.py` additionally interprets canonical, quoted, and
  spaced-colon `uses` keys; rejects movable/unregistered actions; and enforces
  approved acquisition entrypoints. Workflows may call only their registered
  repository Python scripts. `gh` is restricted to Henret's own
  create/upload/post-upload-download routes in `ci.yml`, with every command
  explicitly bound to the literal `nabbisen/henret` repository.
  `GH_REPO`/`GH_HOST`, `GITHUB_REPOSITORY` reassignment, external repository
  selectors, prefixed/unparsed `gh`, interpreter snippets, and direct HTTP
  clients are rejected.
  Exact per-workflow installer calls, Lean selector agreement, and canonical
  package metadata are also required. The `ci.yml` contract additionally binds
  the exact main/release-tag push triggers, an active non-error-tolerant `gate`
  job, and a project-owned per-object guard immediately before one pinned
  `actions/upload-artifact` step. The guard and upload have the exact all-push
  condition and no error suppression. The guard requires exactly one canonical
  `release/henret-*.tar.gz`, regular nonempty manifest and summary files, and
  every expected gate log; the action's `if-no-files-found: error` remains
  defense in depth for the exact retained path set.

The monthly/manual `supply-chain-refresh` workflow compares action and mdBook
pins with upstream refs and confirms the repository-locked Lean release still
exists. A newer Lean compiler is a language/toolchain migration, not an
automatic supply-chain refresh. The workflow does not edit source, update a
release, or fall back to a movable version. A reported update is handled as a
normal reviewed change:

1. inspect the official upstream release and changelog;
2. update every corresponding workflow literal and its exact
   `workflow_sha256` entry in `ci/supply-chain.json`;
3. obtain tool digests from official GitHub release metadata and independently
   hash downloaded test bytes when practical;
4. run `python3 scripts/ci_supply_chain.py --self-test`, the fast gate, and the
   documentation gate; and
5. review the source diff before merge.

If an upstream asset disappears or its bytes do not match policy, CI fails
before extraction. Do not substitute `latest`, skip verification, or silently
replace the digest. Treat unexpected digest drift as an incident: retain the
failure evidence, stop publication, and investigate upstream provenance.

Release manifests retain the complete policy and its policy-file hash. This
records what the run trusted; checksum pinning does not prove that upstream
bytes themselves are trustworthy.

## Hosted runner trust boundary

The checksum policy does not make the full GitHub-hosted environment immutable.
The trusted substrate still includes the selected runner image, Linux kernel,
shell/coreutils, Python, Git, TLS roots, GitHub Actions service, artifact
service, and the runner-provided `gh` publication client. Current manifests
therefore retain repository/run/ref/workflow identity, runner environment,
architecture, and image OS/version. The v4 verifier requires GitHub-hosted
provenance and rejects local prechecks, but these fields identify rather than
cryptographically reproduce that base TCB. Unexpected runner-image or `gh`
changes must be evaluated as release-environment changes before publication.

## Write-control trust anchor

Every control above — checksum pinning, the byte-allowlisted workflow, the
per-object retained-evidence guard, the hosted-provenance fields — governs
what a hosted run does once it starts. None of it governs who can start one
on `main` or push a release tag. The publication channel's integrity
therefore reduces one level further than the runner substrate: to enforced
**repository write control** over `nabbisen/henret` — who may push to `main`
and who may create tags. This project does not treat that as solved by CI
configuration; it is a repository-hosting control (branch and tag
protection, required reviews) outside `ci.yml`, `ci/supply-chain.json`, and
this document.

As with the C-concurrency trust boundary (R3 in
[the risk register](../risk-register.md)), this is a named, accepted trust
boundary rather than a gap the checksum policy silently papers over: hosted
`hosted_ci.*` fields are **unsigned run-identity assertions**, not
cryptographic attestations of build provenance. A compromised or
unprotected write path to `main`/tags would let an attacker's commit acquire
the same `workflow_ref`/`workflow_sha` shape as a legitimate one. Whether
branch/tag protection with required reviews is configured, and whether a
durable fix (cryptographic build provenance, e.g. GitHub artifact
attestations or Sigstore) is scheduled, are decisions for the human owner —
see R9 in the risk register.
