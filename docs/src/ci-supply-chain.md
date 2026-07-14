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
  package metadata are also required.

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
