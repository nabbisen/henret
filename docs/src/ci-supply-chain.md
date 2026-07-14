# CI supply-chain policy

RFC 104 makes CI executable inputs reviewable source. The authoritative file
is `ci/supply-chain.json`:

- GitHub Actions are identified by full commit SHA. Workflow comments retain
  the human-readable major version.
- elan and mdBook use versioned GitHub release URLs and SHA-256 digests from
  the official release metadata.
- `scripts/install_ci_tool.py` verifies the downloaded archive before any
  extraction or execution and rejects path traversal and link members.
- `scripts/ci_supply_chain.py` rejects movable action refs, unregistered
  actions, `latest` downloads, missing digests, workflow/policy disagreement,
  and placeholder package metadata.

The monthly/manual `supply-chain-refresh` workflow only compares pins with
upstream refs. It does not edit source, update a release, or fall back to a
movable version. A reported update is handled as a normal reviewed change:

1. inspect the official upstream release and changelog;
2. update `ci/supply-chain.json` and every corresponding workflow literal;
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
