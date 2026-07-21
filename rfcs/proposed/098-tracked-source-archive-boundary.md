---
rfc: 98
title: Tracked Source Archive Boundary
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [80, 95]
blocks: [102]
category: release-process
---

# RFC 098 — Tracked Source Archive Boundary

## Status

Proposed. Release-blocking for the v0.34.6 integrity milestone.

## Summary

Construct the canonical source archive from an explicit Git-tracked allowlist
instead of archiving the working directory with a growing exclude list. Add a
machine-checked archive-content contract so ignored, untracked, or internal
local material cannot enter a release artifact. Accidentally tracked sensitive
content requires a separate tracked-content policy and is not prevented by the
archive boundary alone.

## Motivation

The current release command archives `.`. Ignored paths are invisible to the
ordinary dirty-tree check, and the current selection includes `.git-exclude/`
when that local directory exists. A provenance manifest cannot repair an
incorrect archive boundary after the fact.

## Non-goals

- Do not change model semantics or public Lean APIs.
- Do not add ignored build output to the release.
- Do not rely on an expanded denylist as the primary boundary.

## Proposed design

1. Define the release input as Git-tracked files plus a short, explicit list of
   generated release records created after the source archive.
2. Read the ordered path, blob, mode, symlink, and commit-time inputs from Git
   objects, but serialize tar and gzip bytes in project-owned code. Emit only
   the specified ustar header form and stored-block DEFLATE form, with fixed
   path order, timestamp, numeric owner/group, modes, headers, padding, end
   markers, CRC-32, and ISIZE. Reject values outside that format and reject
   gitlinks/submodules until an explicit recursive source policy exists.
3. Add an archive policy checker that validates:
   - every source entry is tracked and expected;
   - no `.git`, `.git-exclude`, cache, build, or release-output entry exists;
   - paths extract directly at the destination root;
   - no unexpected top-level path exists;
   - regular, executable, directory, and symlink modes match the Git tree;
   - a second build from the same commit produces the same SHA-256; and
   - the supplied archive is byte-for-byte equal to the project-owned canonical
     reconstruction, so alternate valid tar/gzip encodings are rejected.
4. Record the archive policy/checker hash in the release manifest.
5. Keep the dirty-tree rejection as a separate guarantee: tracked modifications
   still prevent an authoritative release even though the archive is selected
   from tracked paths.

### Canonical byte format

All Git object reads use `--no-replace-objects`; repository-local replacement
refs are not release inputs. Paths are sorted by their UTF-8 bytes. Long ustar
paths split at the rightmost slash whose prefix is at most 155 bytes and name
is at most 100 bytes. Symlink targets are UTF-8 and at most 100 bytes.

Each 512-byte ustar header uses name at bytes 0–99; NUL-terminated octal mode,
uid, gid, size, and commit timestamp at 100–147; six-octal-digit checksum plus
NUL and space at 148–155; type flag and link name at 156–256; `ustar\0` / `00`
at 257–264; empty owner/group names; zero device numbers; and the optional
prefix at 345–499. Regular data is zero-padded to 512 bytes. Directories and
symlinks have no data payload. Two zero blocks terminate the stream.

The gzip stream is the fixed ten-byte header
`1f8b08000000000000ff`, followed by raw DEFLATE stored blocks of at most 65,535
bytes. Every block carries little-endian LEN and one's-complement NLEN; only the
last block has BFINAL set. The trailer is little-endian CRC-32 and input size
modulo 2^32. No Git tar serializer, zlib compressor, locale, timezone, process
umask, or ambient Git configuration defines canonical bytes.

## Implementation tasks

1. Extract archive construction and validation into testable scripts.
2. Replace the `tar -C . .` selection in `scripts/check.sh`.
3. Add positive and negative self-tests, including an ignored
   `.git-exclude/sentinel` fixture.
4. Update the release checklist, manifest schema, and archive-hygiene docs.
5. Add the new scripts to `gate_policy` hashing.

## Acceptance criteria

- An ignored or untracked sentinel never appears in the archive.
- Every archive source entry maps to a Git-tracked path at the release commit.
- The archive has no intermediate parent directory and no unexpected top-level
  path.
- Rebuilding from the same commit is byte-reproducible.
- Golden tar/gzip vectors and conflicting locale, timezone, umask, and Git
  configuration fixtures produce identical bytes across supported runners.
- Every authoritative push artifact retains the generated canonical tarball
  beside the manifest, gate summary, and logs for independent pre-tag review.
- The workflow-policy checker binds retention across the authoritative
  main/release-tag push trigger, active fail-closed job, a project-owned
  per-object guard immediately before upload, and the pinned upload step. The
  guard separately requires one tarball, the manifest, summary, and every gate
  log; guard/step/job error suppression, relocation, substitution, or
  unreachable push conditions fail validation.
- The release-core gate fails when the archive-content checker is bypassed or
  reports a mismatch.

## Risks

Symlinks and executable bits must retain their intended Git semantics.
Gitlinks/submodules are rejected with a policy error rather than silently
omitted. Tests must inspect the produced tar, not merely the input list.
