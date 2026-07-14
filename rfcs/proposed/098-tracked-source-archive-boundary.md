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
2. Build the source archive with `git archive` or a NUL-safe `git ls-files -z`
   pipeline. Preserve deterministic path order, timestamp, owner, group, and
   Git executable/symlink modes. Pin `tar.umask=0022` independently of ambient
   Git configuration; reject gitlinks/submodules until an explicit recursive
   source policy exists.
3. Add an archive policy checker that validates:
   - every source entry is tracked and expected;
   - no `.git`, `.git-exclude`, cache, build, or release-output entry exists;
   - paths extract directly at the destination root;
   - no unexpected top-level path exists;
   - regular, executable, directory, and symlink modes match the Git tree;
   - a second build from the same commit produces the same SHA-256.
4. Record the archive policy/checker hash in the release manifest.
5. Keep the dirty-tree rejection as a separate guarantee: tracked modifications
   still prevent an authoritative release even though the archive is selected
   from tracked paths.

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
- The release-core gate fails when the archive-content checker is bypassed or
  reports a mismatch.

## Risks

Symlinks and executable bits must retain their intended Git semantics.
Gitlinks/submodules are rejected with a policy error rather than silently
omitted. Tests must inspect the produced tar, not merely the input list.
