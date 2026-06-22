#!/usr/bin/env python3
"""RFC 096 — verify a stack-release.json against local package manifests.

    verify_stack_release.py <stack-release.json> <manifest-dir> [tarball-dir]

Local-file v1 (network fetching is a later revision). Manifests are resolved by
**hash, not URL** (RFC 096 D6): each package's manifest is the file in
`manifest-dir` whose SHA-256 equals the package entry's `manifest_sha256`.

Checks (RFC 096 D5):

  packages:  names unique; each manifest_sha256 resolves to a manifest whose
             package/version match the entry; tarball_sha256 resolves in
             tarball-dir when that dir is given.
  edges:     consumer and provider each resolve to exactly one package entry;
             provider_manifest_sha256 == provider entry's manifest_sha256; and
             the edge matches a `dependencies` entry in the resolved consumer
             manifest (package, version, manifest_sha256).

Hash-only verification (trusts the channel the artifacts were fetched over).
Exit 0 on success, non-zero on any mismatch.
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def index_by_hash(directory: Path, pattern: str) -> dict[str, Path]:
    out: dict[str, Path] = {}
    if directory and directory.is_dir():
        for p in directory.glob(pattern):
            try:
                out[sha256_file(p)] = p
            except OSError:
                pass
    return out


def main() -> int:
    if not 3 <= len(sys.argv) <= 4:
        print(__doc__)
        return 2
    stack_path = Path(sys.argv[1])
    manifest_dir = Path(sys.argv[2])
    tarball_dir = Path(sys.argv[3]) if len(sys.argv) > 3 else None

    if not stack_path.exists():
        print(f"verify-stack: missing {stack_path}", file=sys.stderr)
        return 2
    stack = json.loads(stack_path.read_text())
    errors: list[str] = []

    if stack.get("stack_manifest_schema") != 1:
        errors.append(f"unexpected stack_manifest_schema: "
                      f"{stack.get('stack_manifest_schema')!r}")

    packages = stack.get("packages", [])
    manifests_by_hash = index_by_hash(manifest_dir, "*.json")
    tarballs_by_hash = index_by_hash(tarball_dir, "*") if tarball_dir else {}

    # packages: uniqueness + resolution
    by_name: dict[str, dict] = {}
    loaded_manifest: dict[str, dict] = {}      # package name -> manifest json
    for entry in packages:
        name = entry.get("package")
        if name in by_name:
            errors.append(f"duplicate package in stack: {name!r}")
            continue
        by_name[name] = entry
        mh = entry.get("manifest_sha256")
        mpath = manifests_by_hash.get(mh)
        if not mpath:
            errors.append(f"{name}: manifest_sha256 {mh} not found in {manifest_dir}")
            continue
        m = json.loads(mpath.read_text())
        loaded_manifest[name] = m
        if m.get("package") != name:
            errors.append(f"{name}: manifest package is {m.get('package')!r}")
        if m.get("version") != entry.get("version"):
            errors.append(f"{name}: version {entry.get('version')!r} != manifest "
                          f"{m.get('version')!r}")
        if tarball_dir is not None:
            th = entry.get("tarball_sha256")
            if th not in tarballs_by_hash:
                errors.append(f"{name}: tarball_sha256 {th} not found in {tarball_dir}")

    # edges: resolution + cross-check against consumer manifest dependencies
    for e in stack.get("dependency_edges", []):
        consumer, provider = e.get("consumer"), e.get("provider")
        if consumer not in by_name:
            errors.append(f"edge consumer {consumer!r} not a package entry")
        if provider not in by_name:
            errors.append(f"edge provider {provider!r} not a package entry")
        if consumer not in by_name or provider not in by_name:
            continue
        pmh = e.get("provider_manifest_sha256")
        if pmh != by_name[provider].get("manifest_sha256"):
            errors.append(f"edge {consumer}->{provider}: provider_manifest_sha256 "
                          f"!= provider package entry manifest_sha256")
        cm = loaded_manifest.get(consumer, {})
        deps = cm.get("dependencies", [])
        match = [d for d in deps
                 if d.get("package") == provider
                 and d.get("version") == e.get("provider_version")
                 and d.get("manifest_sha256") == pmh]
        if not match:
            errors.append(f"edge {consumer}->{provider} ({e.get('provider_version')}) "
                          f"has no matching dependency in {consumer}'s manifest")

    if errors:
        for x in errors:
            print(f"verify-stack: FAIL — {x}", file=sys.stderr)
        return 1

    print(f"verify-stack: OK — {stack.get('stack')} v{stack.get('stack_version')}; "
          f"{len(packages)} packages, "
          f"{len(stack.get('dependency_edges', []))} edges verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
