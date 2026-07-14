#!/usr/bin/env python3
"""Build and validate the canonical Git-tracked source archive (RFC 098)."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import subprocess
import tarfile
import tempfile
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = {".git", ".git-exclude", ".lake", "release", "docs/book",
             "__pycache__", ".cache", ".elan"}
CANONICAL_UMASK = "0022"


def git(root: Path, *args: str, binary: bool = False):
    return subprocess.run(["git", *args], cwd=root, check=True, capture_output=True,
                          text=not binary).stdout


def tracked(root: Path, commit: str) -> dict[str, str]:
    raw = git(root, "ls-tree", "-rz", "--full-tree", commit, binary=True)
    paths = {}
    for record in raw.split(b"\0"):
        if not record:
            continue
        meta, path = record.split(b"\t", 1)
        mode, kind, _object = meta.split()
        if kind in (b"blob", b"commit"):
            paths[path.decode("utf-8", "surrogateescape")] = mode.decode()
    return paths


def tracked_dirs(paths) -> set[str]:
    dirs = set()
    for name in paths:
        parent = PurePosixPath(name).parent
        while parent != PurePosixPath("."):
            dirs.add(parent.as_posix())
            parent = parent.parent
    return dirs


def forbidden(path: str) -> bool:
    return any(path == item or path.startswith(item + "/") for item in FORBIDDEN)


def archive_bytes(root: Path, commit: str) -> bytes:
    gitlinks = sorted(path for path, mode in tracked(root, commit).items()
                      if mode == "160000")
    if gitlinks:
        raise ValueError(f"gitlinks/submodules are unsupported: {gitlinks}")
    # Pin Git's supported tar.umask knob so user/repository/global config cannot
    # change the canonical archive modes or bytes.
    tar = git(root, "-c", f"tar.umask={CANONICAL_UMASK}",
              "archive", "--format=tar", commit, binary=True)
    out = io.BytesIO()
    with gzip.GzipFile(fileobj=out, mode="wb", filename="", mtime=0,
                       compresslevel=9) as gz:
        gz.write(tar)
    return out.getvalue()


def validate(root: Path, commit: str, archive: Path) -> list[str]:
    errors = []
    expected = tracked(root, commit)
    for path, mode in expected.items():
        if mode == "160000":
            errors.append(f"gitlink/submodule is unsupported by source archive policy: {path}")
    expected_dirs = tracked_dirs(expected)
    actual, actual_dirs, seen = set(), set(), set()
    with tarfile.open(archive, "r:gz") as tf:
        for member in tf.getmembers():
            name = member.name.rstrip("/")
            p = PurePosixPath(name)
            if not name or p.is_absolute() or ".." in p.parts or name.startswith("./"):
                errors.append(f"unsafe/non-root archive path: {member.name!r}")
            if forbidden(name):
                errors.append(f"forbidden archive path: {name}")
            if name in seen:
                errors.append(f"duplicate archive member: {name}")
            seen.add(name)
            if member.isdir():
                actual_dirs.add(name)
                if name not in expected_dirs:
                    errors.append(f"unexpected archive directory: {name}")
                if member.mode & 0o777 != 0o755:
                    errors.append(f"archive directory mode must be 0755: {name} "
                                  f"has {member.mode & 0o777:04o}")
            elif member.isfile() or member.issym():
                actual.add(name)
                mode = expected.get(name)
                if mode is None:
                    errors.append(f"archive entry not tracked at {commit}: {name}")
                elif member.issym() != (mode == "120000"):
                    errors.append(f"archive member type disagrees with Git mode {mode}: {name}")
                else:
                    expected_mode = (0o777 if mode == "120000" else
                                     0o755 if mode == "100755" else 0o644)
                    if member.mode & 0o777 != expected_mode:
                        errors.append(f"archive mode disagrees with Git mode {mode}: "
                                      f"{name} has {member.mode & 0o777:04o}, "
                                      f"expected {expected_mode:04o}")
            else:
                errors.append(f"unsupported archive member type {member.type!r}: {name}")
    expected_names = set(expected)
    missing, extra = sorted(expected_names - actual), sorted(actual - expected_names)
    if missing:
        errors.append(f"tracked entries missing from archive: {missing[:5]}")
    if extra:
        errors.append(f"archive entries not tracked at {commit}: {extra[:5]}")
    missing_dirs, extra_dirs = sorted(expected_dirs - actual_dirs), sorted(actual_dirs - expected_dirs)
    if missing_dirs:
        errors.append(f"tracked directory prefixes missing from archive: {missing_dirs[:5]}")
    if extra_dirs:
        errors.append(f"unexpected archive directories: {extra_dirs[:5]}")
    for path in sorted(expected):
        if forbidden(path):
            errors.append(f"tracked path violates archive policy: {path}")
    return errors


def build(root: Path, commit: str, output: Path) -> None:
    try:
        first = archive_bytes(root, commit)
        second = archive_bytes(root, commit)
    except ValueError as error:
        raise SystemExit(f"source-archive: {error}") from error
    if hashlib.sha256(first).digest() != hashlib.sha256(second).digest():
        raise SystemExit("source-archive: repeated build is not byte-reproducible")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(first)
    errors = validate(root, commit, output)
    if errors:
        output.unlink(missing_ok=True)
        raise SystemExit("\n".join(f"source-archive: {e}" for e in errors))
    print(f"source-archive: {len(tracked(root, commit))} tracked entries; "
          f"sha256={hashlib.sha256(first).hexdigest()}")


def mutated_archive(source: Path, output: Path, *, drop: str | None = None,
                    addition: tarfile.TarInfo | None = None, data: bytes = b"",
                    mode_change: tuple[str, int] | None = None) -> None:
    with tarfile.open(source, "r:gz") as src, tarfile.open(output, "w:gz") as dst:
        for member in src.getmembers():
            if member.name.rstrip("/") == drop:
                continue
            if mode_change and member.name.rstrip("/") == mode_change[0]:
                member.mode = mode_change[1]
            payload = src.extractfile(member) if member.isfile() else None
            dst.addfile(member, payload)
        if addition is not None:
            dst.addfile(addition, io.BytesIO(data) if addition.isfile() else None)


def self_test() -> int:
    base = ROOT / ".git-exclude" / "tmp"
    base.mkdir(parents=True, exist_ok=True)
    errors = []
    with tempfile.TemporaryDirectory(prefix="archive-selftest-", dir=base) as td:
        repo = Path(td)
        git(repo, "init", "-q")
        (repo / ".gitignore").write_text("ignored.txt\n.git-exclude/\n")
        (repo / "tracked.txt").write_text("tracked\n")
        (repo / "run.sh").write_text("#!/bin/sh\nexit 0\n")
        (repo / "run.sh").chmod(0o755)
        (repo / "tracked-link").symlink_to("tracked.txt")
        git(repo, "add", ".gitignore", "tracked.txt", "run.sh", "tracked-link")
        git(repo, "-c", "user.name=Henret", "-c", "user.email=test@example.invalid",
            "-c", "commit.gpgSign=false", "commit", "-qm", "fixture")
        (repo / "ignored.txt").write_text("must not ship\n")
        (repo / ".git-exclude").mkdir()
        (repo / ".git-exclude" / "sentinel").write_text("must not ship\n")
        out = repo / "archive.tar.gz"
        build(repo, "HEAD", out)
        with tarfile.open(out, "r:gz") as tf:
            names = set(tf.getnames())
        if "ignored.txt" in names or ".git-exclude/sentinel" in names:
            errors.append("ignored/untracked sentinel entered archive")
        if validate(repo, "HEAD", out):
            errors.append("valid archive was rejected")
        # Canonical bytes must ignore ambient repository/user tar.umask.
        git(repo, "config", "tar.umask", "0002")
        loose = archive_bytes(repo, "HEAD")
        git(repo, "config", "tar.umask", "0077")
        strict = archive_bytes(repo, "HEAD")
        if loose != strict:
            errors.append("ambient tar.umask changed canonical archive bytes")
        fixtures = []
        unexpected_dir = tarfile.TarInfo("unexpected-top-level/")
        unexpected_dir.type = tarfile.DIRTYPE
        fixtures.append(("unexpected directory", {"addition": unexpected_dir}))
        fifo = tarfile.TarInfo("unsupported-fifo")
        fifo.type = tarfile.FIFOTYPE
        fixtures.append(("unsupported member type", {"addition": fifo}))
        extra = tarfile.TarInfo("extra.txt")
        extra.size = 5
        fixtures.append(("extra file", {"addition": extra, "data": b"extra"}))
        unsafe = tarfile.TarInfo("../escape")
        unsafe.size = 1
        fixtures.append(("unsafe path", {"addition": unsafe, "data": b"x"}))
        fixtures.append(("missing tracked file", {"drop": "tracked.txt"}))
        fixtures.append(("executable mode removal",
                         {"mode_change": ("run.sh", 0o644)}))
        fixtures.append(("non-executable mode escalation",
                         {"mode_change": ("tracked.txt", 0o755)}))
        for index, (label, kwargs) in enumerate(fixtures):
            broken = repo / f"broken-{index}.tar.gz"
            mutated_archive(out, broken, **kwargs)
            if not validate(repo, "HEAD", broken):
                errors.append(f"validator accepted {label}")

        # A tracked internal path is outside the archive policy even though it
        # is part of the Git tree; this is distinct from ignored sentinels.
        internal = repo / ".git-exclude" / "tracked"
        internal.write_text("tracked but forbidden\n")
        git(repo, "add", "-f", ".git-exclude/tracked")
        git(repo, "-c", "user.name=Henret", "-c", "user.email=test@example.invalid",
            "-c", "commit.gpgSign=false", "commit", "-qm", "forbidden fixture")
        forbidden_tar = repo / "forbidden.tar.gz"
        forbidden_tar.write_bytes(archive_bytes(repo, "HEAD"))
        if not validate(repo, "HEAD", forbidden_tar):
            errors.append("validator accepted tracked forbidden path")

        # Gitlinks are rejected explicitly rather than silently emitting an
        # incomplete submodule directory.
        head = git(repo, "rev-parse", "HEAD").strip()
        git(repo, "update-index", "--add", "--cacheinfo",
            f"160000,{head},vendor/submodule")
        git(repo, "-c", "user.name=Henret", "-c", "user.email=test@example.invalid",
            "-c", "commit.gpgSign=false", "commit", "-qm", "gitlink fixture")
        try:
            archive_bytes(repo, "HEAD")
            errors.append("builder accepted gitlink/submodule")
        except ValueError as error:
            if "gitlinks/submodules are unsupported" not in str(error):
                errors.append("builder rejected gitlink without clear policy error")
        raw_gitlink = git(repo, "-c", f"tar.umask={CANONICAL_UMASK}", "archive",
                          "--format=tar", "HEAD", binary=True)
        gitlink_tar = repo / "gitlink.tar.gz"
        with gitlink_tar.open("wb") as raw_output:
            with gzip.GzipFile(filename="", mode="wb", fileobj=raw_output,
                               mtime=0) as gz:
                gz.write(raw_gitlink)
        if not any("gitlink/submodule" in error
                   for error in validate(repo, "HEAD", gitlink_tar)):
            errors.append("validator accepted gitlink/submodule policy")
    print(f"source-archive-selftest: {len(errors)} error(s)")
    return 1 if errors else 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--check", type=Path)
    parser.add_argument("--commit", default="HEAD")
    parser.add_argument("output", type=Path, nargs="?")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    if args.check:
        errors = validate(ROOT, args.commit, args.check)
        for error in errors:
            print(f"source-archive: {error}")
        return 1 if errors else 0
    if not args.output:
        parser.error("output path required unless --check/--self-test is used")
    build(ROOT, args.commit, args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
