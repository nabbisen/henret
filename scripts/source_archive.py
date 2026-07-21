#!/usr/bin/env python3
"""Build and validate the canonical Git-tracked source archive (RFC 098)."""
from __future__ import annotations

import argparse
import binascii
import gzip
import hashlib
import io
import os
import struct
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = {".git", ".git-exclude", ".lake", "release", "docs/book",
             "__pycache__", ".cache", ".elan"}
CANONICAL_UMASK = "0022"
TAR_BLOCK = 512
DEFLATE_BLOCK = 65535
GZIP_HEADER = bytes.fromhex("1f8b08000000000000ff")


def git(root: Path, *args: str, binary: bool = False,
        env: dict[str, str] | None = None):
    # A named commit must always mean its literal object graph. Repository-local
    # refs/replace state is not tracked release input and must never substitute
    # a different tree, blob, or commit timestamp behind the same object ID.
    return subprocess.run(["git", "--no-replace-objects", *args], cwd=root,
                          check=True, capture_output=True, text=not binary,
                          env=env).stdout


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


def git_blob(root: Path, commit: str, path: str) -> bytes:
    return git(root, "cat-file", "blob", f"{commit}:{path}", binary=True)


def canonical_utf8(value: str, label: str) -> bytes:
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{label} is not canonical UTF-8: {value!r}") from exc
    if not encoded or b"\0" in encoded:
        raise ValueError(f"{label} is empty or contains NUL: {value!r}")
    return encoded


def octal_field(value: int, width: int, label: str) -> bytes:
    if value < 0:
        raise ValueError(f"negative {label} is unsupported: {value}")
    encoded = f"{value:0{width - 1}o}".encode()
    if len(encoded) >= width:
        raise ValueError(f"{label} does not fit canonical tar field: {value}")
    return encoded + b"\0"


def ustar_name(path: str) -> tuple[bytes, bytes]:
    raw = canonical_utf8(path, "archive path")
    if len(raw) <= 100:
        return raw, b""
    splits = [index for index, char in enumerate(path) if char == "/"
              and index not in (0, len(path) - 1)]
    for split in reversed(splits):
        prefix = canonical_utf8(path[:split], "archive prefix")
        name = canonical_utf8(path[split + 1:], "archive name")
        if len(prefix) <= 155 and len(name) <= 100:
            return name, prefix
    raise ValueError(f"archive path does not fit canonical ustar fields: {path!r}")


def tar_header(*, path: str, mode: int, size: int, mtime: int,
               kind: bytes, link: bytes = b"") -> bytes:
    name, prefix = ustar_name(path)
    if kind not in (b"0", b"2", b"5"):
        raise ValueError(f"unsupported canonical tar typeflag: {kind!r}")
    if kind != b"2" and link:
        raise ValueError(f"non-symlink member has a link target: {path!r}")
    if len(link) > 100 or b"\0" in link:
        raise ValueError(f"link target does not fit canonical ustar field: {path!r}")
    header = bytearray(TAR_BLOCK)

    def put(start: int, width: int, value: bytes, label: str) -> None:
        if len(value) > width:
            raise ValueError(f"{label} exceeds canonical tar field width")
        header[start:start + len(value)] = value

    put(0, 100, name, "name")
    put(100, 8, octal_field(mode, 8, "mode"), "mode")
    put(108, 8, octal_field(0, 8, "uid"), "uid")
    put(116, 8, octal_field(0, 8, "gid"), "gid")
    put(124, 12, octal_field(size, 12, "size"), "size")
    put(136, 12, octal_field(mtime, 12, "mtime"), "mtime")
    header[148:156] = b"        "
    put(156, 1, kind, "typeflag")
    put(157, 100, link, "linkname")
    put(257, 6, b"ustar\0", "magic")
    put(263, 2, b"00", "version")
    put(329, 8, octal_field(0, 8, "device major"), "device major")
    put(337, 8, octal_field(0, 8, "device minor"), "device minor")
    put(345, 155, prefix, "prefix")
    checksum = sum(header)
    if checksum > 0o777777:
        raise ValueError(f"tar checksum does not fit canonical field: {path!r}")
    header[148:156] = f"{checksum:06o}\0 ".encode()
    return bytes(header)


def serialize_tar(members: list[dict], mtime: int) -> bytes:
    out = io.BytesIO()
    for member in members:
        data = member.get("data", b"")
        kind = member["kind"]
        payload = data if kind == b"0" else b""
        out.write(tar_header(path=member["path"], mode=member["mode"],
                             size=len(payload), mtime=mtime, kind=kind,
                             link=member.get("link", b"")))
        out.write(payload)
        out.write(b"\0" * (-len(payload) % TAR_BLOCK))
    out.write(b"\0" * (2 * TAR_BLOCK))
    return out.getvalue()


def archive_tar_bytes(root: Path, commit: str) -> bytes:
    paths = tracked(root, commit)
    gitlinks = sorted(path for path, mode in paths.items() if mode == "160000")
    if gitlinks:
        raise ValueError(f"gitlinks/submodules are unsupported: {gitlinks}")
    members: list[dict] = []
    for directory in tracked_dirs(paths):
        if forbidden(directory):
            raise ValueError(f"tracked path violates archive policy: {directory}")
        members.append({"path": directory + "/", "mode": 0o755, "kind": b"5"})
    for path, git_mode in paths.items():
        if forbidden(path):
            raise ValueError(f"tracked path violates archive policy: {path}")
        p = PurePosixPath(path)
        if p.is_absolute() or ".." in p.parts or path.startswith("./"):
            raise ValueError(f"unsafe/non-root tracked path: {path!r}")
        data = git_blob(root, commit, path)
        if git_mode == "120000":
            try:
                data.decode("utf-8")
            except UnicodeDecodeError as exc:
                raise ValueError(f"symlink target is not canonical UTF-8: {path}") from exc
            members.append({"path": path, "mode": 0o777, "kind": b"2", "link": data})
        elif git_mode in ("100644", "100755"):
            members.append({"path": path,
                            "mode": 0o755 if git_mode == "100755" else 0o644,
                            "kind": b"0", "data": data})
        else:
            raise ValueError(f"unsupported Git mode {git_mode} for {path}")
    members.sort(key=lambda member: canonical_utf8(member["path"], "archive path"))
    timestamp = int(git(root, "show", "-s", "--format=%ct", commit).strip())
    return serialize_tar(members, timestamp)


def stored_deflate(data: bytes) -> bytes:
    out = io.BytesIO()
    if not data:
        return b"\x01\x00\x00\xff\xff"
    for offset in range(0, len(data), DEFLATE_BLOCK):
        block = data[offset:offset + DEFLATE_BLOCK]
        final = offset + len(block) == len(data)
        out.write(b"\x01" if final else b"\x00")
        out.write(struct.pack("<HH", len(block), 0xffff ^ len(block)))
        out.write(block)
    return out.getvalue()


def canonical_gzip(data: bytes) -> bytes:
    trailer = struct.pack("<II", binascii.crc32(data) & 0xffffffff,
                          len(data) & 0xffffffff)
    return GZIP_HEADER + stored_deflate(data) + trailer


def archive_bytes(root: Path, commit: str) -> bytes:
    return canonical_gzip(archive_tar_bytes(root, commit))


def validate(root: Path, commit: str, archive: Path) -> list[str]:
    errors = []
    expected = tracked(root, commit)
    for path, mode in expected.items():
        if mode == "160000":
            errors.append(f"gitlink/submodule is unsupported by source archive policy: {path}")
    expected_dirs = tracked_dirs(expected)
    expected_order = sorted([*expected, *(directory + "/" for directory in expected_dirs)],
                            key=lambda name: canonical_utf8(name, "archive path"))
    actual, actual_dirs, seen, actual_order = set(), set(), set(), []
    expected_mtime = int(git(root, "show", "-s", "--format=%ct", commit).strip())
    try:
        with tarfile.open(archive, "r:gz") as tf:
            for member in tf.getmembers():
                raw_name = member.name
                name = raw_name.rstrip("/")
                actual_order.append(name + "/" if member.isdir() else name)
                p = PurePosixPath(name)
                if not name or p.is_absolute() or ".." in p.parts or name.startswith("./"):
                    errors.append(f"unsafe/non-root archive path: {raw_name!r}")
                if forbidden(name):
                    errors.append(f"forbidden archive path: {name}")
                if name in seen:
                    errors.append(f"duplicate archive member: {name}")
                seen.add(name)
                if member.uid != 0 or member.gid != 0 or member.uname or member.gname:
                    errors.append(f"archive ownership must be numeric root/root: {name}")
                if member.mtime != expected_mtime:
                    errors.append(f"archive mtime disagrees with commit: {name}")
                if member.pax_headers:
                    errors.append(f"archive member uses unsupported PAX headers: {name}")
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
                        expected_data = git_blob(root, commit, name)
                        if member.issym():
                            try:
                                observed_link = member.linkname.encode("utf-8")
                            except UnicodeEncodeError:
                                observed_link = b""
                            if observed_link != expected_data:
                                errors.append(f"archive symlink target disagrees with Git: {name}")
                        else:
                            stream = tf.extractfile(member)
                            observed_data = stream.read() if stream is not None else b""
                            if observed_data != expected_data:
                                errors.append(f"archive file bytes disagree with Git: {name}")
                else:
                    errors.append(f"unsupported archive member type {member.type!r}: {name}")
    except (OSError, tarfile.TarError, EOFError) as exc:
        return [f"cannot read archive: {exc}"]
    if actual_order != expected_order:
        errors.append("archive member order is not canonical UTF-8 byte order")
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


def canonical_errors(root: Path, commit: str, archive: Path) -> list[str]:
    try:
        expected = archive_bytes(root, commit)
        observed = archive.read_bytes()
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        return [f"cannot compare canonical archive bytes: {exc}"]
    if observed == expected:
        return []
    return ["archive bytes are not canonical for commit "
            f"{commit}: expected sha256={hashlib.sha256(expected).hexdigest()}, "
            f"observed sha256={hashlib.sha256(observed).hexdigest()}"]


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
    errors = validate(root, commit, output) + canonical_errors(root, commit, output)
    if errors:
        output.unlink(missing_ok=True)
        raise SystemExit("\n".join(f"source-archive: {e}" for e in errors))
    print(f"source-archive: {len(tracked(root, commit))} tracked entries; "
          f"sha256={hashlib.sha256(first).hexdigest()}")


def mutated_archive(source: Path, output: Path, *, drop: str | None = None,
                    addition: tarfile.TarInfo | None = None, data: bytes = b"",
                    mode_change: tuple[str, int] | None = None,
                    link_change: tuple[str, str] | None = None,
                    data_change: tuple[str, bytes] | None = None,
                    reverse: bool = False) -> None:
    with tarfile.open(source, "r:gz") as src, tarfile.open(output, "w:gz") as dst:
        members = src.getmembers()
        if reverse:
            members.reverse()
        for member in members:
            if member.name.rstrip("/") == drop:
                continue
            if mode_change and member.name.rstrip("/") == mode_change[0]:
                member.mode = mode_change[1]
            if link_change and member.name.rstrip("/") == link_change[0]:
                member.linkname = link_change[1]
            payload = src.extractfile(member) if member.isfile() else None
            if data_change and member.name.rstrip("/") == data_change[0]:
                replacement = data_change[1]
                member.size = len(replacement)
                payload = io.BytesIO(replacement)
            dst.addfile(member, payload)
        if addition is not None:
            dst.addfile(addition, io.BytesIO(data) if addition.isfile() else None)


def self_test() -> int:
    base = ROOT / ".git-exclude" / "tmp"
    base.mkdir(parents=True, exist_ok=True)
    errors = []

    gzip_vectors = {
        b"": "1f8b08000000000000ff010000ffff0000000000000000",
        b"abc": "1f8b08000000000000ff010300fcff616263c241243503000000",
    }
    for payload, expected_hex in gzip_vectors.items():
        if canonical_gzip(payload).hex() != expected_hex:
            errors.append(f"gzip fixed vector disagrees for {len(payload)} bytes")
    block_hashes = {
        65535: "643fb7a87b8f0817ef09ff2d10fd0dc57747d02ea7f27f5e159c350e2e3f08cf",
        65536: "8ce1228370933e613c738255b30a7b85d69a81d73a3e96a88e0e10871a3695a9",
        131071: "8b0eaf030469e9453eaf05f3f545329ffa387bd0065a6bc25f6300fe305f706d",
    }
    for size, expected_hash in block_hashes.items():
        observed = hashlib.sha256(canonical_gzip(b"x" * size)).hexdigest()
        if observed != expected_hash:
            errors.append(f"gzip {size}-byte golden hash {observed} != {expected_hash}")

    golden_members = [
        {"path": "bin/", "mode": 0o755, "kind": b"5"},
        {"path": "bin/run", "mode": 0o755, "kind": b"0", "data": b"#!/bin/sh\n"},
        {"path": "empty", "mode": 0o644, "kind": b"0", "data": b""},
        {"path": "link", "mode": 0o777, "kind": b"2", "link": b"plain"},
        {"path": "plain", "mode": 0o644, "kind": b"0", "data": b"hello\n"},
    ]
    golden_tar = serialize_tar(golden_members, 1700000000)
    golden_tar_hash = hashlib.sha256(golden_tar).hexdigest()
    if golden_tar_hash != "e1c96234b93ca64549583778a8bbb7d1c9f0ed6a19018b6edc287d868745e266":
        errors.append(f"tar golden hash disagrees: {golden_tar_hash}")
    boundary_members = [
        {"path": "n" * 100, "mode": 0o644, "kind": b"0", "data": b""},
        {"path": "p" * 155 + "/" + "q" * 100,
         "mode": 0o644, "kind": b"0", "data": b"boundary\n"},
        {"path": "é" * 50, "mode": 0o644, "kind": b"0", "data": b"utf8\n"},
        {"path": "link-100", "mode": 0o777, "kind": b"2", "link": b"l" * 100},
    ]
    boundary_tar = serialize_tar(boundary_members, 1700000000)
    boundary_hash = hashlib.sha256(boundary_tar).hexdigest()
    if boundary_hash != "65009520db73e6c5791f5588b2c5786aea190e83c7b8ca3b2cd318283e901c82":
        errors.append(f"tar boundary golden hash disagrees: {boundary_hash}")
    with tarfile.open(fileobj=io.BytesIO(boundary_tar), mode="r:") as archive:
        observed = archive.getmembers()
    if [member.name for member in observed] != [member["path"] for member in boundary_members] \
            or observed[-1].linkname != "l" * 100:
        errors.append("supported ustar path/link boundary did not round-trip")
    try:
        tar_header(path="x" * 101, mode=0o644, size=0, mtime=0, kind=b"0")
        errors.append("tar serializer accepted an unsplittable overlong path")
    except ValueError:
        pass
    try:
        tar_header(path="link", mode=0o777, size=0, mtime=0, kind=b"2",
                   link=b"x" * 101)
        errors.append("tar serializer accepted an overlong link target")
    except ValueError:
        pass
    try:
        canonical_utf8("\udcff", "fixture")
        errors.append("tar serializer accepted a non-UTF-8 fixture")
    except ValueError:
        pass
    for label, kwargs in (
            ("size overflow", {"size": 1 << 33, "mtime": 0}),
            ("timestamp overflow", {"size": 0, "mtime": 1 << 33})):
        try:
            tar_header(path="overflow", mode=0o644, kind=b"0", **kwargs)
            errors.append(f"tar serializer accepted {label}")
        except ValueError:
            pass

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
        if validate(repo, "HEAD", out) or canonical_errors(repo, "HEAD", out):
            errors.append("valid archive was rejected")
        # Canonical bytes do not delegate to Git's archive serializer and must
        # ignore ambient repository/user tar.umask.
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
        fixtures.append(("tracked byte mutation",
                         {"data_change": ("tracked.txt", b"changed\n")}))
        fixtures.append(("symlink target mutation",
                         {"link_change": ("tracked-link", "run.sh")}))
        fixtures.append(("member order reversal", {"reverse": True}))
        for index, (label, kwargs) in enumerate(fixtures):
            broken = repo / f"broken-{index}.tar.gz"
            mutated_archive(out, broken, **kwargs)
            if not validate(repo, "HEAD", broken):
                errors.append(f"validator accepted {label}")
            if not canonical_errors(repo, "HEAD", broken):
                errors.append(f"canonical comparison accepted {label}")

        # A structurally valid gzip using a different DEFLATE encoding is not
        # the canonical file, even though it expands to the canonical tar.
        alternate = repo / "alternate-gzip.tar.gz"
        with alternate.open("wb") as raw:
            with gzip.GzipFile(filename="", mode="wb", fileobj=raw,
                               mtime=0, compresslevel=9) as encoded:
                encoded.write(archive_tar_bytes(repo, "HEAD"))
        if validate(repo, "HEAD", alternate):
            errors.append("structurally valid alternate gzip failed content validation")
        if not canonical_errors(repo, "HEAD", alternate):
            errors.append("canonical comparison accepted alternate valid gzip encoding")

        raw_tar = bytearray(archive_tar_bytes(repo, "HEAD"))
        header_changed = bytearray(raw_tar)
        header_changed[500] ^= 1  # reserved ustar header byte
        header_changed[148:156] = b"        "
        header_changed[148:156] = f"{sum(header_changed[:TAR_BLOCK]):06o}\0 ".encode()
        header_archive = repo / "alternate-tar-header.tar.gz"
        header_archive.write_bytes(canonical_gzip(header_changed))
        if validate(repo, "HEAD", header_archive):
            errors.append("valid alternate tar header failed structural validation")
        if not canonical_errors(repo, "HEAD", header_archive):
            errors.append("canonical comparison accepted alternate tar header")

        padding_changed = bytearray(raw_tar)
        tracked_at = padding_changed.find(b"tracked\n")
        if tracked_at < 0:
            errors.append("tar padding fixture could not locate tracked payload")
        else:
            padding_changed[tracked_at + len(b"tracked\n")] = 1
            padding_archive = repo / "alternate-tar-padding.tar.gz"
            padding_archive.write_bytes(canonical_gzip(padding_changed))
            if validate(repo, "HEAD", padding_archive):
                errors.append("valid alternate tar padding failed structural validation")
            if not canonical_errors(repo, "HEAD", padding_archive):
                errors.append("canonical comparison accepted alternate tar padding")

        # Byte-level header, block, CRC, and ISIZE mutations all fail closed.
        canonical = out.read_bytes()
        mutation_offsets = {
            "gzip header": 9,
            "DEFLATE block": len(GZIP_HEADER),
            "CRC-32": len(canonical) - 8,
            "ISIZE": len(canonical) - 4,
        }
        for label, offset in mutation_offsets.items():
            changed = bytearray(canonical)
            changed[offset] ^= 1
            broken = repo / f"byte-{label.replace(' ', '-')}.tar.gz"
            broken.write_bytes(changed)
            if not canonical_errors(repo, "HEAD", broken):
                errors.append(f"canonical comparison accepted {label} mutation")

        # A tracked internal path is outside the archive policy even though it
        # is part of the Git tree; this is distinct from ignored sentinels.
        internal = repo / ".git-exclude" / "tracked"
        internal.write_text("tracked but forbidden\n")
        git(repo, "add", "-f", ".git-exclude/tracked")
        git(repo, "-c", "user.name=Henret", "-c", "user.email=test@example.invalid",
            "-c", "commit.gpgSign=false", "commit", "-qm", "forbidden fixture")
        try:
            archive_bytes(repo, "HEAD")
            errors.append("builder accepted tracked forbidden path")
        except ValueError as error:
            if "violates archive policy" not in str(error):
                errors.append("builder rejected forbidden path without clear policy error")

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

    # Replacement refs must not alter any source fact behind a named object ID.
    # Ordinary Git is also sampled to prove the fixture would substitute the
    # replacement tree, blob, and timestamp without --no-replace-objects.
    with tempfile.TemporaryDirectory(prefix="archive-replace-selftest-", dir=base) as td:
        repo = Path(td)
        git(repo, "init", "-q")
        (repo / "payload").write_bytes(b"original\n")
        git(repo, "add", "payload")
        original_env = {**os.environ, "GIT_AUTHOR_DATE": "1700000000 +0000",
                        "GIT_COMMITTER_DATE": "1700000000 +0000"}
        git(repo, "-c", "user.name=Henret", "-c", "user.email=test@example.invalid",
            "-c", "commit.gpgSign=false", "commit", "-qm", "original", env=original_env)
        original = git(repo, "rev-parse", "HEAD").strip()
        original_tree = git(repo, "ls-tree", "-rz", "--full-tree", original, binary=True)
        original_blob = git_blob(repo, original, "payload")
        original_time = git(repo, "show", "-s", "--format=%ct", original).strip()
        original_archive = archive_bytes(repo, original)

        (repo / "payload").write_bytes(b"replacement\n")
        git(repo, "add", "payload")
        replacement_env = {**os.environ, "GIT_AUTHOR_DATE": "1700000100 +0000",
                           "GIT_COMMITTER_DATE": "1700000100 +0000"}
        git(repo, "-c", "user.name=Henret", "-c", "user.email=test@example.invalid",
            "-c", "commit.gpgSign=false", "commit", "-qm", "replacement",
            env=replacement_env)
        replacement = git(repo, "rev-parse", "HEAD").strip()
        replacement_archive = archive_bytes(repo, replacement)
        git(repo, "replace", original, replacement)

        protected_tree = git(repo, "ls-tree", "-rz", "--full-tree", original, binary=True)
        protected_blob = git_blob(repo, original, "payload")
        protected_time = git(repo, "show", "-s", "--format=%ct", original).strip()
        protected_archive = archive_bytes(repo, original)
        if (protected_tree, protected_blob, protected_time, protected_archive) != \
                (original_tree, original_blob, original_time, original_archive):
            errors.append("replacement ref changed protected exact-commit source facts")
        if replacement_archive == original_archive:
            errors.append("replacement fixture did not change candidate archive bytes")

        def ordinary(*args: str, binary: bool = False):
            return subprocess.run(["git", *args], cwd=repo, check=True,
                                  capture_output=True, text=not binary).stdout

        ordinary_tree = ordinary("ls-tree", "-rz", "--full-tree", original, binary=True)
        ordinary_blob = ordinary("cat-file", "blob", f"{original}:payload", binary=True)
        ordinary_time = ordinary("show", "-s", "--format=%ct", original).strip()
        if ordinary_tree == original_tree or ordinary_blob == original_blob or \
                ordinary_time == original_time:
            errors.append("replacement fixture did not exercise ordinary Git substitution")

    # Separate processes with conflicting locale, timezone, umask, and Git
    # configuration must reconstruct the same candidate bytes.
    with tempfile.TemporaryDirectory(prefix="archive-env-selftest-", dir=base) as td:
        outputs = [Path(td) / "a.tar.gz", Path(td) / "b.tar.gz"]
        variants = [
            ({"LC_ALL": "C", "TZ": "UTC", "GIT_CONFIG_COUNT": "1",
              "GIT_CONFIG_KEY_0": "tar.umask", "GIT_CONFIG_VALUE_0": "0002"}, 0o077),
            ({"LC_ALL": "C.UTF-8", "TZ": "Asia/Tokyo", "GIT_CONFIG_COUNT": "1",
              "GIT_CONFIG_KEY_0": "tar.umask", "GIT_CONFIG_VALUE_0": "0077"}, 0o002),
        ]
        for output, (extra_env, process_umask) in zip(outputs, variants):
            env = {**os.environ, **extra_env, "GIT_CONFIG_NOSYSTEM": "1",
                   "GIT_CONFIG_GLOBAL": "/dev/null"}
            result = subprocess.run(
                [sys.executable, str(Path(__file__).resolve()), "--commit", "HEAD", str(output)],
                cwd=ROOT, env=env, capture_output=True, text=True,
                preexec_fn=lambda mask=process_umask: os.umask(mask))
            if result.returncode:
                errors.append(f"separate-process environment build failed: {result.stderr.strip()}")
        if all(output.exists() for output in outputs) and \
                outputs[0].read_bytes() != outputs[1].read_bytes():
            errors.append("locale/timezone/umask/Git config changed canonical archive bytes")
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
        try:
            errors = (validate(ROOT, args.commit, args.check) +
                      canonical_errors(ROOT, args.commit, args.check))
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            print(f"source-archive: cannot check canonical archive: {error}")
            return 1
        for error in errors:
            print(f"source-archive: {error}")
        return 1 if errors else 0
    if not args.output:
        parser.error("output path required unless --check/--self-test is used")
    try:
        build(ROOT, args.commit, args.output)
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"source-archive: cannot build canonical archive: {error}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
