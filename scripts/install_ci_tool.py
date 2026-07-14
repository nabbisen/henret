#!/usr/bin/env python3
"""Install an RFC 104 pinned CI tool after verifying its archive digest."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import shutil
import stat
import sys
import tarfile
import tempfile
import urllib.request
import warnings
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
POLICY = ROOT / "ci" / "supply-chain.json"


def canonical_member(name: str, destination: Path) -> tuple[Path, str]:
    """Return a contained output path and collision key for an archive member."""
    raw = name.rstrip("/")
    parts = raw.split("/")
    if not raw or "\\" in raw or any(part in ("", ".", "..") for part in parts):
        raise ValueError(f"unsafe archive member: {name!r}")
    target = (destination / raw).resolve()
    if target == destination or destination not in target.parents:
        raise ValueError(f"unsafe archive member: {name!r}")
    return target, target.relative_to(destination).as_posix()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def verify_digest(path: Path, expected: str) -> None:
    observed = sha256_file(path)
    if observed != expected:
        raise ValueError(f"SHA-256 mismatch for {path.name}: expected {expected}, "
                         f"observed {observed}")


def safe_extract(archive: Path, destination: Path) -> None:
    destination = destination.resolve()
    with tarfile.open(archive, "r:gz") as bundle:
        names: set[str] = set()
        for member in bundle.getmembers():
            _, canonical = canonical_member(member.name, destination)
            if not (member.isfile() or member.isdir()) or canonical in names:
                raise ValueError(f"unsafe archive member: {member.name!r}")
            names.add(canonical)
        try:
            bundle.extractall(destination, filter="data")
        except TypeError:  # Python < 3.12: the strict pre-scan remains binding.
            bundle.extractall(destination)


def safe_extract_zip(archive: Path, destination: Path) -> None:
    destination = destination.resolve()
    with zipfile.ZipFile(archive) as bundle:
        names: set[str] = set()
        for member in bundle.infolist():
            _, canonical = canonical_member(member.filename, destination)
            mode = member.external_attr >> 16
            kind = stat.S_IFMT(mode)
            supported = member.is_dir() or kind in (0, stat.S_IFREG)
            if not supported or canonical in names:
                raise ValueError(f"unsafe archive member: {member.filename!r}")
            names.add(canonical)
        bundle.extractall(destination)
        for member in bundle.infolist():
            mode = (member.external_attr >> 16) & 0o777
            if mode and not member.is_dir():
                (destination / member.filename).chmod(mode)


def install(tool_name: str, destination: Path) -> Path:
    policy = json.loads(POLICY.read_text())
    try:
        tool = policy["tools"][tool_name]
    except KeyError as exc:
        raise ValueError(f"unknown pinned tool {tool_name!r}") from exc
    destination.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f"henret-{tool_name}-") as td:
        archive_kind = tool.get("archive")
        if archive_kind not in ("tar.gz", "zip"):
            raise ValueError(f"unsupported archive format {archive_kind!r}")
        archive = Path(td) / ("tool.zip" if archive_kind == "zip" else "tool.tar.gz")
        request = urllib.request.Request(
            tool["url"], headers={"User-Agent": "henret-rfc104-installer/1"})
        with urllib.request.urlopen(request, timeout=60) as response, \
                archive.open("wb") as output:
            shutil.copyfileobj(response, output)
        verify_digest(archive, tool["sha256"])
        if archive_kind == "zip":
            safe_extract_zip(archive, destination)
        else:
            safe_extract(archive, destination)
    binary = destination / tool["binary"]
    if not binary.is_file():
        raise ValueError(f"verified archive did not contain {tool['binary']!r}")
    binary.chmod(binary.stat().st_mode | 0o111)
    return binary


def self_test() -> int:
    failures = 0
    with tempfile.TemporaryDirectory(prefix="henret-installer-selftest-") as td:
        root = Path(td)

        def archive(name: str, member: tarfile.TarInfo, data: bytes = b"") -> Path:
            path = root / name
            member.size = len(data)
            with tarfile.open(path, "w:gz") as bundle:
                bundle.addfile(member, io.BytesIO(data) if data else None)
            return path

        valid = archive("valid.tar.gz", tarfile.TarInfo("tool"), b"ok")
        try:
            safe_extract(valid, root / "valid")
            failures += int((root / "valid" / "tool").read_bytes() != b"ok")
        except (OSError, ValueError):
            failures += 1

        traversal = archive("traversal.tar.gz", tarfile.TarInfo("../escape"), b"bad")
        link_info = tarfile.TarInfo("tool-link")
        link_info.type = tarfile.SYMTYPE
        link_info.linkname = "/tmp/outside"
        link = archive("link.tar.gz", link_info)
        for fixture in (traversal, link):
            try:
                safe_extract(fixture, root / fixture.stem)
                failures += 1
            except ValueError:
                pass

        zip_path = root / "duplicate.zip"
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            with zipfile.ZipFile(zip_path, "w") as bundle:
                bundle.writestr("tool", b"one")
                bundle.writestr("tool", b"two")
        try:
            safe_extract_zip(zip_path, root / "duplicate")
            failures += 1
        except ValueError:
            pass
        fifo = tarfile.TarInfo("fifo")
        fifo.type = tarfile.FIFOTYPE
        try:
            safe_extract(archive("fifo.tar.gz", fifo), root / "fifo")
            failures += 1
        except ValueError:
            pass

        tar_alias = root / "tar-alias.tar.gz"
        with tarfile.open(tar_alias, "w:gz") as bundle:
            for name in ("tool", "./tool"):
                info = tarfile.TarInfo(name)
                info.size = 1
                bundle.addfile(info, io.BytesIO(b"x"))
        zip_alias = root / "zip-alias.zip"
        with zipfile.ZipFile(zip_alias, "w") as bundle:
            bundle.writestr("tool", b"one")
            bundle.writestr("a/../tool", b"two")
        for fixture, extractor in ((tar_alias, safe_extract),
                                   (zip_alias, safe_extract_zip)):
            try:
                extractor(fixture, root / f"{fixture.stem}-out")
                failures += 1
            except ValueError:
                pass
    print(f"install-ci-tool-selftest: valid + 6 unsafe archive fixtures; "
          f"{failures} error(s)")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    parser = argparse.ArgumentParser()
    parser.add_argument("tool")
    parser.add_argument("--destination", required=True, type=Path)
    args = parser.parse_args()
    try:
        binary = install(args.tool, args.destination)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"install-ci-tool: FAIL — {exc}")
        return 1
    print(f"install-ci-tool: verified and installed {binary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
