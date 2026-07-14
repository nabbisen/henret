#!/usr/bin/env python3
"""Resolve local links in current repository Markdown (RFC 101).

Every tracked or newly added Markdown file is current unless it matches the
explicit historical/generated exclusions below. This fail-open-to-inclusion
policy ensures new live locations enter the gate automatically.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parent.parent
LINK = re.compile(r"(?<!!)\[[^\]]*\]\((?:<([^>]+)>|([^)\s]+))(?:\s+['\"][^)]*['\"])?\)")


EXCLUDED_PREFIXES = (
    ".git-exclude/",       # local tasks, handoffs, and review records
    "docs/reviews/",       # historical review records
    "docs/handoff-",       # historical handoffs
    "docs/src/migration/", # version-scoped historical instructions
    "rfcs/done/",          # immutable implemented design records
    "rfcs/archive/",       # immutable withdrawn/superseded records
)
EXCLUDED_FILES = {"CHANGELOG.md"}  # historical release ledger


def current(path: str) -> bool:
    return path not in EXCLUDED_FILES and not path.startswith(EXCLUDED_PREFIXES)


def markdown_files() -> list[Path]:
    proc = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard",
         "--", "*.md"], cwd=ROOT, capture_output=True, check=True)
    names = sorted({p.decode() for p in proc.stdout.split(b"\0") if p})
    return [ROOT / name for name in names if current(name)]


def inspect_text(path: Path, text: str) -> tuple[list[str], int]:
    errors, links = [], 0
    for line_no, line in enumerate(text.splitlines(), 1):
        for match in LINK.finditer(line):
            target = (match.group(1) or match.group(2)).strip()
            if target.startswith(("http://", "https://", "mailto:", "#")):
                continue
            local = unquote(target.split("#", 1)[0].split("?", 1)[0])
            if not local:
                continue
            links += 1
            if not (path.parent / local).resolve().exists():
                errors.append(f"{path.relative_to(ROOT)}:{line_no}: {target}")
    return errors, links


def self_test() -> int:
    required = ["docs/risk-register.md", "examples/README.md", "rfcs/TEMPLATE.md",
                "future/live/location.md"]
    failures = sum(not current(path) for path in required)
    failures += int(current("docs/handoff-old.md"))
    good, _ = inspect_text(ROOT / "fixture.md", "[ok](README.md)")
    bad, _ = inspect_text(ROOT / "fixture.md", "[bad](definitely-missing.md)")
    failures += int(bool(good)) + int(len(bad) != 1)
    print(f"markdown-link-selftest: scope + positive/negative link fixtures; "
          f"{failures} error(s)")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    errors, links = [], 0
    files = markdown_files()
    for path in files:
        found, count = inspect_text(path, path.read_text())
        errors.extend(found)
        links += count
    for error in errors:
        print(f"ERROR broken local Markdown link: {error}")
    print(f"markdown-link-check: {len(files)} current files, {links} local links, "
          f"{len(errors)} error(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
