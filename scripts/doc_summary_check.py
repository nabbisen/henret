#!/usr/bin/env python3
"""RFC 094 — documentation structure checks (orphan + local links).

Not part of `check.sh --fast` (that path is the Lean proof/model gate). This runs
in the separate docs gate (`scripts/check_docs.sh`). It verifies three things
about the mdBook under `docs/src/`:

1. **SUMMARY targets exist** — every file linked from `docs/src/SUMMARY.md` is a
   real file.
2. **No orphans** — every Markdown file under `docs/src/` (except `SUMMARY.md`
   itself and the explicit exclusions) is reachable from `SUMMARY.md`.
3. **Local links resolve** — every relative Markdown link in any `docs/src/` page
   points at an existing file on disk.

Exit non-zero on any violation.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "docs" / "src"
SUMMARY = SRC / "SUMMARY.md"

LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")

# Files under docs/src/ that are intentionally not listed as their own SUMMARY
# chapter. Keep this list tiny and justified.
ORPHAN_EXCLUDE: set[str] = {
    "SUMMARY.md",  # the table of contents itself
}


def summary_targets() -> list[str]:
    targets = []
    for m in LINK_RE.finditer(SUMMARY.read_text()):
        t = m.group(1).strip()
        if t.startswith(("http://", "https://", "mailto:", "#")):
            continue
        targets.append(t.split("#")[0])
    return targets


def main() -> int:
    errors: list[str] = []

    if not SUMMARY.exists():
        print(f"doc-summary: {SUMMARY} missing", file=sys.stderr)
        return 1

    # (1) SUMMARY targets exist + collect the reachable set.
    reachable: set[str] = set()
    for t in summary_targets():
        resolved = (SUMMARY.parent / t).resolve()
        rel = resolved.relative_to(SRC).as_posix() if SRC in resolved.parents else t
        reachable.add(rel)
        if not resolved.exists():
            errors.append(f"SUMMARY links missing file: {t}")

    # (2) no orphans
    for md in sorted(SRC.rglob("*.md")):
        rel = md.relative_to(SRC).as_posix()
        if rel in ORPHAN_EXCLUDE:
            continue
        if rel not in reachable:
            errors.append(f"orphan (not in SUMMARY): docs/src/{rel}")

    # (3) all local links resolve
    link_count = 0
    for md in sorted(SRC.rglob("*.md")):
        for m in LINK_RE.finditer(md.read_text()):
            t = m.group(1).strip()
            if t.startswith(("http://", "https://", "mailto:", "#")):
                continue
            path = t.split("#")[0].split("?")[0]
            if not path:
                continue
            link_count += 1
            if not (md.parent / path).resolve().exists():
                errors.append(f"broken local link in docs/src/{md.relative_to(SRC).as_posix()}: {t}")

    if errors:
        for e in errors:
            print(f"doc-summary: {e}", file=sys.stderr)
        print(f"doc-summary: {len(errors)} error(s)", file=sys.stderr)
        return 1

    n_md = sum(1 for _ in SRC.rglob("*.md"))
    print(f"doc-summary: {n_md} pages, all reachable from SUMMARY; "
          f"{link_count} local links resolve")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
