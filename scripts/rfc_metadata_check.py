#!/usr/bin/env python3
"""RFC 085 — RFC front-matter linter (stdlib only, no YAML dependency).

Validates the canonical front-matter block on every RFC under
rfcs/{done,proposed,archive}/. Hard errors fail the build; loose slug
correspondence is advisory (RFC 000 requires only a loose match, and
filenames are permanent so they cannot be renamed to satisfy a strict rule).

`depends_on` is authoritative for scheduling. `blocks` is an optional forward
hint, and every declared A-blocks-B edge must be mirrored by B-depends-on-A.

Accepted YAML subset (085-1): scalar strings, integer `rfc`, bare-integer
lists `[80, 84]` / `[]`, `null`; no nested objects, no multiline scalars.
"""
import re
import sys
from pathlib import Path

RFCS = Path("rfcs")
STATUSES = {"Draft", "Proposed", "Implemented", "Withdrawn", "Superseded"}
FOLDER_OK = {
    "done": {"Implemented"},
    "proposed": {"Draft", "Proposed"},
    "archive": {"Withdrawn", "Superseded"},
}
VERSION_RE = re.compile(r"^v\d+\.\d+\.\d+(?:-[0-9A-Za-z.]+)?$")  # 085-3
LIST_RE = re.compile(r"^\[\s*(\d+(?:\s*,\s*\d+)*)?\s*\]$")        # 085-1/2
REQUIRED = ["rfc", "title", "status", "implemented_in",
            "supersedes", "superseded_by", "depends_on", "blocks", "category"]

errors, warnings = [], []


def err(f, msg):
    errors.append(f"{f}: {msg}")


def warn(f, msg):
    warnings.append(f"{f}: {msg}")


def parse_frontmatter(path):
    text = path.read_text()
    if not text.startswith("---\n"):
        return None
    end = text.find("\n---\n", 4)
    if end == -1:
        return None
    fm = {}
    for line in text[4:end].splitlines():
        if not line.strip():
            continue
        if ":" not in line:
            return {"__parse_error__": f"non key:value line: {line!r}"}
        k, _, v = line.partition(":")
        fm[k.strip()] = v.strip()
    return fm


def parse_list(f, key, raw):
    m = LIST_RE.match(raw)
    if not m:
        err(f, f"{key} must be a bare-integer list like [80, 84] or [], got {raw!r}")
        return None
    return [int(x) for x in m.group(1).split(",")] if m.group(1) else []


def slug_tokens(s):
    s = s.lower().replace("&", " and ")
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return [t for t in s.split() if t]


def asymmetric_block_edges(relations):
    bad = []
    for source, (source_file, source_relations) in relations.items():
        for target in source_relations.get("blocks", []):
            target_relations = relations.get(target, ("", {}))[1]
            if source not in target_relations.get("depends_on", []):
                bad.append((source_file, source, target))
    return bad


def self_test():
    good = {1: ("1.md", {"blocks": [2]}),
            2: ("2.md", {"depends_on": [1]})}
    bad = {1: ("1.md", {"blocks": [2]}),
           2: ("2.md", {"depends_on": []})}
    failures = int(bool(asymmetric_block_edges(good))) + \
               int(len(asymmetric_block_edges(bad)) != 1)
    print(f"rfc-metadata-selftest: reciprocal + one-sided fixtures; "
          f"{failures} error(s)")
    return failures


def main():
    if "--self-test" in sys.argv:
        sys.exit(1 if self_test() else 0)
    files = []
    for folder in ("done", "proposed", "archive"):
        d = RFCS / folder
        if d.is_dir():
            files += [(folder, p) for p in sorted(d.glob("[0-9]*.md"))]

    seen = {}                      # rfc number -> file
    relations = {}                 # rfc number -> parsed dependency lists
    all_numbers = set()
    for _, p in files:
        m = re.match(r"(\d+)-", p.name)
        if m:
            all_numbers.add(int(m.group(1)))

    for folder, p in files:
        f = f"{folder}/{p.name}"
        fnum = int(re.match(r"(\d+)-", p.name).group(1))
        fslug = re.match(r"\d+-(.+)\.md$", p.name).group(1)

        fm = parse_frontmatter(p)
        if fm is None:
            err(f, "missing or unterminated YAML front matter")
            continue
        if "__parse_error__" in fm:
            err(f, fm["__parse_error__"])
            continue

        for key in REQUIRED:
            if key not in fm:
                err(f, f"missing required field: {key}")

        # rfc integer + matches filename
        if "rfc" in fm:
            if not re.fullmatch(r"\d+", fm["rfc"]):
                err(f, f"rfc must be a bare integer, got {fm['rfc']!r}")
            else:
                rnum = int(fm["rfc"])
                if rnum != fnum:
                    err(f, f"rfc {rnum} != filename number {fnum}")
                if rnum in seen:
                    err(f, f"duplicate rfc number {rnum} (also {seen[rnum]})")
                seen[rnum] = f

        # title
        if not fm.get("title"):
            err(f, "title is empty")

        # status + folder consistency
        st = fm.get("status")
        if st not in STATUSES:
            err(f, f"status {st!r} not in {sorted(STATUSES)}")
        elif st not in FOLDER_OK[folder]:
            err(f, f"status {st!r} inconsistent with folder {folder}/ "
                   f"(expected one of {sorted(FOLDER_OK[folder])})")

        # implemented_in
        impl = fm.get("implemented_in", "")
        if st == "Implemented":
            if not VERSION_RE.match(impl):
                err(f, f"implemented_in must be vMAJOR.MINOR.PATCH for "
                       f"Implemented, got {impl!r}")
        else:
            if impl != "null":
                err(f, f"implemented_in must be null when status={st}, got {impl!r}")

        # list fields -> bare ints pointing to existing RFCs
        parsed_relations = {}
        for key in ("supersedes", "superseded_by", "depends_on", "blocks"):
            if key in fm:
                lst = parse_list(f, key, fm[key])
                if lst is not None:
                    parsed_relations[key] = lst
                    for n in lst:
                        if n not in all_numbers:
                            err(f, f"{key} references RFC {n} which does not exist")
                        if n == fnum:
                            err(f, f"{key} references itself ({n})")
        relations[fnum] = (f, parsed_relations)

        # loose slug correspondence (advisory; RFC 000 requires only a loose match)
        title = fm.get("title", "")
        if title:
            ftok = set(slug_tokens(fslug))
            ttok = set(slug_tokens(title))
            if ftok:
                overlap = len(ftok & ttok) / len(ftok)
                if overlap < 0.5:
                    warn(f, f"filename slug weakly matches title "
                            f"(overlap {overlap:.0%}): {fslug!r} vs {title!r}")

    for source_file, source, target in asymmetric_block_edges(relations):
        err(source_file, f"blocks RFC {target}, but RFC {target} "
            f"does not declare depends_on RFC {source}")

    for w in warnings:
        print(f"WARN  {w}")
    for e in errors:
        print(f"ERROR {e}")
    print(f"\nrfc-metadata-check: {len(files)} files, "
          f"{len(errors)} errors, {len(warnings)} warnings")
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
