#!/usr/bin/env python3
"""RFC 064 fault-taxonomy consistency gate.

Checks:
  1. All eight taxonomy classes appear in docs/src/fault-taxonomy.md.
  2. The `StepResult` -> class table in the doc matches the Lean `faultClass`
     definition in Henret/Diagnostics/Taxonomy.lean exactly (both directions).
  3. The doc lists every StepResult constructor (no outcome left unclassified).

No fuzzy prose scanning: the gate is a generated-doc-consistency check, so it
cannot drift into false positives.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOC = ROOT / "docs" / "src" / "fault-taxonomy.md"
LEAN = ROOT / "Henret" / "Diagnostics" / "Taxonomy.lean"
RESULT = ROOT / "Henret" / "Core" / "Result.lean"

CLASS_HEADINGS = [
    "Protocol invalidity", "Ordinary waiting", "Cancellation", "Timeout",
    "Task fault", "Supervisor fault", "Runtime adapter failure",
    "Trusted backend failure",
]


def parse_lean_faultclass(text: str) -> dict:
    """ctor -> class from the `def faultClass` match block."""
    m = re.search(r"def faultClass[^\n]*\n((?:\s*\|[^\n]*\n)+)", text)
    if not m:
        sys.exit("fault-taxonomy-check: could not find `def faultClass` block")
    mapping = {}
    for line in m.group(1).splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        lhs, _, rhs = line.partition("=>")
        cls = rhs.strip().lstrip(".").strip()
        for ctor in re.findall(r"\.([a-zA-Z]+)", lhs):
            mapping[ctor] = cls
    return mapping


def parse_doc_table(text: str) -> dict:
    """ctor -> class from the StepResult mapping table."""
    mapping = {}
    for row in re.findall(r"^\|\s*`([a-zA-Z]+)`\s*\|\s*`([a-zA-Z]+)`\s*\|\s*(?:yes|no)\s*\|",
                          text, re.MULTILINE):
        mapping[row[0]] = row[1]
    return mapping


def stepresult_ctors(text: str) -> set:
    return set(re.findall(r"^\s*\|\s*([a-zA-Z]+)\b", text, re.MULTILINE))


def main() -> int:
    doc = DOC.read_text()
    lean = LEAN.read_text()
    result = RESULT.read_text()
    errors = []

    for h in CLASS_HEADINGS:
        if h.lower() not in doc.lower():
            errors.append(f"missing taxonomy class heading: {h!r}")

    lean_map = parse_lean_faultclass(lean)
    doc_map = parse_doc_table(doc)

    # every StepResult constructor is classified in Lean
    ctors = stepresult_ctors(result)
    for c in ctors:
        if c not in lean_map:
            errors.append(f"StepResult.{c} not classified by faultClass")

    # doc table and Lean agree both ways
    for c, cls in lean_map.items():
        if c not in doc_map:
            errors.append(f"doc table missing StepResult.{c}")
        elif doc_map[c] != cls:
            errors.append(f"class mismatch for {c}: lean={cls} doc={doc_map[c]}")
    for c in doc_map:
        if c not in lean_map:
            errors.append(f"doc table has stray StepResult.{c}")

    if errors:
        print("fault-taxonomy-check: FAIL")
        for e in errors:
            print("  -", e)
        return 1
    print(f"fault-taxonomy-check: {len(lean_map)} outcomes classified, "
          f"8 classes documented, doc==code")
    return 0


if __name__ == "__main__":
    sys.exit(main())
