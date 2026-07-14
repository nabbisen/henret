#!/usr/bin/env python3
"""Reject executable ``native_decide`` in Git-tracked Lean sources (RFC 100).

Comments and string/character literals are ignored by a small nested-comment
aware lexer. There is intentionally no path-based exception.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOKEN = re.compile(r"\bnative_decide\b")


def executable_text(text: str) -> str:
    out = list(text)
    i, depth, quote = 0, 0, None
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            out[i] = "\n" if text[i] == "\n" else " "
            if pair == "/-":
                out[i:i + 2] = "  "; depth += 1; i += 2; continue
            if pair == "-/":
                out[i:i + 2] = "  "; depth -= 1; i += 2; continue
            i += 1; continue
        if quote:
            out[i] = "\n" if text[i] == "\n" else " "
            if text[i] == "\\" and i + 1 < len(text):
                out[i + 1] = " "; i += 2; continue
            if text[i] == quote:
                quote = None
            i += 1; continue
        if pair == "/-":
            out[i:i + 2] = "  "; depth = 1; i += 2; continue
        if pair == "--":
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end - i); i = end; continue
        # Lean identifiers commonly end in apostrophes (`foo'`), so only
        # double-quoted strings are masked. A valid Char literal cannot contain
        # the multi-character token `native_decide`.
        if text[i] == '"':
            quote = text[i]; out[i] = " "; i += 1; continue
        i += 1
    return "".join(out)


def self_test() -> int:
    hidden = ["-- native_decide", "/- native_decide -/",
              "/- outer /- native_decide -/ -/", '"native_decide"']
    visible = ["example : True := by native_decide",
               "def helper' := by native_decide"]
    errors = [s for s in hidden if TOKEN.search(executable_text(s))]
    errors += [s for s in visible if not TOKEN.search(executable_text(s))]
    print(f"native-decide-selftest: {len(errors)} error(s)")
    return 1 if errors else 0


def tracked_lean_files() -> list[Path]:
    proc = subprocess.run(["git", "ls-files", "-z", "--", "*.lean"],
                          cwd=ROOT, capture_output=True, check=True)
    return [ROOT / p.decode() for p in proc.stdout.split(b"\0") if p]


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    errors = []
    files = tracked_lean_files()
    for path in files:
        clean = executable_text(path.read_text())
        for match in TOKEN.finditer(clean):
            line = clean.count("\n", 0, match.start()) + 1
            errors.append(f"{path.relative_to(ROOT)}:{line}: executable native_decide")
    for error in errors:
        print(f"ERROR {error}")
    print(f"native-decide-check: {len(files)} tracked Lean files, "
          f"{len(errors)} violation(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
