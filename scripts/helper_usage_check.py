#!/usr/bin/env python3
"""RFC 082 — helper-usage gate.

Every exported ``wf_*_pass`` helper in ``Henret/Proofs/StepFields.lean`` must
be *used* — its identifier appears, outside StepFields.lean, in a library
``.lean`` source after stripping Lean comments and string literals (082-1, so
a commented-out or quoted occurrence does not count) — or carry a valid
``HENRET_HELPER_RESERVED`` annotation (082-2). The eight A1 helpers must be
USED, never annotated-away. Stdlib only.
"""
import re
import sys
from pathlib import Path

STEPFIELDS = Path("Henret/Proofs/StepFields.lean")

# The RFC 042 helpers the v0.17.0 audit found dead (A1 set). These must be USED.
A1 = {
    "wf_parent_spawned_pass", "wf_occ_pass",
    "wf_timed_has_deadline_pass", "wf_deadline_is_timed_pass",
    "wf_timed_has_timer_pass", "wf_timed_is_waiter_pass",
    "wf_timed_waiters_valid_pass", "wf_timed_waiters_nodup_pass",
}


def strip_lean(src: str) -> str:
    """Remove nested block comments, line comments, and string literals."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        two = src[i:i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1; i += 2; continue
            if two == "-/":
                depth -= 1; i += 2; continue
            i += 1; continue
        if two == "/-":
            depth = 1; i += 2; continue
        if two == "--":
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if src[i] == '"':
            i += 1
            while i < n and src[i] != '"':
                if src[i] == '\\':
                    i += 1
                i += 1
            i += 1; continue
        out.append(src[i]); i += 1
    return "".join(out)


def main() -> None:
    if not STEPFIELDS.exists():
        print(f"FAIL: {STEPFIELDS} not found (run from repo root)")
        sys.exit(1)
    sf = STEPFIELDS.read_text()
    exported = re.findall(r"theorem\s+(wf_\w+_pass)\b", sf)

    # HENRET_HELPER_RESERVED annotation immediately preceding a helper decl.
    reserved = {}
    for m in re.finditer(
            r"HENRET_HELPER_RESERVED:\s*(.*?)\s*-/\s*theorem\s+(wf_\w+_pass)\b",
            sf, re.S):
        reserved[m.group(2)] = m.group(1).strip()

    # Usage corpus: every library .lean except StepFields, comment/string-stripped.
    corpus = "\n".join(
        strip_lean(p.read_text())
        for p in Path("Henret").rglob("*.lean") if p != STEPFIELDS)
    used = {h for h in exported
            if re.search(r"\b" + re.escape(h) + r"\b", corpus)}

    fail = False
    for h in exported:
        if h in used:
            continue
        if h in A1:
            print(f"FAIL: A1 helper {h} is not used "
                  f"(must be used, never annotated-away)")
            fail = True
            continue
        reason = reserved.get(h, "")
        # A valid annotation carries reason; target RFC; expiry condition.
        if reason and reason.count(";") >= 2:
            print(f"  reserved: {h} -- {reason}")
            continue
        if h in reserved:
            print(f"FAIL: helper {h} has a reasonless/malformed "
                  f"HENRET_HELPER_RESERVED annotation (need 'reason; rfc; expiry')")
        else:
            print(f"FAIL: helper {h} is neither used nor "
                  f"HENRET_HELPER_RESERVED-annotated")
        fail = True

    missing_a1 = sorted(A1 - used)
    print(f"helper-usage: {len(exported)} exported wf_*_pass; {len(used)} used; "
          f"A1 used {len(A1 & used)}/{len(A1)}; {len(reserved)} reserved")
    if missing_a1:
        fail = True
    sys.exit(1 if fail else 0)


if __name__ == "__main__":
    main()
