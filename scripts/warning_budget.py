#!/usr/bin/env python3
"""RFC 086 — warning-budget gate (RFC 080 stage 10).

Parses a build log and enforces a warning budget over the gate's build scope
(086-4: Henret + examples + demo, whatever the gate compiled). Defaults to a
total-warning budget of zero (086-1) and an unused-variable budget of zero,
with an explicit, justified allowlist for any exception.

    warning_budget.py <build.log> [--all-warnings N] [--unused-variables N]
                      [--allow "<substring> | <justification>"] ...

A log produced from a *cached* build contains no warnings (nothing
recompiled); the gate is authoritative on the fresh CI build, consistent with
RFC 080-D. Stdlib only.
"""
import argparse
import re
import sys
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    ap.add_argument("--all-warnings", type=int, default=0)
    ap.add_argument("--unused-variables", type=int, default=0)
    ap.add_argument("--allow", action="append", default=[],
                    help='"<substring> | <justification>" — allow matching warnings')
    args = ap.parse_args()

    p = Path(args.log)
    text = p.read_text(errors="replace") if p.exists() else ""
    # Lean/Lake warnings: "warning: <path>:<l>:<c>: <message>". The follow-up
    # "note: this linter can be disabled..." lines are not counted.
    warns = [w.strip() for w in re.findall(r"^warning:\s*(.+)$", text, re.M)]

    allow_subs = [a.split("|", 1)[0].strip() for a in args.allow if a.split("|", 1)[0].strip()]
    if any("|" not in a for a in args.allow):
        print("FAIL: every --allow entry must carry a justification "
              '("<substring> | <why>") (086-D)')
        sys.exit(1)

    def allowed(w):
        return any(sub in w for sub in allow_subs)

    effective = [w for w in warns if not allowed(w)]
    unused = [w for w in effective if "unused variable" in w]

    print(f"warning-budget: {len(warns)} warning(s) in log; "
          f"{len(effective)} after allowlist ({len(allow_subs)} allow rule(s)); "
          f"{len(unused)} unused-variable")

    ok = True
    if len(unused) > args.unused_variables:
        ok = False
        print(f"FAIL: {len(unused)} unused-variable warning(s) > "
              f"budget {args.unused_variables}")
        for w in unused[:20]:
            print("  ", w)
    if len(effective) > args.all_warnings:
        ok = False
        print(f"FAIL: {len(effective)} total warning(s) > "
              f"budget {args.all_warnings} (086-1)")
        for w in effective[:20]:
            print("  ", w)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
