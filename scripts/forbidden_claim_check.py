#!/usr/bin/env python3
"""RFC 081 — evidence-ledger validator + forbidden-claim gate.

Three responsibilities (081-4: the gate is a phrase list + allowed-context
patterns + ledger validation, not phrase whack-a-mole):

  1. Validate docs/evidence-ledger.yaml against the closed vocabulary and the
     081-2/081-3 rules (namespaced stable ids; in-tree => verified-here;
     out-of-tree => immutable coordinates or an explicit null posture).
  2. Render the ledger to docs/evidence-ledger.md and verify the committed
     file is in sync (081-1: YAML is the source, .md is generated). Pass
     --generate to (re)write the .md.
  3. Forbidden-claim gate: reject live-doc phrasing that implies this tarball
     verifies the out-of-tree runtime tests, unless an allowed context is
     present or the ledger actually backs the claim (verified_by_ci).

Runs in the RFC 080 doc-consistency gate. Stdlib only.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER_YAML = ROOT / "docs" / "evidence-ledger.yaml"
LEDGER_MD = ROOT / "docs" / "src" / "evidence-ledger.md"

TIERS = {"PROVEN", "TRUSTED", "TESTED", "OUTSCOPE", "PLANNED"}
LOCATIONS = {"in_tree_model_proof", "in_tree_model_test",
             "sibling_runtime_package", "external_artifact", "planned"}
IN_TREE = {"in_tree_model_proof", "in_tree_model_test"}
OUT_OF_TREE = {"sibling_runtime_package", "external_artifact"}

errors = []


def err(m):
    errors.append(m)


# --------------------------------------------------------- stdlib YAML subset
def parse_ledger(text):
    """Parse a list of single-level mappings. Records begin with `- key:`;
    continuation fields are `  key: value`. Values: null/true/false/string."""
    records, cur = [], None
    for raw in text.splitlines():
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        m = re.match(r"-\s+(\w+):\s?(.*)$", raw)
        if m:
            if cur is not None:
                records.append(cur)
            cur = {}
            _set(cur, m.group(1), m.group(2))
            continue
        m = re.match(r"\s+(\w+):\s?(.*)$", raw)
        if m and cur is not None:
            _set(cur, m.group(1), m.group(2))
            continue
        err(f"unparseable ledger line: {raw!r}")
    if cur is not None:
        records.append(cur)
    return records


def _set(rec, key, val):
    v = val.strip()
    if v == "null" or v == "":
        rec[key] = None
    elif v in ("true", "false"):
        rec[key] = (v == "true")
    else:
        rec[key] = v.strip('"')


# ------------------------------------------------------------- schema (081-B)
def validate(records):
    seen = set()
    for r in records:
        cid = r.get("claim_id")
        if not cid:
            err("record missing claim_id")
            continue
        if not re.fullmatch(r"[a-z]+\.[a-z0-9_]+", cid):
            err(f"{cid}: claim_id not lowercase-namespaced (081-3)")
        if cid in seen:
            err(f"{cid}: duplicate claim_id")
        seen.add(cid)
        for f in ("claim", "tier", "evidence_location",
                  "verified_by_this_tarball", "verified_by_ci"):
            if f not in r:
                err(f"{cid}: missing required field {f}")
        tier, loc = r.get("tier"), r.get("evidence_location")
        if tier not in TIERS:
            err(f"{cid}: tier {tier!r} not in closed vocabulary")
        if loc not in LOCATIONS:
            err(f"{cid}: evidence_location {loc!r} not in closed vocabulary")
        vbt, vci = r.get("verified_by_this_tarball"), r.get("verified_by_ci")
        if not isinstance(vbt, bool) or not isinstance(vci, bool):
            err(f"{cid}: verified_by_* must be booleans")
            continue
        # in-tree <=> verified by this tarball
        if loc in IN_TREE and not vbt:
            err(f"{cid}: in-tree location but verified_by_this_tarball=false")
        if loc not in IN_TREE and vbt:
            err(f"{cid}: out-of-tree/planned location but verified_by_this_tarball=true")
        # 081-2: out-of-tree needs coordinates+ci, or an explicit null posture
        if loc in OUT_OF_TREE:
            ext = r.get("external_version") or r.get("external_commit")
            if ext and not vci:
                err(f"{cid}: has external coordinates but verified_by_ci=false")
            if not ext:
                if vci:
                    err(f"{cid}: out-of-tree, no coordinates, but verified_by_ci=true (081-2)")
                if not r.get("notes"):
                    err(f"{cid}: out-of-tree null posture requires a notes line (081-2)")
    return seen


# --------------------------------------------------------------- md rendering
def render_md(records):
    out = ["# Evidence Ledger",
           "",
           "<!-- GENERATED from docs/evidence-ledger.yaml by "
           "scripts/forbidden_claim_check.py. Do not edit by hand (RFC 081). -->",
           "",
           "Each claim records its assurance tier and *where* its evidence "
           "lives. The model-package tarball verifies only `in_tree_*` claims; "
           "`sibling_runtime_package` claims live in the separately versioned "
           "runtime package and are **not** verified by this tarball "
           "(see [`package-boundary.md`](package-boundary.md)).",
           "",
           "| claim_id | tier | location | verified here | claim |",
           "|---|---|---|:---:|---|"]
    for r in records:
        out.append(f"| `{r['claim_id']}` | {r['tier']} | {r['evidence_location']} "
                   f"| {'yes' if r['verified_by_this_tarball'] else 'no'} "
                   f"| {r['claim']} |")
    out.append("")
    return "\n".join(out)


# ------------------------------------------------------- forbidden-claim gate
FORBIDDEN = [
    re.compile(r"this (?:release|tarball|package) verifies runtimeTests", re.I),
    re.compile(r"\bruntimeTests?\s+pass(?:es)?\b", re.I),
    re.compile(r"all runtime tests pass", re.I),
    re.compile(r"runtime (?:harness|tests?) (?:are )?verified by this", re.I),
    re.compile(r"\blinearizability\b.{0,40}\bverified\b", re.I),
]
ALLOWED_CONTEXT = re.compile(
    r"not verified by this|separately versioned|out-of-tree|out of tree|"
    r"sibling|not present in|does not (?:run|verify)|excluded from|"
    r"in a separate package|RFC 081", re.I)

SCAN_DIRS = ("docs",)
SCAN_FILES = ("README.md",)
EXCLUDE = ("docs/reviews", "docs/handoff", "docs/src/evidence-ledger.md")


def scan_targets():
    for f in SCAN_FILES:
        yield ROOT / f
    for d in SCAN_DIRS:
        for p in (ROOT / d).rglob("*.md"):
            rel = p.relative_to(ROOT).as_posix()
            if any(rel.startswith(e) or rel == e for e in EXCLUDE):
                continue
            yield p


def forbidden_gate(records):
    runtime_ci_backed = any(r["evidence_location"] in OUT_OF_TREE
                            and r.get("verified_by_ci") for r in records)
    for p in scan_targets():
        if not p.exists():
            continue
        rel = p.relative_to(ROOT).as_posix()
        for i, line in enumerate(p.read_text().splitlines(), 1):
            for pat in FORBIDDEN:
                if pat.search(line):
                    if ALLOWED_CONTEXT.search(line) or runtime_ci_backed:
                        continue
                    err(f"forbidden claim {rel}:{i}: implies in-tree runtime "
                        f"verification without ledger support / allowed context\n"
                        f"        | {line.strip()[:100]}")


def main():
    text = LEDGER_YAML.read_text()
    records = parse_ledger(text)
    validate(records)
    forbidden_gate(records)

    expected = render_md(records)
    if "--generate" in sys.argv:
        LEDGER_MD.write_text(expected + "\n")
        print(f"wrote {LEDGER_MD.relative_to(ROOT)} ({len(records)} claims)")
        return
    actual = LEDGER_MD.read_text() if LEDGER_MD.exists() else ""
    if actual.rstrip() != expected.rstrip():
        err("docs/src/evidence-ledger.md is out of sync with the YAML "
            "(run: forbidden_claim_check.py --generate)")

    for e in errors:
        print("LEDGER FAIL:", e)
    print(f"evidence-ledger: {len(records)} claims, {len(errors)} error(s)")
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
