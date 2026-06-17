#!/usr/bin/env python3
"""RFC 084 stopgap — doc count check.

Computes the current model counts from the Lean source of truth
(`RuntimeOp` / `TaskState` / `StepResult` constructors and `WellFormed`
fields) and rejects live docs whose *current-claim* count statements
contradict them — the recurring "N operations" / "N-field WellFormed"
drift class.

Lines that narrate a change ("extended from 10 fields", "RFC 039's 21",
"as of v0.11.0", "(v0.x") are historical context and are skipped, as are
the historical files entirely (CHANGELOG, rfcs/, reviews, handoffs,
migration guides) and generated docs (084-3). A precursor to the full
RFC 084 generator; runs in the RFC 080 gate suite (stage 9).
"""
import re
import sys
from pathlib import Path

ROOT = Path(".")

# ---------------------------------------------------------------- ground truth
def _block(text, start_re):
    m = re.search(start_re, text, re.M)
    if not m:
        return None
    rest = text[m.end():]
    end = re.search(r"^(deriving|inductive |structure |def |theorem |lemma |"
                    r"abbrev |namespace |end |@\[)", rest, re.M)
    return rest[: end.start()] if end else rest


def count_ctors(path, name):
    text = (ROOT / path).read_text()
    blk = _block(text, r"^inductive\s+" + re.escape(name) + r"\b")
    if blk is None:
        raise SystemExit(f"cannot find inductive {name} in {path}")
    return len(re.findall(r"^\s*\|\s*[A-Za-z_]\w*", blk, re.M))


def count_wf_fields(path):
    text = (ROOT / path).read_text()
    blk = _block(text, r"^structure\s+WellFormed\b")
    if blk is None:
        raise SystemExit(f"cannot find structure WellFormed in {path}")
    return len(re.findall(r"^  [A-Za-z_]\w*\s*:", blk, re.M))


GROUND = {
    "runtime_op": count_ctors("Henret/Scheduler/Op.lean", "RuntimeOp"),
    "task_state": count_ctors("Henret/Actor/Task.lean", "TaskState"),
    "step_result": count_ctors("Henret/Core/Result.lean", "StepResult"),
    "wellformed": count_wf_fields("Henret/Proofs/Invariants.lean"),
}
LABEL = {
    "runtime_op": "RuntimeOp constructors",
    "task_state": "TaskState constructors",
    "step_result": "StepResult constructors",
    "wellformed": "WellFormed fields",
}

# --------------------------------------------------------------- claim patterns
PAT = {
    "runtime_op": [
        re.compile(r"(\d+)[-\s]operation grammar", re.I),
        re.compile(r"(\d+)\s+RuntimeOps?\b"),
        re.compile(r"(\d+)[-\s]constructor RuntimeOp", re.I),
        re.compile(r"RuntimeOp[^.\n]{0,40}?(\d+)\s+(?:operations|constructors)", re.I),
    ],
    "wellformed": [
        re.compile(r"(\d+)[-\s]field WellFormed", re.I),
        re.compile(r"(\d+)[-\s]field WF\b"),
        re.compile(r"(\d+)\s+WellFormed fields", re.I),
        re.compile(r"WellFormed[^.\n]{0,40}?(\d+)\s+(?:fields|invariant fields)", re.I),
    ],
    "task_state": [
        re.compile(r"(\d+)\s+TaskStates?\b"),
        re.compile(r"TaskState[^.\n]{0,40}?(\d+)\s+(?:constructors|states|cases)", re.I),
    ],
    "step_result": [
        re.compile(r"(\d+)\s+StepResults?\b"),
        re.compile(r"StepResult[^.\n]{0,40}?(\d+)\s+(?:constructors|cases|values)", re.I),
    ],
}

# Lines that narrate a change cite past counts legitimately -> skip.
HIST_CUE = re.compile(
    r"extended (?:from|to)|\+\s*\d+\s+over|RFC\s+0*\d+'s|as of v\d|"
    r"\bwas\b|previously|formerly|earlier|prior\b|grew |up from|"
    r"from \d+ (?:to|field)|history|historical|changelog|\(v\d+\.\d",
    re.I,
)

# Files/dirs that legitimately cite past counts, or are generated.
# docs/src/migration/ is excluded because migration guides intentionally cite
# source-version counts (RFC 094 §9); they must mark such numbers as historical.
EXCLUDE_DIR = ("docs/src/generated", "docs/reviews", "docs/src/migration", "rfcs", ".lake")
EXCLUDE_NAME_PREFIX = ("handoff",)


def scan_targets():
    yield ROOT / "README.md"
    yield ROOT / "Main.lean"
    for base in ("docs", "Henret"):
        for p in (ROOT / base).rglob("*"):
            if p.suffix not in (".md", ".lean"):
                continue
            rel = p.relative_to(ROOT).as_posix()
            if any(rel.startswith(d + "/") or rel == d for d in EXCLUDE_DIR):
                continue
            if p.name.startswith(EXCLUDE_NAME_PREFIX):
                continue
            yield p


def main():
    print("ground truth:", ", ".join(f"{LABEL[k]}={v}" for k, v in GROUND.items()))
    errors = []
    for path in scan_targets():
        if not path.exists():
            continue
        rel = path.relative_to(ROOT).as_posix()
        for i, line in enumerate(path.read_text().splitlines(), 1):
            if HIST_CUE.search(line):
                continue
            for concept, pats in PAT.items():
                truth = GROUND[concept]
                for pat in pats:
                    for m in pat.finditer(line):
                        n = int(m.group(1))
                        if n != truth:
                            errors.append((rel, i, concept, n, truth, line.strip()))

    for rel, i, concept, n, truth, text in errors:
        print(f"ERROR {rel}:{i}: claims {n} {LABEL[concept]} but source has "
              f"{truth}\n        | {text[:110]}")
    print(f"\ndoc-count-check: {len(errors)} mismatch(es)")
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
