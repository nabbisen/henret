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


def contiguous_count(values, label):
    numbers = sorted(values)
    expected = list(range(1, len(numbers) + 1))
    if numbers != expected:
        raise SystemExit(f"{label} numbering is not contiguous: {numbers}")
    return len(numbers)


GROUND = {
    "runtime_op": count_ctors("Henret/Scheduler/Op.lean", "RuntimeOp"),
    "task_state": count_ctors("Henret/Actor/Task.lean", "TaskState"),
    "step_result": count_ctors("Henret/Core/Result.lean", "StepResult"),
    "wellformed": count_wf_fields("Henret/Proofs/Invariants.lean"),
    "demo_scenario": contiguous_count(
        [int(n) for n in re.findall(r'IO\.println\s+"scenario\s+(\d+):',
                                    (ROOT / "Main.lean").read_text())],
        "demo scenario"),
    "numbered_example": contiguous_count(
        [int(path.name[:2]) for path in (ROOT / "examples").glob("[0-9][0-9]_*.lean")],
        "numbered example"),
}
LABEL = {
    "runtime_op": "RuntimeOp constructors",
    "task_state": "TaskState constructors",
    "step_result": "StepResult constructors",
    "wellformed": "WellFormed fields",
    "demo_scenario": "demo scenarios",
    "numbered_example": "numbered examples",
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
    "demo_scenario": [
        re.compile(r"^\s*(\d+)\s+(?:demo\s+)?scenarios?\b", re.I),
        re.compile(r"\bdemo(?:\s+(?:has|runs|contains|executes))?\s+(\d+)\s+scenarios?\b", re.I),
    ],
    "numbered_example": [
        re.compile(r"(\d+)\s+(?:self-contained\s+|numbered\s+)?examples?\b", re.I),
    ],
}

NUMBER_WORDS = {
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6,
    "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11,
    "twelve": 12, "thirteen": 13, "fourteen": 14, "fifteen": 15,
    "sixteen": 16,
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
    for base in ("docs", "Henret", "examples"):
        for p in (ROOT / base).rglob("*"):
            if p.suffix not in (".md", ".lean"):
                continue
            rel = p.relative_to(ROOT).as_posix()
            if any(rel.startswith(d + "/") or rel == d for d in EXCLUDE_DIR):
                continue
            if p.name.startswith(EXCLUDE_NAME_PREFIX):
                continue
            yield p


def line_mismatches(line):
    # Markdown emphasis/code delimiters are presentation, not a way to hide a
    # current count claim from the gate (RFC 101 regression class).
    normalized = line.replace("`", "").replace("*", "").replace("_", "")
    found = []
    if HIST_CUE.search(normalized):
        return found
    for concept, pats in PAT.items():
        claim_text = normalized
        if concept == "demo_scenario":
            claim_text = re.sub(
                r"\b(" + "|".join(NUMBER_WORDS) + r")(?=\s+(?:demo\s+)?scenarios?\b)",
                lambda match: str(NUMBER_WORDS[match.group(1).lower()]),
                claim_text, flags=re.I)
        elif concept == "numbered_example":
            claim_text = re.sub(
                r"\b(" + "|".join(NUMBER_WORDS) + r")(?=\s+(?:self-contained\s+|numbered\s+)?examples?\b)",
                lambda match: str(NUMBER_WORDS[match.group(1).lower()]),
                claim_text, flags=re.I)
        for pat in pats:
            for match in pat.finditer(claim_text):
                value = int(match.group(1))
                if value != GROUND[concept]:
                    found.append((concept, value, GROUND[concept]))
    return found


def self_test():
    fixtures = [f"**{GROUND['runtime_op'] - 1}-operation grammar**",
                f"`{GROUND['wellformed'] - 1}-field WellFormed`",
                "Nine demo scenarios", "Fifteen self-contained examples"]
    errors = sum(not line_mismatches(line) for line in fixtures)
    print(f"doc-count-selftest: {len(fixtures)} stale count fixtures, "
          f"{errors} error(s)")
    return errors


def main():
    if "--self-test" in sys.argv:
        sys.exit(1 if self_test() else 0)
    print("ground truth:", ", ".join(f"{LABEL[k]}={v}" for k, v in GROUND.items()))
    errors = []
    for path in scan_targets():
        if not path.exists():
            continue
        rel = path.relative_to(ROOT).as_posix()
        for i, line in enumerate(path.read_text().splitlines(), 1):
            for concept, n, truth in line_mismatches(line):
                errors.append((rel, i, concept, n, truth, line.strip()))

    for rel, i, concept, n, truth, text in errors:
        print(f"ERROR {rel}:{i}: claims {n} {LABEL[concept]} but source has "
              f"{truth}\n        | {text[:110]}")
    print(f"\ndoc-count-check: {len(errors)} mismatch(es)")
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
