#!/usr/bin/env python3
"""Doc-symbol checker (RFC 026, reviewer SF-05 long-term option).

Extracts backticked identifiers that look like theorem/lemma names from the
proof documentation and emits a Lean file of `#check` lines. The release
gate compiles that file: a stale theorem name in the docs becomes a build
failure instead of silent drift.

Heuristic for "looks like a theorem name": contains an underscore, starts
lowercase, is a bare identifier or a dotted one (Timer.foo, Mailbox.foo,
WellFormed.foo). Tokens in IGNORE are documentation vocabulary, field
names used in prose, file paths, or operation syntax — not public theorem
references.
"""
import re
import sys

# Strict proof-doc files: every theorem name here must exist in source.
PROOF_DOC_FILES = [
    "docs/proof-index.md",
    "docs/proof-trust-test-matrix.md",
]

# Broader live-doc files: README, guides, examples (excludes historical
# docs that intentionally quote removed names: rfcs/done/, docs/reviews/,
# docs/handoff-*, CHANGELOG.md entries that quote old state).
LIVE_DOC_FILES = [
    "README.md",
    "docs/test-index.md",
    "docs/guided-tour.md",
    "examples/README.md",
]

DOC_FILES = PROOF_DOC_FILES + LIVE_DOC_FILES

# Not theorem references: ops/syntax, fields discussed in prose, files, vocab.
IGNORE = {
    # RFC 033 WellFormed field names (not standalone theorems)
    "occ_fresh", "occ_nodup", "occ_disjoint",
    "nextMsgId", "occurrence",
    # RFC 038 WellFormed field names (not standalone theorems; use WellFormed.X form)
    "owner_spawned", "parent_child_spawned",
    # RFC 035/036 Bridge sub-namespace types/internals — not standalone theorems
    "bridgeState_init", "bridgeState_push0", "bridgeState_pop0", "bridgeState_filter0",
    "bridgeState_readyQ_unchanged", "applyQOp", "applyQOps", "applyQOps_append",
    "WorkerQueues", "WorkerQueues.init", "BridgeState", "QOp", "toQOps", "toQOpsTrace",
    "bridge_stable", "WorkerIdx", "pushWorker0",
    # toQOps direct-effect lemmas (internal; listed in proof-index but not live docs)
    "toQOps_spawn_valid", "toQOps_spawn_invalid",
    "toQOps_spawnChild_valid",
    "toQOps_yield_valid", "toQOps_yield_invalid",
    "toQOps_wake_valid", "toQOps_wake_invalid",
    "toQOps_cancel_valid", "toQOps_cancel_invalid_terminal", "toQOps_cancel_invalid_unspawned",
    "toQOps_send_valid_waiter", "toQOps_send_valid_no_waiter",
    "toQOps_inject_valid_waiter", "toQOps_inject_valid_no_waiter", "toQOps_inject_invalid",
    "toQOps_tick_valid", "toQOps_tick_invalid",
    "toQOps_complete_nil", "toQOps_receive_nil", "toQOps_sleep_nil",
    "toQOps_schedule_nonempty", "toQOps_schedule_empty",
    # operation syntax and grammar tokens
    "send t b m", "receive t", "inject a m", "spawn a", "yield t",
    "complete t", "cancel t", "sleep t deadline", "tick now", "wake t",
    "tick t", "wake_many", "step s op",
    # structures / types / modules / files (checked elsewhere or not theorems)
    "lean_lib", "check-rfcs", "lake build", "lake exe",
    # WellFormed fields referenced in prose (they resolve as projections;
    # checked via the WellFormed. prefix variants below when written dotted)
    "readyQ_nodup", "readyQ_queued", "running_runs", "timers_nodup",
    "timers_sleep", "fresh_none", "timers_sorted", "spawned_has_owner",
    "owned_has_mailbox",
    # value/test vocabulary
    "proof-trust-test-matrix", "assumption-index", "test-index",
    "henret-demo", "check.sh", "axiom_audit.py",
    # Lean tactics mentioned in prose
    "native_decide",
    # WF fields added in RFC 031 (discussed in prose, not theorem names)
    "waiters_waiting", "waiters_owned", "waiting_queued", "waiters_nodup",
    # Mesa-semantics prose tokens
    "mailboxWaiters", "taskState", "readyQ", "mailboxes",
    # version/file tokens that appear in live docs
    "lake_build", "lake_exe", "lake_env",
    # RuntimeState/RuntimeOp field and constructor names used in prose
    "send", "receive", "inject", "taskOwner", "taskState", "taskParent",
    "now", "running", "nextId", "timers",
    # WellFormed fields referenced bare (the dotted WellFormed.X forms are checked)
    "parent_lt", "parent_spawned",
    # Historical name mentioned only in a rename note
    "drivePopB",
    # RFC 035 BridgeState field names (not standalone theorems)
    "queue_eq", "other_empty",
}

NAME_RE = re.compile(r"`([A-Za-z][A-Za-z0-9_.']*)`")


def looks_like_theorem(tok: str) -> bool:
    if tok in IGNORE:
        return False
    if "/" in tok or " " in tok:
        return False
    head = tok.split(".")[-1]
    if "_" not in head:
        return False
    if not head[0].islower():
        return False
    # skip obvious file stems
    if tok.endswith(".md") or tok.endswith(".lean") or tok.endswith(".sh"):
        return False
    return True


def main() -> int:
    names = set()
    for f in DOC_FILES:
        try:
            text = open(f).read()
        except FileNotFoundError:
            print(f"doc-symbol: missing doc file {f}")
            return 1
        for tok in NAME_RE.findall(text):
            tok = tok.rstrip(".")
            if looks_like_theorem(tok):
                names.add(tok)

    lines = [
        "import Henret",
        "import Henret.Native.DequeModel",
        "import Henret.Native.Assumptions",
        "open Henret Henret.Native Henret.Bridge",
        "",
    ]
    for n in sorted(names):
        lines.append(f"#check @{n}")
    out = "\n".join(lines) + "\n"
    sys.stdout.write(out)
    print(f"-- doc-symbol: {len(names)} names extracted", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
