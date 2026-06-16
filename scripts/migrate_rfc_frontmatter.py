#!/usr/bin/env python3
"""RFC 085 — one-shot migration of every RFC to canonical YAML front matter.

Normalizes the three legacy status formats (YAML-ish front matter,
`**Status.**` block, `## Status` header) into a single front-matter block:

    ---
    rfc: <int>
    title: <string>
    status: Draft | Proposed | Implemented | Withdrawn | Superseded
    implemented_in: vX.Y.Z | null
    supersedes: []
    superseded_by: []
    depends_on: []
    blocks: []
    category: <string>
    ---

Folder is the source of truth for status (RFC 000): done/ -> Implemented,
proposed/ -> Proposed, archive/ -> Withdrawn|Superseded. The body is left
untouched (any legacy status prose remains as non-normative human context;
the front matter is authoritative). One-shot; safe to re-run (idempotent on
already-canonical files).
"""
import re
import sys
from pathlib import Path

RFCS = Path("rfcs")
VERSION_RE = re.compile(r"v\d+\.\d+\.\d+(?:-[0-9A-Za-z.]+)?")

# Declared dependency edges for the stabilization wave (RFCs 080-086).
WAVE_DEPS = {
    85: ([], [80, 84]),
    84: ([85], [80]),
    80: ([85, 84], [81, 83, 86]),
    81: ([80], []),
    86: ([80], []),
    83: ([80], []),
    82: ([], []),
}

# Ordered keyword -> category map (first match wins). Soft field for the index.
CATEGORY_RULES = [
    (("positioning", "scope", "identity", "naming", "lean-only", "core package"),
     "foundation"),
    (("refinement",), "refinement"),
    (("invariant", "reachability", "wellformed", "preservation", "proof",
      "axiom", "ergonomics", "completeness", "theorem"), "proofs"),
    (("bridge", "worker"), "bridge"),
    (("conformance", "golden", "explorer", "negative test"), "conformance"),
    (("trace", "observability", "visualization", "replay", "snapshot",
      "diff", "fairness", "liveness"), "observability"),
    (("equivalence", "bisimulation", "fault model"), "theory"),
    (("integration", "adapter", "consumer"), "integration"),
    (("profile", "capability"), "profiles"),
    (("security", "robustness"), "security"),
    (("publication", "community", "counterexample", "patterns"), "pedagogy"),
    (("release", "gate", "ci", "manifest"), "release-process"),
    (("governance", "lifecycle", "metadata", "api stability",
      "dependency budget", "evidence ledger", "package boundary",
      "assurance", "playbook", "review"), "governance"),
    (("module architecture", "dependency graph", "warning", "import"), "tooling"),
    (("ffi", "backend boundary"), "ffi"),
    (("documentation", "doc", "docsite", "guided tour", "examples", "claim",
      "consistency", "extraction", "orientation"), "documentation"),
    (("actor", "task", "scheduler", "message", "wake", "timer", "sleep",
      "receive", "spawn", "waiting", "occurrence", "envelope", "cancellation",
      "shutdown", "restart", "supervision", "selective", "timeout", "mailbox",
      "backpressure", "resource", "deadline", "priority", "scheduling",
      "ownership", "time", "blocked", "semantics", "invalid operation"),
     "model-semantics"),
]


def categorize(title: str) -> str:
    t = title.lower()
    for keys, cat in CATEGORY_RULES:
        for k in keys:
            if re.search(r"\b" + re.escape(k) + r"\b", t):
                return cat
    return "general"


def slugify(title: str) -> str:
    s = title.lower()
    s = s.replace("&", " and ")
    s = re.sub(r"[^a-z0-9]+", "-", s)
    return re.sub(r"-+", "-", s).strip("-")


def parse_existing_frontmatter(text: str):
    """Return (fm_dict, body) if text starts with a --- block, else (None, text)."""
    if not text.startswith("---\n"):
        return None, text
    end = text.find("\n---\n", 4)
    if end == -1:
        return None, text
    block = text[4:end]
    body = text[end + 5:]
    fm = {}
    for line in block.splitlines():
        if ":" in line:
            k, _, v = line.partition(":")
            fm[k.strip()] = v.strip()
    return fm, body


def extract_title_from_h1(body: str):
    for line in body.splitlines():
        m = re.match(r"^#\s+RFC[ -](?:HENRET-)?\d+\s*[—:-]\s*(.+)$", line)
        if m:
            return m.group(1).strip()
    return None


def extract_status_text(body: str):
    # **Status.** <text>
    m = re.search(r"^\*\*Status\.\*\*\s*(.+)$", body, re.MULTILINE)
    if m:
        return m.group(1).strip()
    # ## Status\n\n<text>
    m = re.search(r"^##\s+Status\s*\n+([^\n]+)", body, re.MULTILINE)
    if m:
        return m.group(1).strip()
    return ""


def yaml_quote(s: str) -> str:
    if re.search(r"[:#\[\]{}\",]", s):
        return '"' + s.replace('"', '\\"') + '"'
    return s


def build_frontmatter(num, title, status, impl, deps, blocks, category):
    impl_str = impl if impl else "null"
    return (
        "---\n"
        f"rfc: {num}\n"
        f"title: {yaml_quote(title)}\n"
        f"status: {status}\n"
        f"implemented_in: {impl_str}\n"
        "supersedes: []\n"
        "superseded_by: []\n"
        f"depends_on: {deps}\n"
        f"blocks: {blocks}\n"
        f"category: {category}\n"
        "---\n"
    )


def migrate_file(path: Path, folder: str):
    num = int(re.match(r"(\d+)", path.name).group(1))
    text = path.read_text()
    fm, body = parse_existing_frontmatter(text)

    # Title: prefer existing front-matter title, else H1.
    title = None
    if fm and fm.get("title"):
        title = fm["title"].strip().strip('"')
    if not title:
        title = extract_title_from_h1(body)
    if not title:
        raise SystemExit(f"{path}: cannot determine title")

    # Status text source: front-matter status, else body.
    status_text = (fm.get("status", "") if fm else "") or extract_status_text(body)

    # Canonical status from folder (RFC 000: folder is source of truth).
    if folder == "done":
        status = "Implemented"
    elif folder == "proposed":
        status = "Draft" if status_text.lower().startswith("draft") else "Proposed"
    else:  # archive
        low = status_text.lower()
        status = "Superseded" if "supersed" in low else "Withdrawn"

    # implemented_in only when Implemented; preserve an existing value so the
    # migration is idempotent (status text is clean after the first pass).
    impl = None
    if status == "Implemented":
        existing = fm.get("implemented_in", "").strip() if fm else ""
        if existing and existing.lower() != "null":
            impl = existing
        else:
            m = VERSION_RE.search(status_text)
            impl = m.group(0) if m else None

    deps, blocks = WAVE_DEPS.get(num, ([], []))
    category = categorize(title)

    new_fm = build_frontmatter(num, title, status, impl, deps, blocks, category)

    # For format-1 (already had front matter) the body starts right after the
    # old block; for format-2/3 prepend before the H1 with a blank line.
    if fm is not None:
        new_text = new_fm + body
    else:
        new_text = new_fm + "\n" + body if not body.startswith("\n") else new_fm + body

    path.write_text(new_text)
    return num, status, impl, category


def main():
    changed = 0
    for folder in ("done", "proposed", "archive"):
        d = RFCS / folder
        if not d.is_dir():
            continue
        for path in sorted(d.glob("[0-9]*.md")):
            num, status, impl, cat = migrate_file(path, folder)
            changed += 1
            print(f"  {folder}/{path.name:55s} rfc={num:<3} {status:<11} "
                  f"{impl or '-':<8} [{cat}]")
    print(f"migrated {changed} RFC files")


if __name__ == "__main__":
    main()
