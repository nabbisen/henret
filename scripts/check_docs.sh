#!/usr/bin/env bash
# RFC 094 — documentation gate (separate from the Lean proof fast gate).
#
# This is intentionally NOT part of scripts/check.sh --fast: mdBook is a Rust
# tool and must not be coupled into the Lean/Lake proof path. Run this on
# documentation/layout PRs and as a release-candidate gate.
#
#   scripts/check_docs.sh
#
# The book targets the mdBook 0.5 line. CI installs the exact checksum-pinned
# policy release (see ci/supply-chain.json); locally, compatible 0.5.x works.
# Requires `mdbook` on PATH (https://rust-lang.github.io/mdBook/).
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== docs gate: structure (orphan + local links) =="
python3 scripts/doc_summary_check.py
python3 scripts/markdown_link_check.py

echo "== docs gate: mdbook build =="
if command -v mdbook >/dev/null 2>&1; then
  echo "mdbook: $(mdbook --version)"
  mdbook build docs >/dev/null
  echo "mdbook: build succeeded (output in docs/book/)"
else
  echo "mdbook: NOT INSTALLED — skipping build (structure checks above still ran)." >&2
  echo "        install mdBook 0.5.x from https://rust-lang.github.io/mdBook/ to verify the build." >&2
  exit 2
fi

echo "== docs gate: all checks passed =="
