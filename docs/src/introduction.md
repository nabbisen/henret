# Henret

**Executable actor and task runtime models for Lean 4 — a verified semantic
reference, not a runtime library.**

Henret specifies the semantics of a concurrent actor/task scheduler — spawning
tasks, sending messages, parking on an empty mailbox, sleeping until a deadline,
waking when a timer fires, acquiring and releasing resources — and *proves* that
those semantics preserve a 33-field `WellFormed` invariant in every reachable
state, with zero `sorry` and no project-specific axioms.

It is a reference you reason *against*, not a library you link. The model is
executable (`step` / `run`) for testing and exploration, but its value is the
machine-checked guarantees and the explicit trust boundaries, not throughput.

## Three reader paths

- **New users** — start with *What Henret is* and the *Guided tour* to learn the
  model and its profiles.
- **Intermediate users / integrators** — the *Integration contract* says what you
  may depend on; the semantics and *Generated reference* chapters describe the
  operations, state, and proven theorems.
- **Maintainers & contributors** — the proof-engineering chapters (style, API
  stability, dependency budget, ergonomics metrics) and the assurance case
  describe how the corpus is built and kept honest.

## Generated reference

The model tables, public-theorem index, axiom budget, proof-dependency budget,
and RFC index under *Generated reference* are produced from the Lean source and
the audit allowlist by the `scripts/extract_*` and `scripts/*_index` tools, and
are diff-gated by `check.sh` — they cannot drift from the code.
