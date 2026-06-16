# Proof API stability

> **Status:** RFC 062 Phase 1 (v0.30.0). Establishes the public-theorem tiers and
> the migration procedure enforced by the theorem-name diff gate.

Henret's downstream consumers — other proofs, `docs/proof-index.md`, the
trust/test matrix, and external reviewers — depend on theorem *names* staying
stable. This document defines which names are public, how they are protected, and
what to do when one must legitimately change.

## Tiers

| Tier | What | Stability | Where checked |
|---|---|---|---|
| **public** | Top-level `theorem`s with a stable public prefix: `preserves_wf_`, `step_preserves_`, `reachable_`, `bridge_`, `run_preserves_`. | Name must not disappear/rename without a recorded migration. | `public_theorem_index.py --check` (gate 7) vs `docs/generated/public-theorems.md`. |
| **audited** | The subset additionally listed in the axiom-audit allowlist (`scripts/axiom_audit.py`). | Name *and* axiom budget fixed. | gate 6 (`axiom_audit.py`) + `extract_theorem_docs.py --check` (gate 7). |
| **internal** | Helper lemmas (`wf_*_pass`, resource helpers), local `have`s, names without a public prefix. | May change freely. | helper-usage gate (RFC 082) checks *use*, not name stability. |
| **generated** | Names emitted into `docs/generated/`. | Regenerated from source; never hand-edited. | the relevant `extract_*.py --check`. |
| **deprecated** | A public name kept as a thin alias/wrapper after its body moved. | Listed below until removed in a documented major step. | snapshot diff + this file. |

The two snapshots are complementary: `public-theorems.md` (this gate) covers the
**prefix-defined** surface — including the per-op `preserves_wf_<op>` theorems
that are *not* individually audited — while `public-theorem-index.md`
(`extract_theorem_docs.py`) covers the **audit-allowlist** surface with its axiom
budgets. A rename of `preserves_wf_sleep` is caught by the former even though it
is not in the latter.

## Migration procedure

A public theorem name may legitimately change (a clearer name, a merge, an
intentional removal once a helper subsumes it). When it does:

1. Prefer keeping the public name. If a helper makes a theorem redundant, keep
   the theorem and let it delegate to the helper — do not delete the name.
2. If a rename is truly warranted, perform it in source, then regenerate:
   `python3 scripts/public_theorem_index.py`. The snapshot diff *is* the
   migration record; commit it together with the source change and note the
   rename in the **Migration log** below.
3. If a public name is intentionally removed, either leave a deprecated alias
   (add it to the **Deprecated aliases** list) or record the removal in the
   **Migration log** with the rationale and the theorem that now carries the
   obligation.
4. Never silence the gate by editing the snapshot without a corresponding source
   change — the snapshot must always be reproducible by the generator.

## Deprecated aliases

_None._ (No public theorem currently survives only as an alias.)

## Migration log

_None yet._ (No public theorem has been renamed or removed since the surface was
first snapshotted in v0.30.0.)
