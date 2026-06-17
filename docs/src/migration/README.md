# Migration guides

Version-to-version upgrade notes for downstream consumers of the Henret model.
Henret's public *theorem* surface is additive-only (see
[API stability](../proof-api-stability.md)), but the model **grammar**
(`RuntimeOp` / `RuntimeState` / `StepResult` / `TaskState`) grows and
occasionally changes in breaking ways across versions. Each guide below covers
one span: what changed, who needs to act, and exactly what to update — most
often the exhaustive `match` / `cases` over a changed type, which the Lean
compiler flags for you.

Guides are written only for spans where a downstream consumer must act; spans
with no consumer-visible change are intentionally omitted. To author a new
guide, copy the [template](template.md).

## Available guides

- [Template](template.md) — the format for a new guide, plus the historical-count
  convention.
- [v0.14 → v0.15](v0.14-to-v0.15.md)
- [v0.16 → v0.17](v0.16-to-v0.17.md)
- [v0.17 → v0.18](v0.17-to-v0.18.md)
- [v0.18 → v0.19](v0.18-to-v0.19.md)
- [v0.26 → v0.27](v0.26-to-v0.27.md)

## Historical-count convention

Migration guides may cite model counts (constructors, `WellFormed` fields) as
they were at the *source* version. Such numbers are always marked as historical
(for example, "was 29 at v0.33") so that neither the `doc_count_check.py`
stale-count gate — which excludes `docs/src/migration/` — nor a human reader
mistakes them for the current ground truth.
