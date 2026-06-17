# Henret documentation

The full documentation is an [mdBook](https://rust-lang.github.io/mdBook/)
under [`src/`](src/SUMMARY.md). Build it locally with:

```bash
mdbook build docs      # output in docs/book/
mdbook serve docs      # live preview
```

Start at [`src/introduction.md`](src/introduction.md). The book is organized by
reader path — new users, integrators, and maintainers/contributors — per
`docs/src/SUMMARY.md`.

Repo-internal documents that are **not** part of the book live alongside this
file: `reviews/` (architect review records), `handoff-*.md` (session handoffs),
`risk-register.md`, and `evidence-ledger.yaml` (machine data; its reader-facing
rendering is `src/evidence-ledger.md`).
