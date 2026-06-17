# Project Positioning

**One sentence:** Henret is a Lean 4 package for executable actor/task runtime
models, scheduler semantics, refinement patterns, and auditable backend
boundaries.

## Scope and non-goals

| In scope (v0.1.0) | Not claimed |
|---|---|
| Actor/task lifecycle modeling | Production async runtime |
| Executable scheduler semantics (`step`/`run`) | Tokio parity / "Tokio for Lean" |
| Mailbox send/receive semantics | OS process manager |
| Logical-time sleep/tick/wake semantics | Native thread library |
| Kernel-checked lifecycle/ownership/timer proofs | Verified lock-free scheduler |
| Backend refinement contract + reference backend | C race-freedom proofs |
| Proof/trust/test matrix discipline | async/await surface syntax |

## Why this positioning

Lean 4 is often perceived as a mathematics environment. Henret demonstrates
practical systems modeling: behavior as data and pure transitions, executable
reference semantics, proofs where Lean proof is appropriate, tests where it is
not, and an explicit ledger of every trusted boundary. The first ecosystem
value is being a **copyable pattern** for Lean systems work, not a runtime.

## Migration note

Henret supersedes an earlier "lean-runtime-workspace" prototype framed as a
runtime foundation (Lean model + C Chase-Lev deque + typed FFI axioms). The
patterns were reused; the runtime framing and its native-correctness ambitions
were deliberately **not** inherited. See `prior-art-runtime-workspace.md`.
