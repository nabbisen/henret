# Henret Roadmap

> Henret is a kernel-checked semantic ledger for execution management:
> every transition is executable, every safety claim is named,
> every trust boundary is explicit, and every bridge to native/runtime
> machinery is scoped by a relation.

## Current version: v0.8.0

19-field `WellFormed` invariant. Actor-scoped send/receive. Parked receive
with mailbox wait queues. Mesa-style wake-one semantics. Actor-scoped child
spawn and parent-chain acyclicity. Message envelope occurrence identity.
Single-worker bridge skeleton (RFC 035).

## Near-term milestones

| Version | RFC(s) | Deliverable |
|---|---|---|
| v0.9.0 | 037 + 036 | Public claim repair + complete single-worker queue-projection bridge |
| v0.9.1 | 038 | Stronger parent/owner exactness invariants |
| v0.10.0 | 039 (+ 042) | Supervision cascade cancel; proof automation as needed |
| v0.11.0 | 040 | Receive timeout and multi-wait semantics |
| v0.11.x | 041 | Selective receive semantics |
| v0.12.0 | 043 + 044 | Multi-worker bridge direction and external integration contract |

## Development layers

### Layer A — Release hygiene and bridge correctness (v0.9.0)

RFC 037 repairs stale public claims identified in the v0.8.0 architect review.
RFC 036 completes the single-worker bridge: correct `toQOps`, all 12 bridge
preservation theorems, a single-step umbrella theorem, and a trace-based headline.

### Layer B — Semantic exactness (v0.9.1 – v0.10.0)

RFC 038 strengthens parenthood and ownership so supervision can be specified
cleanly. RFC 039 adds cascade cancellation — the first real supervision operation.

### Layer C — Advanced actor execution semantics (v0.11.x)

RFC 040 adds timeout-aware receive. RFC 041 adds selective receive.
Both require careful design of multi-waiter state composition.

### Layer D — Proof engineering and consumer maturity (v0.12.0+)

RFC 042 introduces proof automation to keep growing preservation files
maintainable. RFC 043 generalises the bridge to multiple workers.
RFC 044 publishes a stable integration contract for downstream projects.

### Layer E — Sophistication backlog (RFCs 045–079)

Trace semantics, conditional liveness, golden conformance suites, bounded
model exploration, supervision restart policies, observability, release
maturity, extension governance, assurance case, failure taxonomy, semantic
equivalence, replay, state diff, proof governance, bridge certification,
documentation extraction, counterexample pedagogy, verified actor patterns,
security interpretation, and community review.

See `rfcs/README.md` for the full proposed RFC list.

## Do not do yet

- Production native runtime integration until RFC 036 is complete.
- Restart policies before RFC 039 (cascade cancel) is proved.
- Selective receive before RFC 040 (wait/timer composition) is stabilised.
- Task-to-worker assignment in the semantic kernel unless a theorem requires it.
- Multi-worker bridge (RFC 043) before single-worker bridge (RFC 036) is complete.
