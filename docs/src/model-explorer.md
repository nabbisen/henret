# Bounded Model Explorer (RFC 048)

A development tool that enumerates small Henret operation sequences,
checks executable property predicates, and shrinks counterexamples by
deletion. It finds missing assumptions, misdocumented semantics, and
regressions before they become proof obligations.

## What it is — and is not

> The explorer is **empirical model-search support, not a proof.**

It lives in the separate `HenretExplore` Lake library, **outside** the
default `import Henret` path, so it never affects the verified model or
its axiom budget. The checkers are bounded *necessary* conditions
evaluated over a finite world — they are deliberately **not** connected
to soundness theorems (which would be false, since `WellFormed` and the
occurrence invariants quantify over infinite domains). Their role is to
confirm the proven invariants over a bounded sample and catch
regressions, never to substitute for `reachable_wf`, `reachable_occurrence_unique`, or `bridge_run_tracks_single_worker`.

## The generator

```lean
structure SmallWorld where
  maxTask  : Nat := 2
  maxActor : Nat := 2
  maxMsg   : Nat := 1
  maxTime  : Nat := 2
```

`genOps w` is a curated subset of `RuntimeOp`s over the bounded domains
(lifecycle, messaging, parking, timers, supervision). `genPrograms w d`
enumerates all sequences up to length `d`. Search grows as
`|genOps|^d`, so defaults are tiny: at the default world, depth 3 is
25,260 programs — tractable; widen only for local exploration.

## Properties

| Property | Meaning |
|---|---|
| `propWellFormed` | bounded structural check: `readyQ` nodup, running task not queued |
| `propOccurrenceUnique w` | occurrence ids across bounded mailboxes are distinct |
| `propBridge` | the single-worker bridge tracks `readyQ` (executable `bridge_run_tracks` content) |
| `propReadyAlwaysEmpty` | **deliberately false** — `readyQ` is always empty (for the shrinker demo) |

## Search and shrinking

```lean
def explore   (w : SmallWorld) (depth : Nat) (p : Property) : Option (List RuntimeOp)
def confirms  (w : SmallWorld) (depth : Nat) (p : Property) : Bool
def shrinkProgram (p : Property) (fuel : Nat) : List RuntimeOp → List RuntimeOp
def findAndShrink (w : SmallWorld) (depth : Nat) (p : Property) : Option (List RuntimeOp)
```

Shrinking is deletion-based: try removing each operation, keep the
removal if the property still fails, repeat to a fixed point.

## Running it

```bash
lake exe henret-explore
```

The RFC 103 release gate executes the same entry point interpreted and records
the canonical release bounds in its retained gate record:

```text
HENRET_EXPLORE_MAX_TASK=2  HENRET_EXPLORE_MAX_ACTOR=2
HENRET_EXPLORE_MAX_MSG=1   HENRET_EXPLORE_MAX_TIME=2
HENRET_EXPLORE_DEPTH=3
```

Standalone local runs may override these environment values. Gate
`test.explorer` fixes them: the v3 verifier rejects shallower or otherwise
different bounds. The gate is bounded and fail-closed. Its manifest record includes
the world/depth parameters, pass result, duration, and stdout hash. This is
current TESTED evidence only; it does not strengthen any claim to PROVEN.

The executable emits exactly one `HENRET_EXPLORER_RESULT` JSON line containing
the actual bounds, program count, three bounded-property outcomes, and the
counterexample/shrinker outcomes. Gate 11 derives its structured manifest
fields from that line. Missing, duplicate, false, or non-canonical output fails
the gate. JSON objects reject duplicate keys at every nesting level, booleans
must be JSON booleans, and integer fields must be JSON integers (so `1` cannot
stand in for `true`, and `true` cannot stand in for `1`). Success also requires
the deliberately false property to shrink to
the deterministic minimal counterexample `[spawn 0]`; the “unexpected” branch
returns nonzero.

Sample output:

```text
world = { maxTask := 2, maxActor := 2, maxMsg := 1, maxTime := 2 }, depth = 3, programs = 25260
Confirming proven invariants over the bounded sample:
  CONFIRMED  well-formedness (bounded structural) holds over all programs up to depth 3
  CONFIRMED  occurrence uniqueness (bounded) holds over all programs up to depth 3
  CONFIRMED  single-worker bridge tracking holds over all programs up to depth 3
Shrinking a deliberately false property (readyQ always empty):
  minimal counterexample: [Henret.RuntimeOp.spawn 0]
All proven invariants confirmed over the bounded sample.
```

The deliberately false property is found and shrunk to the minimal
`[spawn 0]` — a single spawn already populates `readyQ`, so the
"always empty" claim fails on the shortest possible program.

## Scope and risks

Exhaustive search explodes with depth and world size; keep CI runs tiny
and treat larger exploration as a local/nightly activity. The explorer
complements the proofs and the conformance suite — it does not replace
them.
