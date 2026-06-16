---
rfc: 44
title: Runtime Integration Contract for External Consumers
status: Implemented
implemented_in: v0.12.1
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: integration
---

# RFC 044 — Runtime Integration Contract for External Consumers

**Status.** Implemented (v0.12.1)  
**Target version.** v0.12.0 or earlier if an external project needs Henret  
**Priority.** High for downstream use  
**Track.** Product/API maturity, ecosystem integration  
**Depends on.** Current public model; RFC 036 recommended for bridge users  
**Touches.** docs, examples, import barrels, public theorem index

## Summary

Create a stable integration contract for projects that want to use Henret as a semantic reference model.

This is different from a guided tour. The guided tour teaches Henret. The integration contract tells a downstream runtime, actor framework, or verification project what it may rely on.

## Motivation

Henret has become large enough that downstream users need a precise boundary:

- Which imports are stable?
- Which operations are public semantic surface?
- Which theorems are intended as public guarantees?
- Which modules are examples or internal proof machinery?
- How should external runtime events map to Henret operations?
- What does Mesa semantics require consumers to handle?
- What is explicitly not proved?

Without an integration contract, consumers may depend on internal lemmas or misunderstand model-level claims.

## Proposed document

Create:

```text
docs/integration-contract.md
```

## Required sections

### 1. Project role

State:

```text
Henret is a semantic reference model, not a runtime library.
```

Consumers should use Henret to specify and check behavior, not to execute production workloads.

### 2. Stable imports

Define stability levels:

| Import | Stability | Meaning |
|---|---|---|
| `import Henret.Model` | stable model surface | operations, state, step/run |
| `import Henret.Proofs` | stable theorem surface, names may grow | public safety theorems |
| `import Henret.Refinement` | stable pattern surface | backend contracts |
| `import Henret.Bridge` | experimental until RFC 036 | queue bridge |
| `import Henret.Native.*` | optional/trusted | axiom-bearing native boundary |
| `Henret.Examples.*` | unstable | examples only |

### 3. Operation mapping guide

Provide a table:

| External event | Henret op |
|---|---|
| create root task | `spawn actor` |
| running task creates child | `spawnChild task actor` |
| scheduler selects next task | `schedule` |
| task voluntarily yields | `yield task` |
| task sends message | `send task actor body` |
| external message arrives | `inject actor body` |
| task receives | `receive task` |
| task sleeps | `sleep task deadline` |
| timer advances | `tick now` |
| external direct wake | `wake task` |
| task completes | `complete task` |
| task cancels | `cancel task` |

If cascade cancel or timeout RFCs are implemented, extend this table.

### 4. Mesa semantics contract

State clearly:

- delivery wakes at most one waiter;
- wake does not atomically hand off the message;
- woken task must re-run receive;
- another task may consume the message first;
- no per-message delivery guarantee is implied unless a later theorem states it.

### 5. Occurrence identity contract

Explain:

- every delivered envelope gets a fresh occurrence id;
- equal occurrence ids imply same envelope in the same mailbox in reachable states;
- `send` stamps source actor;
- `inject` stamps `source = none` or the current external-source representation.

### 6. Supervision contract

If RFC 039 is not yet implemented, state:

```text
Parenthood is modeled and acyclic; cascade cancellation and restart policies are not yet part of the stable contract.
```

If RFC 039 is implemented, document `cancelTree`.

### 7. Bridge contract

For `Henret.Bridge`, state:

- current bridge level: single-worker or multi-worker;
- relation type: exact-list or membership;
- which operations are covered;
- which theorem is the headline bridge theorem;
- bridge does not prove native concurrency.

### 8. Theorem contract

List public theorem families:

- `reachable_wf`
- `reachable_queue_exact`
- `reachable_waiters_exact`
- `receive_only_own`
- `reachable_occurrence_unique`
- `reachable_parent_lt`
- bridge headline theorem after RFC 036

Warn consumers not to rely on preservation helper lemmas unless they are listed in the public theorem table.

### 9. Trust boundary

Restate claim classes:

- kernel-proven;
- trusted axioms;
- tested harnesses;
- out-of-scope.

### 10. Versioning policy

Define breaking changes:

- changing `RuntimeOp` constructor signatures;
- changing `RuntimeState` field names/types;
- changing `StepResult` constructors;
- weakening theorem statements;
- moving stable theorem names.

Define non-breaking changes:

- adding new theorems;
- adding new docs;
- adding examples;
- adding stricter internal lemmas;
- proof refactors preserving public theorem names.

## Examples for consumers

Add `examples/integration/` or documented snippets:

1. map a small actor trace to Henret ops;
2. prove the resulting state is well-formed via `reachable_wf`;
3. use `reachable_occurrence_unique`;
4. use bridge theorem if RFC 036 exists.

## Acceptance criteria

- `docs/integration-contract.md` exists.
- Stable imports are listed.
- Public theorem surface is listed.
- Operation mapping table exists.
- Mesa semantics are explained.
- Trust boundary is explicit.
- Example snippets build or are marked pseudocode.
- README links to the integration contract.

## Risks

### Freezing too much too early

The integration contract should identify stability levels. It need not freeze experimental modules such as bridge internals.

### Consumers relying on internals

Document internal namespaces and discourage dependence on helper lemmas that are not public surface.

## Non-goals

- Creating a runtime adapter library.
- Providing FFI bindings.
- Supporting every external runtime architecture.
- Guaranteeing theorem-name permanence for internal proof helpers.
