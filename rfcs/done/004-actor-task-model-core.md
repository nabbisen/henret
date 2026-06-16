---
rfc: 4
title: Actor/Task Model Core
status: Implemented
implemented_in: v0.1.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC-HENRET-004: Actor/Task Model Core


## Motivation

Henret needs a semantic center. Actor/task modeling is the confirmed first domain.

## Design

Define core types:

```lean
abbrev TaskId := Nat
abbrev ActorId := Nat

inductive TaskState where
  | new
  | ready
  | running
  | yielded
  | sleeping
  | completed
  | cancelled
```

Define actor and mailbox state:

```lean
structure Message where
  id      : Nat
  payload : Nat

structure Mailbox where
  messages : List Message

structure ActorState where
  id      : ActorId
  mailbox : Mailbox
```

Define runtime state with explicit ownership locations.

## Invariants

- Completed tasks are terminal.
- Cancelled tasks are terminal.
- A task appears in at most one ownership location.
- A message appears in at most one mailbox or delivery location.

## Tasks

1. Define identifiers.
2. Define task states.
3. Define actor state.
4. Define mailbox.
5. Define runtime state.
6. Define ownership invariants.
7. Prove terminal-state monotonicity.

## Acceptance criteria

- Actor/task lifecycle is explicit.
- Terminal states are proven terminal.
- Mailbox state is represented in Lean, not prose.

## Implementation note (v0.1.0)

Henret/Core/Id.lean, Henret/Actor/{Task,Mailbox}.lean, RuntimeState in Henret/Scheduler/Model.lean. Terminal monotonicity proven unconditionally: step_preserves_terminal, run_preserves_terminal.
