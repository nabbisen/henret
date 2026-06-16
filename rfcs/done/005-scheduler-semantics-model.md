---
rfc: 5
title: Scheduler Semantics Model
status: Implemented
implemented_in: v0.1.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC-HENRET-005: Scheduler Semantics Model


## Motivation

Henret must model runtime behavior as executable state transitions.

## Design

Define an operation grammar similar to:

```lean
inductive RuntimeOp where
  | spawn     : ActorId -> RuntimeOp
  | schedule  : RuntimeOp
  | yield     : TaskId -> RuntimeOp
  | complete  : TaskId -> RuntimeOp
  | cancel    : TaskId -> RuntimeOp
  | send      : ActorId -> Message -> RuntimeOp
  | receive   : ActorId -> RuntimeOp
  | sleep     : TaskId -> Nat -> RuntimeOp
  | tick      : Nat -> RuntimeOp
  | wake      : TaskId -> RuntimeOp
```

Define:

```lean
def step : RuntimeState -> RuntimeOp -> RuntimeState × StepResult
def run  : RuntimeState -> List RuntimeOp -> RuntimeState
```

## Invalid operations

Invalid operations must be explicit. Choose one of:

1. no-op with `StepResult.invalid`, or
2. error result with unchanged state.

Do not silently mutate state on invalid operations.

## Tasks

1. Define `RuntimeOp`.
2. Define `StepResult`.
3. Implement `step`.
4. Implement `run`.
5. Add ready queue semantics.
6. Add lifecycle transition semantics.
7. Add examples.

## Acceptance criteria

- The model is executable.
- Every operation has documented semantics.
- Invalid operations are testable.

## Implementation note (v0.1.0)

RuntimeOp + StepResult + total executable step/run/runTrace in Henret/Scheduler. Invalid operations return (s, .invalid) — unchanged state by construction; demo regression-tests this.
