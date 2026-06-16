---
rfc: 6
title: Message and Wake Semantics
status: Implemented
implemented_in: v0.1.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: model-semantics
---

# RFC-HENRET-006: Message and Wake Semantics


## Motivation

Actor/task systems depend on exact message and wake behavior. These are high-value proof targets.

## Message semantics

`send` should append or enqueue a message to the target actor mailbox.

`receive` should remove exactly one message if available.

Required properties:

- send preserves message identity,
- receive consumes exactly one message,
- receive from empty mailbox is defined,
- messages are not duplicated.

## Wake semantics

`wake task` should move the exact task from sleeping/blocked state to ready state when valid.

Required properties:

- wake does not target the wrong task,
- duplicate wake does not duplicate ready entries,
- wake of completed/cancelled task is harmless or invalid,
- wake preserves global task uniqueness.

## Tasks

1. Implement send.
2. Implement receive.
3. Implement wake.
4. Prove receive consumes one message.
5. Prove send preserves ownership.
6. Prove wake exactness.
7. Prove no duplicate ready task after wake.

## Acceptance criteria

- Message ownership and wake exactness are proven or explicitly classified.
- Examples demonstrate send/receive and wake behavior.

## Implementation note (v0.1.0)

Proven: send_appends, send_preserves_other, receive_consumes_one, receive_length, receive_empty_invalid, wake_exact, wake_sets_ready, wake_twice_invalid (duplicate wake invalid ⇒ no duplicate ready entries).
