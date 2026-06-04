---
title: Examples and Guided Tour
rfc: RFC-HENRET-011
status: Implemented (v0.1.0)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-011: Examples and Guided Tour


## Motivation

Henret should be learnable. Examples are part of the product.

## Example sequence

```text
01_task_lifecycle.lean
02_actor_mailbox.lean
03_spawn_and_schedule.lean
04_send_receive.lean
05_sleep_and_tick.lean
06_cancel_task.lean
07_refinement_contract.lean
08_proof_trust_test_matrix.lean
09_optional_ffi_boundary.lean
```

## Example rules

Each example should:

- teach one concept,
- be short,
- avoid native dependencies unless marked optional,
- include comments,
- link to relevant theorem/doc page.

## Guided tour

Create:

```text
docs/guided-tour.md
examples/README.md
```

## Acceptance criteria

- A new Lean user can run examples in order.
- Examples explain the model before proofs become complex.

## Implementation note (v0.1.0)

Nine self-contained example files in `examples/` (01–09), each teaching one
concept. Example 09 is a documented placeholder for RFC 010 (optional FFI
boundary, still proposed). `examples/README.md` provides the learning-order
index and run instructions. `docs/guided-tour.md` gives narrative context.
