---
title: Refinement Patterns
rfc: RFC-HENRET-008
status: Implemented (v0.1.0)
project: Henret
package: henret
namespace: Henret
---

# RFC-HENRET-008: Refinement Patterns


## Motivation

Henret's ecosystem value is not only the actor/task model. It should teach how to connect executable models to backend contracts.

## Design

Define a pattern:

```text
abstract backend contract
pure reference backend
proof reference backend satisfies contract
optional native backend declared as trusted/tested
```

Candidate contracts:

- queue contract,
- mailbox contract,
- timer queue contract,
- scheduler-driver contract.

## Tasks

1. Define first backend contract.
2. Provide pure reference backend.
3. Prove reference backend satisfies contract.
4. Show how runtime model uses the contract parametrically.
5. Write `docs/patterns/refinement-contract.md`.

## Acceptance criteria

- A user can copy the pattern for a new backend.
- Native backends are not required to understand the pattern.

## Implementation note (v0.1.0)

MailboxBackend contract (Henret/Refinement/Contract.lean) with toList observation laws; listBackend and mailboxBackend reference backends proven; pattern doc at docs/patterns/refinement-contract.md.
