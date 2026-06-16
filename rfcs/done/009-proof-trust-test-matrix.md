---
rfc: 9
title: Proof/Trust/Test Matrix
status: Implemented
implemented_in: v0.1.0
supersedes: []
superseded_by: []
depends_on: []
blocks: []
category: proofs
---

# RFC-HENRET-009: Proof/Trust/Test Matrix


## Motivation

Henret should make truthfulness a project feature. Users must know what is proven, assumed, tested, and out of scope.

## Required documents

```text
docs/proof-trust-test-matrix.md
docs/proof-index.md
docs/assumption-index.md
docs/test-index.md
```

## Classification

| Class | Meaning |
|---|---|
| PROVEN | Lean kernel checked |
| ASSUMED | Trusted interface or axiom |
| TESTED | Executable test evidence |
| OUTSCOPE | Not claimed |

## Tasks

1. Create matrix.
2. Index all theorems.
3. Index all assumptions.
4. Index all tests.
5. Add PR rule that new claims must update the matrix.

## Acceptance criteria

- A reviewer can audit project claims without reading every source file.
- No native-thread or process-manager claim appears as proven.

## Implementation note (v0.1.0)

docs/proof-trust-test-matrix.md plus proof/assumption/test indexes; PR rule recorded in CONTRIBUTING.md. Zero project-specific assumptions in v0.1.0.
