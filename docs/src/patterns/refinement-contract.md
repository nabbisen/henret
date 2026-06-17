# Pattern: Refinement Contract

The reusable shape (RFC 008):

```text
1. abstract backend contract   -- structure with ops + observation laws
2. pure reference backend      -- laws hold by rfl / small proofs
3. (optional) native backend   -- laws become named ASSUMED axioms
                                  mapped to conformance tests
```

## The contract

```lean
structure MailboxBackend (σ : Type) where
  empty   : σ
  enqueue : σ → Message → σ
  dequeue : σ → Option (Message × σ)
  toList  : σ → List Message
  toList_empty   : toList empty = []
  toList_enqueue : ∀ s m, toList (enqueue s m) = toList s ++ [m]
  toList_dequeue : ∀ s, dequeue s = match toList s with
    | []      => none
    | m :: _  => some (m, ?rest)  -- see Contract.lean for the exact statement
```

The key idea: pick one **observation function** (`toList`) and state every law
through it. Clients written against the contract are correct for *any*
backend satisfying the laws — that is the refinement.

## Applying it to your own component

1. Choose the observation (a list, a multiset, a map).
2. State each operation's effect on the observation.
3. Implement the pure reference backend; the laws should be nearly `rfl`.
4. For a native backend, declare the same laws as named axioms, register them
   in `docs/assumption-index.md`, and write conformance tests that exercise
   each law. Never let an ASSUMED law appear in a PROVEN claim.

Candidate next contracts in Henret: ready-queue contract, timer-queue
contract, scheduler-driver contract.
