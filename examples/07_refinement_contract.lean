import Henret
open Henret
/-!
# Example 07 — Refinement Contract

Concept: the `MailboxBackend` pattern.

A *backend contract* is a `structure` that bundles operations plus
**observation laws** stated through a single `toList` function.  Any
implementation that satisfies the laws is interchangeable.

```text
MailboxBackend σ
  ├── empty   : σ
  ├── enqueue : σ → Message → σ
  ├── dequeue : σ → Option (Message × σ)
  ├── toList  : σ → List Message
  ├── toList_empty   : toList empty = []
  ├── toList_enqueue : ∀ s m, toList (enqueue s m) = toList s ++ [m]
  └── toList_dequeue : (head-removal law)
```

Henret ships two reference implementations, both kernel-proven.

Run with:  `lake env lean examples/07_refinement_contract.lean`
-/

-- The contract type (lives in namespace Henret, module Henret.Refinement.Contract).
#check @MailboxBackend

-- Reference backend 1: bare `List Message`.
#check @listBackend
-- listBackend : MailboxBackend (List Message)

-- Reference backend 2: the `Mailbox` wrapper.
#check @mailboxBackend
-- mailboxBackend : MailboxBackend Mailbox

-- Exercise listBackend manually.
#eval listBackend.toList listBackend.empty
-- []
#eval listBackend.toList (listBackend.enqueue
        (listBackend.enqueue listBackend.empty ⟨1, 10⟩) ⟨2, 20⟩)
-- [{ id := 1, payload := 10 }, { id := 2, payload := 20 }]  (FIFO: enqueue appends)

#eval listBackend.dequeue (listBackend.enqueue
        (listBackend.enqueue listBackend.empty ⟨1, 10⟩) ⟨2, 20⟩)
-- some ({ id := 1, payload := 10 }, [{ id := 2, payload := 20 }])

-- All three laws are kernel-proven fields:
example : listBackend.toList listBackend.empty = [] :=
  listBackend.toList_empty

-- The toList_enqueue law: enqueue always appends.
#check @MailboxBackend.toList_enqueue
-- ∀ {σ} (B : MailboxBackend σ) (s : σ) (m : Message),
--   B.toList (B.enqueue s m) = B.toList s ++ [m]

-- How to copy this pattern for your own component:
-- 1. Choose an observation (a List, a Multiset, a Map …).
-- 2. State every operation's effect through the observation.
-- 3. Implement the reference backend; laws should be `rfl`.
-- 4. Native backends register their laws as named ASSUMED axioms.
--    See docs/patterns/refinement-contract.md.
