import Henret
/-!
# Example 02 — Actor Identity and Mailboxes

Concept: each actor has a distinct `ActorId`.  A task is spawned *for* an
actor; the actor's mailbox is created on first spawn and persists across task
completions.  Multiple tasks can share an actor's mailbox.

Run with:  `lake env lean examples/02_actor_mailbox.lean`
-/
open Henret

-- Spawn two tasks for two *different* actors (actors 10 and 20).
def s0 := RuntimeState.init
def s1 := (step s0 (.spawn 10)).1   -- task 0 for actor 10
def s2 := (step s1 (.spawn 20)).1   -- task 1 for actor 20

-- Both actors now have (empty) mailboxes.
#eval s2.mailboxes 10
-- some { messages := [] }
#eval s2.mailboxes 20
-- some { messages := [] }

-- Spawn a second task for actor 10 (actor 10's mailbox already exists).
def s3 := (step s2 (.spawn 10)).1   -- task 2, same actor

#eval s3.mailboxes 10
-- still some { messages := [] }  — mailbox shared, not duplicated

-- Deliver a message to actor 10 from the environment (`inject` is the
-- task-free delivery path; actor-to-actor `send` is task-scoped — see
-- example 04).
def msg : Message := ⟨1, 42⟩
def s4 := (step s3 (.inject 10 msg)).1

#eval s4.mailboxes 10
-- some { messages := [{ occurrence := 0, source := none, body := { id := 1, payload := 42 } }] }
#eval s4.mailboxes 20
-- some { messages := [] }  — actor 20 is unaffected

-- The theorem: injection never touches another actor's mailbox.
#check @Henret.inject_preserves_other
-- b ≠ a → ((step s (.inject a _)).1).mailboxes b = s.mailboxes b

/-! ## Ownership (v0.2.0, RFC 014)

Each spawned task records its owning actor in `taskOwner`. -/

#eval s4.taskOwner 0
-- some 10   — task 0 is owned by actor 10 (set at spawn)

-- The theorems: ownership is set at spawn and immutable thereafter.
#check @Henret.WellFormed.spawned_has_owner
-- reachable_spawned_has_owner: every reachable spawned task has an owner
