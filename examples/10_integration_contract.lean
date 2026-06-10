import Henret
/-!
# Example 10 — Integration Contract for External Consumers (RFC 044)

This example is written from a **downstream consumer's** point of view.
It shows the integration pattern described in `docs/integration-contract.md`:

  1. map a small external actor trace to Henret ops;
  2. run the trace from the initial state;
  3. discharge the public guarantees `reachable_wf` and
     `reachable_occurrence_unique` on the resulting state.

A consumer imports only `Henret` (which re-exports the stable
`Henret.Model` and `Henret.Proofs` surfaces) and depends only on the
public theorem names listed in the integration contract §8.

Run with:  `lake env lean examples/10_integration_contract.lean`
-/
open Henret

/-! ## 1. Map an external actor scenario to Henret ops

Scenario (as a downstream runtime might log it):

  - create two root actors A (id 7) and B (id 9), each with one task;
  - the scheduler picks the first task to run;
  - A's task sends a message to B and one to itself;
  - the environment injects a message into A;
  - A's task receives its own actor's head message. -/
def consumerTrace : List RuntimeOp :=
  [ .spawn 7,              -- create root task 0, owner actor 7 (A)
    .spawn 9,              -- create root task 1, owner actor 9 (B)
    .schedule,             -- scheduler selects task 0
    .send 0 9 ⟨1, 100⟩,    -- A's task → B
    .send 0 7 ⟨2, 200⟩,    -- A's task → its own actor
    .inject 7 ⟨3, 300⟩,    -- environment → A
    .receive 0 ]           -- A's task receives its head envelope

/-! ## 2. Run the trace -/
def finalState : RuntimeState := run RuntimeState.init consumerTrace

#eval (finalState.mailboxes 9).map (·.messages)
-- B (actor 9) holds the one message A sent it.
#eval (finalState.mailboxes 7).map (·.messages)
-- A (actor 7) holds the injected message; its own head was received.

/-! ## 3. Discharge the public guarantees

A consumer relies only on the public theorem families (contract §8).
Both of these hold for **any** op sequence, so they apply to
`consumerTrace` with no side conditions. -/

-- PUBLIC GUARANTEE: the resulting state is well-formed (all 28 invariant
-- fields), purely because it is reachable.
example : WellFormed finalState :=
  reachable_wf consumerTrace

-- PUBLIC GUARANTEE: occurrence ids are globally unique in the resulting
-- state — if two envelopes (in possibly different mailboxes) share an
-- occurrence id, they are the same envelope in the same mailbox.
example {a b : ActorId} {mba mbb : Mailbox}
    (hmba : finalState.mailboxes a = some mba)
    (hmbb : finalState.mailboxes b = some mbb)
    {ea eb : Envelope}
    (hea : ea ∈ mba.messages) (heb : eb ∈ mbb.messages)
    (hocc : ea.occurrence = eb.occurrence) :
    a = b ∧ ea = eb :=
  reachable_occurrence_unique consumerTrace hmba hmbb hea heb hocc

/-! ## What a consumer must NOT do

A consumer must not depend on internal helper lemmas. For instance
`preserves_wf_receive`, `toQOps_send_valid_waiter`, or any `step_*`
projection lemma are proof machinery whose names may change between
releases. Only the names in the contract's public theorem table are
stable. -/

#check @reachable_wf
#check @reachable_occurrence_unique
#check @reachable_queue_exact
#check @receive_only_own
