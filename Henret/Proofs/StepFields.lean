import Henret.Proofs.Invariants

namespace Henret

/-!
# Henret.Proofs.StepFields  (RFC 042)

Helper theorems that bundle the most repetitive WellFormed preservation
bullets: the three occurrence-identity fields and the two parent-chain
fields.

## Problem

Each preservation proof contains bullets like:

```lean
  · -- occ_fresh
    intro a mb env hmb henv
    simpa [step, hrt, hts] using h.occ_fresh a mb env hmb henv
  · -- occ_nodup
    intro a mb hmb
    simpa [step, hrt, hts] using h.occ_nodup a mb hmb
  · -- occ_disjoint
    intro a b mba mbb hab hmba hmbb ea hea eb heb
    exact h.occ_disjoint a b mba mbb hab
      (by simpa [step, hrt, hts] using hmba)
      (by simpa [step, hrt, hts] using hmbb) ea hea eb heb
```

These patterns recur in every preservation proof for every operation
that leaves `mailboxes` and `nextMsgId` unchanged (most operations).

## Solution

The helpers below close these bullets in **one line each** given the
stability proofs as parameters:

```lean
  · exact wf_occ_fresh_pass    h hm hn a mb env hmb henv
  · exact wf_occ_nodup_pass    h hm    a mb hmb
  · exact wf_occ_disjoint_pass h hm    a b mba mbb hab hmba hmbb ea hea eb heb hocc
```

where `hm : s'.mailboxes = s.mailboxes` and `hn : s'.nextMsgId = s.nextMsgId`
are proved from the step definition with the relevant guards.

## Usage

```lean
-- At the top of the preservation proof, prove the stable-field equalities:
have hm : (step s (.sleep t d)).1.mailboxes = s.mailboxes := by simp [step, hrt, hts]
have hn : (step s (.sleep t d)).1.nextMsgId = s.nextMsgId := by simp [step, hrt, hts]
have hp : (step s (.sleep t d)).1.taskParent = s.taskParent := by simp [step, hrt, hts]

-- Then the occurrence and hierarchy bullets become one-liners:
· exact wf_occ_fresh_pass    h hm hn a mb env hmb henv
· exact wf_occ_nodup_pass    h hm    a mb hmb
· exact wf_occ_disjoint_pass h hm    a b mba mbb hab hmba hmbb ea hea eb heb hocc
· exact wf_parent_lt_pass    h hp    t p hpar
```

See `docs/proof-engineering.md` for more guidance and the before/after diff.
-/

/-! ## Occurrence-identity pass-through helpers -/

/-- `occ_fresh` holds in `s'` when both `mailboxes` and `nextMsgId`
    equal those of the pre-step state `s`. -/
theorem wf_occ_fresh_pass {s s' : RuntimeState} (h : WellFormed s)
    (hm : s'.mailboxes = s.mailboxes)
    (hn : s'.nextMsgId = s.nextMsgId)
    (a : ActorId) (mb : Mailbox) (env : Envelope)
    (hmb : s'.mailboxes a = some mb)
    (henv : env ∈ mb.messages) :
    env.occurrence < s'.nextMsgId := by
  rw [hm] at hmb; rw [hn]; exact h.occ_fresh a mb env hmb henv

/-- `occ_nodup` holds in `s'` when `mailboxes` equals that of `s`. -/
theorem wf_occ_nodup_pass {s s' : RuntimeState} (h : WellFormed s)
    (hm : s'.mailboxes = s.mailboxes)
    (a : ActorId) (mb : Mailbox)
    (hmb : s'.mailboxes a = some mb) :
    (mb.messages.map Envelope.occurrence).Nodup := by
  rw [hm] at hmb; exact h.occ_nodup a mb hmb

/-- `occ_disjoint` holds in `s'` when `mailboxes` equals that of `s`. -/
theorem wf_occ_disjoint_pass {s s' : RuntimeState} (h : WellFormed s)
    (hm : s'.mailboxes = s.mailboxes)
    (a b : ActorId) (mba mbb : Mailbox)
    (hab : a ≠ b)
    (hmba : s'.mailboxes a = some mba)
    (hmbb : s'.mailboxes b = some mbb)
    (ea : Envelope) (hea : ea ∈ mba.messages)
    (eb : Envelope) (heb : eb ∈ mbb.messages) :
    ea.occurrence ≠ eb.occurrence := by
  rw [hm] at hmba hmbb
  exact h.occ_disjoint a b mba mbb hab hmba hmbb ea hea eb heb

/-! ## Parent-chain pass-through helpers -/

/-- `parent_lt` holds in `s'` when `taskParent` equals that of `s`. -/
theorem wf_parent_lt_pass {s s' : RuntimeState} (h : WellFormed s)
    (hp : s'.taskParent = s.taskParent)
    (t p : TaskId)
    (hpar : s'.taskParent t = some p) : p < t := by
  rw [hp] at hpar; exact h.parent_lt t p hpar

/-- `parent_spawned` holds in `s'` when `taskParent` equals that of `s`
    and spawned tasks remain spawned (i.e. `step_preserves_spawned` holds). -/
theorem wf_parent_spawned_pass {s s' : RuntimeState} (h : WellFormed s)
    (hp : s'.taskParent = s.taskParent)
    (hsp : ∀ t, (∃ st, s.taskState t = some st) → ∃ st', s'.taskState t = some st')
    (t p : TaskId)
    (hpar : s'.taskParent t = some p) :
    ∃ st, s'.taskState p = some st := by
  rw [hp] at hpar
  obtain ⟨st, hst⟩ := h.parent_spawned t p hpar
  exact hsp p ⟨st, hst⟩

/-! ## Combined all-occ helper

Proves all three occurrence bullets at once and returns them as a triple.
Useful when you want to handle occ_fresh, occ_nodup, occ_disjoint in one step. -/

structure OccFields (s : RuntimeState) : Prop where
  fresh    : ∀ a mb env, s.mailboxes a = some mb → env ∈ mb.messages →
               env.occurrence < s.nextMsgId
  nodup    : ∀ a mb, s.mailboxes a = some mb →
               (mb.messages.map Envelope.occurrence).Nodup
  disjoint : ∀ a b mba mbb, a ≠ b → s.mailboxes a = some mba →
               s.mailboxes b = some mbb →
               ∀ ea ∈ mba.messages, ∀ eb ∈ mbb.messages,
               ea.occurrence ≠ eb.occurrence

/-- All three occurrence fields transfer from `s` to `s'` when mailboxes
    and nextMsgId are unchanged. -/
theorem wf_occ_pass {s s' : RuntimeState} (h : WellFormed s)
    (hm : s'.mailboxes = s.mailboxes)
    (hn : s'.nextMsgId = s.nextMsgId) :
    OccFields s' :=
  { fresh    := fun a mb env hmb henv => wf_occ_fresh_pass h hm hn a mb env hmb henv
    nodup    := fun a mb hmb => wf_occ_nodup_pass h hm a mb hmb
    disjoint := fun a b mba mbb hab hmba hmbb ea hea eb heb =>
                  wf_occ_disjoint_pass h hm a b mba mbb hab hmba hmbb ea hea eb heb }

end Henret

/-! ## Timed-wait pass-through helpers (RFC 040)

These close the six new WellFormed fields (22-27) for operations that
leave `waitDeadline`, `timers`, and `timedMailboxWaiters` unchanged.
Each helper takes pointwise stability proofs (from `by simp [step, guards]`). -/

namespace Henret

/-- `timed_has_deadline` holds when `waitDeadline` and `taskState` are pointwise-stable. -/
theorem wf_timed_has_deadline_pass {s s' : RuntimeState} (h : WellFormed s)
    (hwd : ∀ u, s'.waitDeadline u = s.waitDeadline u)
    (hts : ∀ u, s'.taskState u = s.taskState u)
    (t : TaskId) (ht : s'.taskState t = some .waitingTimed) :
    ∃ d, s'.waitDeadline t = some d := by
  rw [hwd]; exact h.timed_has_deadline t (by rw [← hts]; exact ht)

/-- `deadline_is_timed` holds when `waitDeadline` and `taskState` are pointwise-stable. -/
theorem wf_deadline_is_timed_pass {s s' : RuntimeState} (h : WellFormed s)
    (hwd : ∀ u, s'.waitDeadline u = s.waitDeadline u)
    (hts : ∀ u, s'.taskState u = s.taskState u)
    (t : TaskId) (d : Nat) (hd : s'.waitDeadline t = some d) :
    s'.taskState t = some .waitingTimed := by
  rw [hts]; exact h.deadline_is_timed t d (by rw [← hwd]; exact hd)

/-- `timed_has_timer` holds when `timers` and `taskState` are stable. -/
theorem wf_timed_has_timer_pass {s s' : RuntimeState} (h : WellFormed s)
    (htm : s'.timers = s.timers)
    (hts : ∀ u, s'.taskState u = s.taskState u)
    (t : TaskId) (ht : s'.taskState t = some .waitingTimed) :
    ∃ e ∈ s'.timers, e.task = t := by
  rw [htm]
  exact h.timed_has_timer t (by rw [← hts]; exact ht)

/-- `timed_is_waiter` holds when `timedMailboxWaiters` and `taskState` are stable. -/
theorem wf_timed_is_waiter_pass {s s' : RuntimeState} (h : WellFormed s)
    (htw : ∀ a, s'.timedMailboxWaiters a = s.timedMailboxWaiters a)
    (hts : ∀ u, s'.taskState u = s.taskState u)
    (t : TaskId) (ht : s'.taskState t = some .waitingTimed) :
    ∃ a, t ∈ s'.timedMailboxWaiters a := by
  obtain ⟨a, ha⟩ := h.timed_is_waiter t (by rw [← hts]; exact ht)
  exact ⟨a, by rw [htw]; exact ha⟩

/-- `timed_waiters_valid` holds when `timedMailboxWaiters` and `taskState` are stable. -/
theorem wf_timed_waiters_valid_pass {s s' : RuntimeState} (h : WellFormed s)
    (htw : ∀ a, s'.timedMailboxWaiters a = s.timedMailboxWaiters a)
    (hts : ∀ u, s'.taskState u = s.taskState u)
    (a : ActorId) (t : TaskId) (ht : t ∈ s'.timedMailboxWaiters a) :
    s'.taskState t = some .waitingTimed := by
  rw [hts]; exact h.timed_waiters_valid a t (by rw [← htw]; exact ht)

/-- `timed_waiters_nodup` holds when `timedMailboxWaiters` is stable. -/
theorem wf_timed_waiters_nodup_pass {s s' : RuntimeState} (h : WellFormed s)
    (htw : ∀ a, s'.timedMailboxWaiters a = s.timedMailboxWaiters a)
    (a : ActorId) : (s'.timedMailboxWaiters a).Nodup := by
  rw [htw]; exact h.timed_waiters_nodup a

/-- `mailbox_within_capacity` (RFC 056) reads only the mailbox policy and the
mailbox contents. Any step that leaves both `mailboxPolicy` and `mailboxes`
pointwise-stable preserves it verbatim — used by every operation that touches
neither (the time and metadata operations). Introduced as the RFC 062 Phase 1
pilot extraction: the three time blocks (`sleep`/`tick`/`wake`) previously
discharged this field with the same five lines apiece. -/
theorem wf_mailbox_capacity_pass {s s' : RuntimeState} (h : WellFormed s)
    (hpol : ∀ a, s'.mailboxPolicy a = s.mailboxPolicy a)
    (hmb : ∀ a, s'.mailboxes a = s.mailboxes a)
    (a : ActorId) (n : Nat) (mb : Mailbox)
    (hcap : (s'.mailboxPolicy a).capacity = some n)
    (hmbx : s'.mailboxes a = some mb) :
    mb.messages.length ≤ n := by
  rw [hpol] at hcap; rw [hmb] at hmbx
  exact h.mailbox_within_capacity a n mb hcap hmbx
end Henret