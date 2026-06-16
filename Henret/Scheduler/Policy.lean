import Henret.Scheduler.Model

/-!
# Henret.Scheduler.Policy  (RFC 058)

A policy-parametric scheduling layer that sits **on top of** the core
scheduler without replacing it. A `SchedulingPolicy` is a *sound chooser* over
the ready queue: it may pick which ready task runs next, but it can only ever
pick a task that is actually ready (`choose_sound`). Policy choice changes
ordering, never the set of runnable tasks — so the core safety invariant
`WellFormed.runnable_queued` is independent of policy (proved in
`Henret/Proofs/Policy.lean`).

The derived runner `policyStep` reorders the ready queue so the chosen task is
at the head and then invokes the *unchanged* core `schedule`. This keeps the
core model intact (RFC 058 non-goal: do not replace the core scheduler) and
makes every policy inherit `WellFormed` preservation for free.
-/

namespace Henret

/-- A scheduling policy: a sound chooser over the ready queue. `choose` may
return `none` to abstain (fall back to the queue order). -/
structure SchedulingPolicy where
  /-- Pick the next ready task to run, or abstain. -/
  choose : RuntimeState → Option TaskId
  /-- A chosen task is always actually ready. -/
  choose_sound : ∀ s t, choose s = some t → t ∈ s.readyQ

namespace SchedulingPolicy

/-- Move the policy-chosen ready task to the front of `readyQ` (a permutation
of the queue); leave the state untouched when the policy abstains. -/
def reorder (p : SchedulingPolicy) (s : RuntimeState) : RuntimeState :=
  match p.choose s with
  | some t => { s with readyQ := t :: s.readyQ.erase t }
  | none   => s

end SchedulingPolicy

/-- One policy-directed schedule step: reorder so the chosen task is at the
head, then run the core `schedule`. The core scheduler is unchanged. -/
def policyStep (p : SchedulingPolicy) (s : RuntimeState) : RuntimeState × StepResult :=
  step (p.reorder s) .schedule

/-- **FIFO** — run the oldest ready task (the queue head). This is the policy
that agrees with the core `schedule`. -/
def fifoPolicy : SchedulingPolicy where
  choose s := s.readyQ.head?
  choose_sound := fun _ _ h => List.mem_of_mem_head? h

/-- **LIFO** — run the newest ready task (the queue tail). A second, genuinely
different policy that nonetheless preserves the same safety invariants. -/
def lifoPolicy : SchedulingPolicy where
  choose s := s.readyQ.getLast?
  choose_sound := fun _ _ h => List.mem_of_mem_getLast? h

end Henret
