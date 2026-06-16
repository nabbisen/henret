import Henret.Proofs.Invariants
import Henret.Proofs.Ownership

/-!
# Henret.Proofs.Resource  (RFC 057)

Reusable lemmas for resource-ledger preservation.

The four resource `WellFormed` fields all reference `taskState`, which most
operations change. The split that makes this tractable:

* **Resource-inert ops** — everything except
  `{complete, cancel, fail, cancelTree, acquire, release, finalize}` — leave
  `resources`/`nextResourceId` unchanged and never move a task from
  non-terminal to terminal. `wf_resource_inert` closes all four fields for
  these, given only that the op preserves non-terminality (`hnt`).
* **Resource-touching ops** are handled individually, with the `markClosingIf`
  shape lemmas below.
-/

namespace Henret

open RuntimeState

/-! ## `markClosingIf` shape lemmas -/

/-- An `allocated` entry in the marked map survives only where it was already
`allocated` and the predicate did not fire. -/
theorem markClosingIf_allocated {p : TaskId → Bool}
    {res : ResourceId → Option ResourceRecord} {r : ResourceId} {o : TaskId}
    (h : markClosingIf p res r = some ⟨o, .allocated⟩) :
    res r = some ⟨o, .allocated⟩ ∧ p o = false := by
  unfold markClosingIf at h
  split at h <;> rename_i heq
  · split at h <;> rename_i hp
    · injection h with h; exact absurd h (by simp)
    · injection h with h1; injection h1 with h2; subst h2; exact ⟨heq, by simpa using hp⟩
  · exact absurd h (heq o)

/-- A `closing` entry came either from an existing `closing` entry, or from a
marked `allocated` entry. -/
theorem markClosingIf_closing {p : TaskId → Bool}
    {res : ResourceId → Option ResourceRecord} {r : ResourceId} {o : TaskId}
    (h : markClosingIf p res r = some ⟨o, .closing⟩) :
    res r = some ⟨o, .closing⟩ ∨ (res r = some ⟨o, .allocated⟩ ∧ p o = true) := by
  unfold markClosingIf at h
  split at h <;> rename_i heq
  · split at h <;> rename_i hp
    · injection h with h1; injection h1 with h2; subst h2; exact Or.inr ⟨heq, hp⟩
    · injection h with h; exact absurd h (by simp)
  · exact Or.inl h

/-- A `released` entry is unchanged by marking. -/
theorem markClosingIf_released {p : TaskId → Bool}
    {res : ResourceId → Option ResourceRecord} {r : ResourceId} {o : TaskId}
    (h : markClosingIf p res r = some ⟨o, .released⟩) :
    res r = some ⟨o, .released⟩ := by
  unfold markClosingIf at h
  split at h <;> rename_i heq
  · split at h <;> rename_i hp <;> (injection h with h; exact absurd h (by simp))
  · exact h

/-- Marking preserves the owner field of every present entry. -/
theorem markClosingIf_owner {p : TaskId → Bool}
    {res : ResourceId → Option ResourceRecord} {r : ResourceId} {rr : ResourceRecord}
    (h : markClosingIf p res r = some rr) :
    ∃ st0, res r = some ⟨rr.owner, st0⟩ := by
  unfold markClosingIf at h
  split at h <;> rename_i heq
  · split at h <;> (injection h with h; subst h; exact ⟨_, heq⟩)
  · exact ⟨rr.state, h⟩

/-- Marking is the identity on a `released` entry. -/
theorem markClosingIf_eq_of_released {p : TaskId → Bool}
    {res : ResourceId → Option ResourceRecord} {r : ResourceId} {rr : ResourceRecord}
    (hrr : res r = some rr) (hrel : rr.state = .released) :
    markClosingIf p res r = res r := by
  unfold markClosingIf; rw [hrr]; obtain ⟨o, st⟩ := rr
  cases st <;> simp_all

/-! ## Inert-operation resource preservation -/

/-- Updating one task to a non-terminal state preserves non-terminality of
every task — the workhorse for `hnt` on messaging operations, which only ever
wake a waiter (`→ .ready`) or park the runner (`→ .waiting`/`.waitingTimed`). -/
theorem upd_nonterminal {ts : TaskMap} {u w : TaskId} {stu target : TaskState}
    (h : ts u = some stu) (hntm : ¬ stu.isTerminal) (htgt : ¬ target.isTerminal) :
    ∃ st', upd ts w (some target) u = some st' ∧ ¬ st'.isTerminal := by
  by_cases huw : u = w
  · subst huw; exact ⟨target, by simp [upd], htgt⟩
  · exact ⟨stu, by simp [upd, huw]; exact h, hntm⟩

/-- For an operation that leaves the resource ledger untouched and never makes
a task terminal (`hnt`), all four resource `WellFormed` fields are preserved.
The owner-spawned and closing-owner-terminal fields follow uniformly from
`step_preserves_spawned` / `step_preserves_terminal`; only non-terminality
(`hnt`) is operation-specific. -/
theorem wf_resource_inert {s : RuntimeState} (h : WellFormed s) (op : RuntimeOp)
    (hres : (step s op).1.resources = s.resources)
    (hnext : (step s op).1.nextResourceId = s.nextResourceId)
    (hnt : ∀ t st, s.taskState t = some st → ¬ st.isTerminal →
        ∃ st', (step s op).1.taskState t = some st' ∧ ¬ st'.isTerminal) :
    (∀ r, r ≥ (step s op).1.nextResourceId → (step s op).1.resources r = none) ∧
    (∀ r rr, (step s op).1.resources r = some rr →
        ∃ st, (step s op).1.taskState rr.owner = some st) ∧
    (∀ r t, (step s op).1.resources r = some ⟨t, .allocated⟩ →
        ∃ st, (step s op).1.taskState t = some st ∧ ¬ st.isTerminal) ∧
    (∀ r t, (step s op).1.resources r = some ⟨t, .closing⟩ →
        ∃ st, (step s op).1.taskState t = some st ∧ st.isTerminal) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr; rw [hres]; exact h.resource_fresh r (by rw [hnext] at hr; exact hr)
  · intro r rr hrr; rw [hres] at hrr
    obtain ⟨st, hst⟩ := h.resource_owner_spawned r rr hrr
    exact step_preserves_spawned hst op
  · intro r t hrt; rw [hres] at hrt
    obtain ⟨st, hst, hnonterm⟩ := h.allocated_owner_nonterminal r t hrt
    exact hnt t st hst hnonterm
  · intro r t hrt; rw [hres] at hrt
    obtain ⟨st, hst, hterm⟩ := h.closing_owner_terminal r t hrt
    exact ⟨st, step_preserves_terminal h hst (by simpa using hterm) op, hterm⟩

/-! ## Terminal-coupling resource preservation -/

/-- The four resource fields are preserved by a terminal transition that marks
every `allocated` resource of a `p`-task `closing`, given that every marked
task is terminal in the new state (`hmarked`) and every unmarked task keeps its
some-ness and terminal classification (`hunmarked`). Closes
`complete`/`cancel`/`fail`/`cancelTree` uniformly (RFC 057). -/
theorem wf_resource_terminal {s s' : RuntimeState} (h : WellFormed s)
    (p : TaskId → Bool)
    (hres : s'.resources = markClosingIf p s.resources)
    (hnext : s'.nextResourceId = s.nextResourceId)
    (hmarked : ∀ u st, p u = true → s.taskState u = some st →
        ∃ st', s'.taskState u = some st' ∧ st'.isTerminal)
    (hunmarked : ∀ u st, p u = false → s.taskState u = some st →
        ∃ st', s'.taskState u = some st' ∧ st'.isTerminal = st.isTerminal) :
    (∀ r, r ≥ s'.nextResourceId → s'.resources r = none) ∧
    (∀ r rr, s'.resources r = some rr → ∃ st, s'.taskState rr.owner = some st) ∧
    (∀ r t, s'.resources r = some ⟨t, .allocated⟩ →
        ∃ st, s'.taskState t = some st ∧ ¬ st.isTerminal) ∧
    (∀ r t, s'.resources r = some ⟨t, .closing⟩ →
        ∃ st, s'.taskState t = some st ∧ st.isTerminal) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr; rw [hres]; rw [hnext] at hr
    exact markClosingIf_none p s.resources r (h.resource_fresh r hr)
  · intro r rr hrr; rw [hres] at hrr
    obtain ⟨st0, hs⟩ := markClosingIf_owner hrr
    obtain ⟨st, hst⟩ := h.resource_owner_spawned r ⟨rr.owner, st0⟩ hs
    by_cases hp : p rr.owner = true
    · obtain ⟨st', hst', _⟩ := hmarked rr.owner st hp hst; exact ⟨st', hst'⟩
    · simp only [Bool.not_eq_true] at hp
      obtain ⟨st', hst', _⟩ := hunmarked rr.owner st hp hst; exact ⟨st', hst'⟩
  · intro r t hrt; rw [hres] at hrt
    obtain ⟨hs, hpt⟩ := markClosingIf_allocated hrt
    obtain ⟨st, hst, hnonterm⟩ := h.allocated_owner_nonterminal r t hs
    obtain ⟨st', hst', hcl⟩ := hunmarked t st hpt hst
    exact ⟨st', hst', by rw [hcl]; exact hnonterm⟩
  · intro r t hrt; rw [hres] at hrt
    rcases markClosingIf_closing hrt with hcl | ⟨hal, hpt⟩
    · obtain ⟨st, hst, hterm⟩ := h.closing_owner_terminal r t hcl
      by_cases hp : p t = true
      · obtain ⟨st', hst', hterm'⟩ := hmarked t st hp hst; exact ⟨st', hst', hterm'⟩
      · simp only [Bool.not_eq_true] at hp
        obtain ⟨st', hst', hcl'⟩ := hunmarked t st hp hst
        exact ⟨st', hst', by rw [hcl']; exact hterm⟩
    · obtain ⟨st, hst, _⟩ := h.allocated_owner_nonterminal r t hal
      obtain ⟨st', hst', hterm'⟩ := hmarked t st hpt hst; exact ⟨st', hst', hterm'⟩

/-! ## Ledger-only operations (acquire / release / finalize) -/

/-- For an operation that changes *only* the resource ledger (`resources`,
`nextResourceId`) and leaves every other field of the state untouched, the 29
non-resource `WellFormed` fields transfer definitionally from `h`; the caller
supplies the four resource fields for the new ledger. -/
theorem wf_resources_only {s : RuntimeState}
    {R : ResourceId → Option ResourceRecord} {N : Nat}
    (h : WellFormed s)
    (h30 : ∀ r, r ≥ N → R r = none)
    (h31 : ∀ r rr, R r = some rr → ∃ st, s.taskState rr.owner = some st)
    (h32 : ∀ r t, R r = some ⟨t, .allocated⟩ → ∃ st, s.taskState t = some st ∧ ¬ st.isTerminal)
    (h33 : ∀ r t, R r = some ⟨t, .closing⟩ → ∃ st, s.taskState t = some st ∧ st.isTerminal) :
    WellFormed { s with resources := R, nextResourceId := N } :=
  ⟨h.readyQ_nodup, h.readyQ_queued, h.running_runs, h.timers_nodup, h.timers_sleep,
   h.fresh_none, h.timers_sorted, h.spawned_has_owner, h.owned_has_mailbox, h.runnable_queued,
   h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, h.parent_lt,
   h.parent_spawned, h.occ_fresh, h.occ_nodup, h.occ_disjoint, h.owner_spawned,
   h.parent_child_spawned, h.timed_has_deadline, h.deadline_is_timed, h.timed_has_timer,
   h.timed_is_waiter, h.timed_waiters_valid, h.timed_waiters_nodup, h.timed_waiters_exclusive,
   h.mailbox_within_capacity, h30, h31, h32, h33⟩

/-- Flipping one present resource to `released` preserves the four resource
fields — shared by `release` (allocated → released) and `finalize`
(closing → released). The released entry can no longer witness the allocated
or closing fields, and all other entries are unchanged. -/
theorem wf_flip_to_released {s : RuntimeState} {r₀ : ResourceId} {o : TaskId}
    {st0 : ResourceState} (h : WellFormed s) (hres : s.resources r₀ = some ⟨o, st0⟩) :
    WellFormed { s with resources := upd s.resources r₀ (some ⟨o, .released⟩) } := by
  refine wf_resources_only h ?_ ?_ ?_ ?_
  · intro r hr
    have hrne : r ≠ r₀ := by
      intro he; rw [he] at hr; rw [h.resource_fresh r₀ hr] at hres; exact absurd hres (by simp)
    rw [upd_ne _ _ hrne]; exact h.resource_fresh r hr
  · intro r rr hrr
    by_cases hrn : r = r₀
    · subst hrn; rw [upd_self] at hrr; injection hrr with hrr; subst hrr
      exact h.resource_owner_spawned r ⟨o, st0⟩ hres
    · rw [upd_ne _ _ hrn] at hrr; exact h.resource_owner_spawned r rr hrr
  · intro r t' hrr
    by_cases hrn : r = r₀
    · subst hrn; rw [upd_self] at hrr; simp at hrr
    · rw [upd_ne _ _ hrn] at hrr; exact h.allocated_owner_nonterminal r t' hrr
  · intro r t' hrr
    by_cases hrn : r = r₀
    · subst hrn; rw [upd_self] at hrr; simp at hrr
    · rw [upd_ne _ _ hrn] at hrr; exact h.closing_owner_terminal r t' hrr

end Henret