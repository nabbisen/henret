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

/-! ## Actor existence is monotone (RFC 091)

No operation removes a mailbox: every writer either keeps `s.mailboxes` or
updates a slot to `some _` (`spawn` lazily creates an empty mailbox; `send`,
`inject`, and the `receive` family rewrite contents). Hence `ActorExists` —
the witness `OwnerValid`/`OwnerLive`/`OwnerClosed` use for actor owners — is
preserved by every op. -/
theorem step_preserves_actor_exists {s : RuntimeState} (a : ActorId) (op : RuntimeOp)
    (h : ActorExists s a) : ActorExists (step s op).1 a := by
  obtain ⟨mb0, hmb0⟩ := h
  have keep : ∀ {x : ActorId} {y : Mailbox},
      ∃ mb, upd s.mailboxes x (some y) a = some mb := by
    intro x y; by_cases hax : a = x
    · subst hax; exact ⟨y, by simp [upd]⟩
    · exact ⟨mb0, by rw [upd_ne _ _ hax]; exact hmb0⟩
  cases op <;>
    simp only [step, ActorExists] <;>
    (repeat' split) <;>
    first
      | exact ⟨mb0, hmb0⟩
      | exact keep
      | (first
          | exact ⟨mb0, hmb0⟩
          | exact keep)

/-! ## `markClosingIfOwner` shape lemmas (RFC 091, owner-generic) -/

/-- An `allocated` entry in the marked map survives only where it was already
`allocated` and the predicate did not fire. -/
theorem markClosingIfOwner_allocated {p : ResourceOwner → Bool}
    {res : ResourceId → Option ResourceRecord} {r : ResourceId} {o : ResourceOwner}
    (h : markClosingIfOwner p res r = some ⟨o, .allocated⟩) :
    res r = some ⟨o, .allocated⟩ ∧ p o = false := by
  unfold markClosingIfOwner at h
  split at h <;> rename_i heq
  · split at h <;> rename_i hp
    · injection h with h; exact absurd h (by simp)
    · injection h with h1; injection h1 with h2; subst h2; exact ⟨heq, by simpa using hp⟩
  · exact absurd h (heq o)

/-- A `closing` entry came either from an existing `closing` entry, or from a
marked `allocated` entry. -/
theorem markClosingIfOwner_closing {p : ResourceOwner → Bool}
    {res : ResourceId → Option ResourceRecord} {r : ResourceId} {o : ResourceOwner}
    (h : markClosingIfOwner p res r = some ⟨o, .closing⟩) :
    res r = some ⟨o, .closing⟩ ∨ (res r = some ⟨o, .allocated⟩ ∧ p o = true) := by
  unfold markClosingIfOwner at h
  split at h <;> rename_i heq
  · split at h <;> rename_i hp
    · injection h with h1; injection h1 with h2; subst h2; exact Or.inr ⟨heq, hp⟩
    · injection h with h; exact absurd h (by simp)
  · exact Or.inl h

/-- Marking preserves the owner field of every present entry. -/
theorem markClosingIfOwner_owner {p : ResourceOwner → Bool}
    {res : ResourceId → Option ResourceRecord} {r : ResourceId} {rr : ResourceRecord}
    (h : markClosingIfOwner p res r = some rr) :
    ∃ st0, res r = some ⟨rr.owner, st0⟩ := by
  unfold markClosingIfOwner at h
  split at h <;> rename_i heq
  · split at h <;> (injection h with h; subst h; exact ⟨_, heq⟩)
  · exact ⟨rr.state, h⟩

/-- Marking is the identity on a `released` entry (any predicate). -/
theorem markClosingIfOwner_eq_of_released {p : ResourceOwner → Bool}
    {res : ResourceId → Option ResourceRecord} {r : ResourceId} {rr : ResourceRecord}
    (hrr : res r = some rr) (hrel : rr.state = .released) :
    markClosingIfOwner p res r = res r := by
  unfold markClosingIfOwner; rw [hrr]; obtain ⟨o, st⟩ := rr
  cases st <;> simp_all

/-- RFC 057 compat: `markClosingIf` (task wrapper) is the identity on released. -/
theorem markClosingIf_eq_of_released {p : TaskId → Bool}
    {res : ResourceId → Option ResourceRecord} {r : ResourceId} {rr : ResourceRecord}
    (hrr : res r = some rr) (hrel : rr.state = .released) :
    markClosingIf p res r = res r :=
  markClosingIfOwner_eq_of_released hrr hrel

/-- RFC 091: `markActorResourcesClosing` is the identity on released entries. -/
theorem markActorResourcesClosing_eq_of_released {a : ActorId}
    {res : ResourceId → Option ResourceRecord} {r : ResourceId} {rr : ResourceRecord}
    (hrr : res r = some rr) (hrel : rr.state = .released) :
    markActorResourcesClosing a res r = res r :=
  markClosingIfOwner_eq_of_released hrr hrel

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

/-- For an operation that leaves the resource ledger untouched, keeps
`actorStatus` fixed (`hstat`), and never makes a task terminal (`hnt`), the
four owner-generic resource `WellFormed` obligations are preserved. Task owners
follow from `step_preserves_spawned`/`step_preserves_terminal`+`hnt`; actor
owners follow from `step_preserves_actor_exists`+`hstat` (RFC 057/091). -/
theorem wf_resource_inert {s : RuntimeState} (h : WellFormed s) (op : RuntimeOp)
    (hres : (step s op).1.resources = s.resources)
    (hnext : (step s op).1.nextResourceId = s.nextResourceId)
    (hstat : (step s op).1.actorStatus = s.actorStatus)
    (hnt : ∀ t st, s.taskState t = some st → ¬ st.isTerminal →
        ∃ st', (step s op).1.taskState t = some st' ∧ ¬ st'.isTerminal) :
    (∀ r, r ≥ (step s op).1.nextResourceId → (step s op).1.resources r = none) ∧
    (∀ r rr, (step s op).1.resources r = some rr → OwnerValid (step s op).1 rr.owner) ∧
    (∀ r rr, (step s op).1.resources r = some rr → rr.state = .allocated →
        OwnerLive (step s op).1 rr.owner) ∧
    (∀ r rr, (step s op).1.resources r = some rr → rr.state = .closing →
        OwnerClosed (step s op).1 rr.owner) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr; rw [hres]; exact h.resource_fresh r (by rw [hnext] at hr; exact hr)
  · intro r rr hrr; rw [hres] at hrr
    have hv := h.resource_owner_valid r rr hrr
    cases ho : rr.owner with
    | task t =>
      rw [ho] at hv; simp only [OwnerValid] at hv ⊢
      obtain ⟨st, hst⟩ := hv; exact step_preserves_spawned hst op
    | actor a =>
      rw [ho] at hv; simp only [OwnerValid] at hv ⊢
      exact step_preserves_actor_exists a op hv
  · intro r rr hrr hal; rw [hres] at hrr
    have hl := h.allocated_owner_live r rr hrr hal
    cases ho : rr.owner with
    | task t =>
      rw [ho] at hl; simp only [OwnerLive] at hl ⊢
      obtain ⟨st, hst, hnonterm⟩ := hl; exact hnt t st hst hnonterm
    | actor a =>
      rw [ho] at hl; simp only [OwnerLive] at hl ⊢
      obtain ⟨hex, hne⟩ := hl
      exact ⟨step_preserves_actor_exists a op hex, by rw [hstat]; exact hne⟩
  · intro r rr hrr hcl; rw [hres] at hrr
    have hc := h.closing_owner_closed r rr hrr hcl
    cases ho : rr.owner with
    | task t =>
      rw [ho] at hc; simp only [OwnerClosed] at hc ⊢
      obtain ⟨st, hst, hterm⟩ := hc
      exact ⟨st, step_preserves_terminal h hst (by simpa using hterm) op, hterm⟩
    | actor a =>
      rw [ho] at hc; simp only [OwnerClosed] at hc ⊢
      obtain ⟨hex, hce⟩ := hc
      exact ⟨step_preserves_actor_exists a op hex, by rw [hstat]; exact hce⟩

/-! ## Terminal-coupling resource preservation -/

/-- The owner-generic resource obligations are preserved by a terminal
transition that marks every `allocated` resource of a `p`-task `closing`. Task
owners use `hmarked`/`hunmarked`; actor owners are untouched by the task-marking
and transfer via `hmb`/`hstat`. Closes `complete`/`cancel`/`fail`/`cancelTree`
uniformly (RFC 057/091). -/
theorem wf_resource_terminal {s s' : RuntimeState} (h : WellFormed s)
    (p : TaskId → Bool)
    (hres : s'.resources = markClosingIf p s.resources)
    (hnext : s'.nextResourceId = s.nextResourceId)
    (hstat : s'.actorStatus = s.actorStatus)
    (hmb : s'.mailboxes = s.mailboxes)
    (hmarked : ∀ u st, p u = true → s.taskState u = some st →
        ∃ st', s'.taskState u = some st' ∧ st'.isTerminal)
    (hunmarked : ∀ u st, p u = false → s.taskState u = some st →
        ∃ st', s'.taskState u = some st' ∧ st'.isTerminal = st.isTerminal) :
    (∀ r, r ≥ s'.nextResourceId → s'.resources r = none) ∧
    (∀ r rr, s'.resources r = some rr → OwnerValid s' rr.owner) ∧
    (∀ r rr, s'.resources r = some rr → rr.state = .allocated → OwnerLive s' rr.owner) ∧
    (∀ r rr, s'.resources r = some rr → rr.state = .closing → OwnerClosed s' rr.owner) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr; rw [hres]; rw [hnext] at hr
    exact markClosingIf_none p s.resources r (h.resource_fresh r hr)
  · intro r rr hrr; rw [hres] at hrr; simp only [markClosingIf] at hrr
    obtain ⟨st0, hs⟩ := markClosingIfOwner_owner hrr
    have hv := h.resource_owner_valid r ⟨rr.owner, st0⟩ hs
    cases ho : rr.owner with
    | task t =>
      rw [ho] at hv; simp only [OwnerValid] at hv ⊢
      obtain ⟨st, hst⟩ := hv
      by_cases hp : p t = true
      · obtain ⟨st', hst', _⟩ := hmarked t st hp hst; exact ⟨st', hst'⟩
      · simp only [Bool.not_eq_true] at hp
        obtain ⟨st', hst', _⟩ := hunmarked t st hp hst; exact ⟨st', hst'⟩
    | actor a =>
      rw [ho] at hv; simp only [OwnerValid, ActorExists] at hv ⊢
      rw [hmb]; exact hv
  · intro r rr hrr hal; rw [hres] at hrr; simp only [markClosingIf] at hrr
    obtain ⟨o, st⟩ := rr; cases hal
    obtain ⟨hs, hpf⟩ := markClosingIfOwner_allocated hrr
    have hl := h.allocated_owner_live r ⟨o, .allocated⟩ hs rfl
    cases ho : o with
    | task t =>
      rw [ho] at hl; simp only [OwnerLive] at hl ⊢
      obtain ⟨st1, hst1, hnt1⟩ := hl
      have hpt : p t = false := by
        simpa [ho] using hpf
      obtain ⟨st', hst', hcl⟩ := hunmarked t st1 hpt hst1
      exact ⟨st', hst', by rw [hcl]; exact hnt1⟩
    | actor a =>
      rw [ho] at hl; simp only [OwnerLive, ActorExists] at hl ⊢
      obtain ⟨hex, hne⟩ := hl
      exact ⟨by rw [hmb]; exact hex, by rw [hstat]; exact hne⟩
  · intro r rr hrr hcl; rw [hres] at hrr; simp only [markClosingIf] at hrr
    obtain ⟨o, st⟩ := rr; cases hcl
    rcases markClosingIfOwner_closing hrr with hclr | ⟨hal, hpt⟩
    · have hc := h.closing_owner_closed r ⟨o, .closing⟩ hclr rfl
      cases ho : o with
      | task t =>
        rw [ho] at hc; simp only [OwnerClosed] at hc ⊢
        obtain ⟨st1, hst1, hterm⟩ := hc
        by_cases hp : p t = true
        · obtain ⟨st', hst', hterm'⟩ := hmarked t st1 hp hst1; exact ⟨st', hst', hterm'⟩
        · simp only [Bool.not_eq_true] at hp
          obtain ⟨st', hst', hcl'⟩ := hunmarked t st1 hp hst1
          exact ⟨st', hst', by rw [hcl']; exact hterm⟩
      | actor a =>
        rw [ho] at hc; simp only [OwnerClosed, ActorExists] at hc ⊢
        obtain ⟨hex, hce⟩ := hc
        exact ⟨by rw [hmb]; exact hex, by rw [hstat]; exact hce⟩
    · have hl := h.allocated_owner_live r ⟨o, .allocated⟩ hal rfl
      cases ho : o with
      | task t =>
        rw [ho] at hl
        have hpt' : p t = true := by simpa [ho] using hpt
        simp only [OwnerLive] at hl
        obtain ⟨st1, hst1, _⟩ := hl
        obtain ⟨st', hst', hterm'⟩ := hmarked t st1 hpt' hst1
        simp only [OwnerClosed]; exact ⟨st', hst', hterm'⟩
      | actor a =>
        exfalso; rw [ho] at hpt; simp at hpt

/-! ## Ledger-only operations (acquire / release / finalize) -/

/-- For an operation that changes *only* the resource ledger (`resources`,
`nextResourceId`) and leaves every other field of the state untouched, the 29
non-resource `WellFormed` fields transfer definitionally from `h`; the caller
supplies the four owner-generic resource obligations for the new ledger. (Owner
predicates only read `taskState`/`actorStatus`/`mailboxes`, all unchanged, so
`OwnerValid`/`Live`/`Closed s` are defeq to the same on the updated state.) -/
theorem wf_resources_only {s : RuntimeState}
    {R : ResourceId → Option ResourceRecord} {N : Nat}
    (h : WellFormed s)
    (h30 : ∀ r, r ≥ N → R r = none)
    (h31 : ∀ r rr, R r = some rr → OwnerValid s rr.owner)
    (h32 : ∀ r rr, R r = some rr → rr.state = .allocated → OwnerLive s rr.owner)
    (h33 : ∀ r rr, R r = some rr → rr.state = .closing → OwnerClosed s rr.owner) :
    WellFormed { s with resources := R, nextResourceId := N } :=
  ⟨h.readyQ_nodup, h.readyQ_queued, h.running_runs, h.timers_nodup, h.timers_sleep,
   h.fresh_none, h.timers_sorted, h.spawned_has_owner, h.owned_has_mailbox, h.runnable_queued,
   h.waiters_waiting, h.waiters_owned, h.waiting_queued, h.waiters_nodup, h.parent_lt,
   h.parent_spawned, h.occ_fresh, h.occ_nodup, h.occ_disjoint, h.owner_spawned,
   h.parent_child_spawned, h.timed_has_deadline, h.deadline_is_timed, h.timed_has_timer,
   h.timed_is_waiter, h.timed_waiters_valid, h.timed_waiters_nodup, h.timed_waiters_exclusive,
   h.mailbox_within_capacity, h30, h31, h32, h33⟩

/-- Flipping one present resource to `released` preserves the resource
obligations — shared by `release` (allocated → released) and `finalize`
(closing → released). The released entry can no longer witness the allocated
or closing obligations, and all other entries are unchanged. -/
theorem wf_flip_to_released {s : RuntimeState} {r₀ : ResourceId} {o : ResourceOwner}
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
      exact h.resource_owner_valid r ⟨o, st0⟩ hres
    · rw [upd_ne _ _ hrn] at hrr; exact h.resource_owner_valid r rr hrr
  · intro r rr hrr hal
    by_cases hrn : r = r₀
    · subst hrn; rw [upd_self] at hrr; injection hrr with hrr; subst hrr; simp at hal
    · rw [upd_ne _ _ hrn] at hrr; exact h.allocated_owner_live r rr hrr hal
  · intro r rr hrr hclr
    by_cases hrn : r = r₀
    · subst hrn; rw [upd_self] at hrr; injection hrr with hrr; subst hrr; simp at hclr
    · rw [upd_ne _ _ hrn] at hrr; exact h.closing_owner_closed r rr hrr hclr


end Henret