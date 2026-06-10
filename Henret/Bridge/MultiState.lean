import Henret.Bridge.State
import Henret.Bridge.Preservation
import Henret.Proofs
/-!
  # Henret.Bridge.MultiState  (RFC 043)

  Multi-worker generalisation of the single-worker `BridgeState`.

  Where `BridgeState` pins henret's `readyQ` to worker 0's queue exactly
  (a strong list-equality relation), the multi-worker bridge relates
  `readyQ` to the *union* of all worker queues by **membership**, not
  order.  This is the right relation for a work-stealing scheduler:
  stealing moves a task between workers without changing the set of
  ready tasks, so a membership relation is preserved by `Steal` while a
  list-equality relation would not be.

  ## Design (RFC 043)

  - No worker-placement field is added to `RuntimeState`.  Worker
    assignment is a bridge/refinement concern; the kernel stays
    actor/task semantic.
  - `MultiBridgeState` (Option B) states: soundness (every queued task is
    ready), completeness (every ready task is queued somewhere),
    per-worker no-duplicates, and global uniqueness (a task sits in at
    most one worker queue).
  - The single-worker `BridgeState` is a strict special case:
    `single_bridge_implies_multi_bridge`.
  - Wake placement policy for this first version: **wake to worker 0**
    (deterministic; compatible with the single-worker projection).

  ## Scope

  This is a model-level membership bridge.  It does not prove C
  race-freedom, fairness, or liveness; those remain out of scope
  (see `docs/bridge-architecture.md`).
-/
namespace Henret.Bridge

/-! ## Multi-worker Steal semantics

    `applyQOp`'s `Steal` is a no-op in the single-worker bridge.  For the
    multi-worker bridge we give it real semantics: a thief takes the head
    of the victim's queue (the model-level analogue of stealing from the
    top end) and appends it to its own tail.  Membership of the union is
    preserved. -/

/-- Multi-worker queue-op application.  Unlike `applyQOp` (single-worker),
    `Steal src dst` actually moves the head of `src`'s queue to `dst`'s
    tail.  `Push`/`Pop`/`Filter` act on the named worker; `Inject` targets
    worker 0; `Wake` targets worker 0 (wake-to-worker-0 policy). -/
def applyMQOp (wqs : WorkerQueues) : QOp → WorkerQueues
  | .Push w t   => fun w' => if w' = w then wqs w ++ [t] else wqs w'
  | .Pop w      => fun w' => if w' = w then (wqs w).tail else wqs w'
  | .Filter w t => fun w' => if w' = w then (wqs w).filter (· ≠ t) else wqs w'
  | .Steal src dst =>
      match (wqs src) with
      | []      => wqs   -- nothing to steal
      | t :: ts => fun w' =>
          if w' = src then ts
          else if w' = dst then wqs dst ++ [t]
          else wqs w'
  | .Wake t     => fun w' => if w' = 0 then wqs 0 ++ [t] else wqs w'
  | .Inject t   => fun w' => if w' = 0 then wqs 0 ++ [t] else wqs w'

/-- Apply a list of multi-worker `QOp`s in order. -/
def applyMQOps (wqs : WorkerQueues) : List QOp → WorkerQueues
  | []        => wqs
  | op :: ops => applyMQOps (applyMQOp wqs op) ops

/-! ## MultiBridgeState relation (Option B — membership) -/

/-- `MultiBridgeState s wqs` — henret's `readyQ` membership equals the
    union of all worker queues, with global uniqueness.

    Membership, not order: a work-stealing scheduler does not preserve a
    single global ready order, so the relation is stated on the set of
    ready tasks. -/
structure MultiBridgeState (s : RuntimeState) (wqs : WorkerQueues) : Prop where
  /-- Soundness: every queued task is ready in henret. -/
  sound        : ∀ t w, t ∈ wqs w → t ∈ s.readyQ
  /-- Completeness: every ready task is queued on some worker. -/
  complete     : ∀ t, t ∈ s.readyQ → ∃ w, t ∈ wqs w
  /-- Each worker queue is duplicate-free. -/
  worker_nodup : ∀ w, (wqs w).Nodup
  /-- Global uniqueness: a task is queued on at most one worker. -/
  global_unique : ∀ t w1 w2, t ∈ wqs w1 → t ∈ wqs w2 → w1 = w2

/-! ## Single-worker bridge is a special case -/

/-- The single-worker `BridgeState` implies the multi-worker
    `MultiBridgeState`, provided henret's `readyQ` is duplicate-free
    (which holds for every reachable state via `WellFormed.readyQ_nodup`). -/
theorem single_bridge_implies_multi_bridge {s : RuntimeState} {wqs : WorkerQueues}
    (hbs : BridgeState s wqs) (hnd : s.readyQ.Nodup) :
    MultiBridgeState s wqs := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- sound
    intro t w hw
    by_cases h0 : w = 0
    · rw [h0, ← hbs.queue_eq] at hw; exact hw
    · rw [hbs.other_empty w h0] at hw; simp at hw
  · -- complete
    intro t ht
    exact ⟨0, by rw [← hbs.queue_eq]; exact ht⟩
  · -- worker_nodup
    intro w
    by_cases h0 : w = 0
    · rw [h0, ← hbs.queue_eq]; exact hnd
    · rw [hbs.other_empty w h0]; exact List.nodup_nil
  · -- global_unique
    intro t w1 w2 h1 h2
    by_cases hw1 : w1 = 0 <;> by_cases hw2 : w2 = 0
    · rw [hw1, hw2]
    · rw [hbs.other_empty w2 hw2] at h2; simp at h2
    · rw [hbs.other_empty w1 hw1] at h1; simp at h1
    · rw [hbs.other_empty w1 hw1] at h1; simp at h1

/-! ## Membership-preservation theorems for multi-worker ops

    Each theorem shows the *set* of ready tasks (and the placement
    invariants) is preserved, mirroring the henret-side effect on
    `readyQ`. -/

/-- `Push w t` to a fresh task `t` (not already queued anywhere) adds `t`
    to henret's `readyQ` and to worker `w`'s queue, preserving the
    membership relation. -/
theorem multi_bridge_push {s : RuntimeState} {wqs : WorkerQueues}
    (hm : MultiBridgeState s wqs) (w : WorkerIdx) (t : TaskId)
    (hfresh : ∀ w', t ∉ wqs w') (hready : t ∉ s.readyQ) :
    MultiBridgeState { s with readyQ := s.readyQ ++ [t] } (applyMQOp wqs (.Push w t)) := by
  simp only [applyMQOp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- sound
    intro u w' hu
    by_cases hw' : w' = w
    · simp only [hw', if_pos rfl] at hu
      rcases List.mem_append.mp hu with hu | hu
      · exact List.mem_append_left _ (hm.sound u w hu)
      · simp only [List.mem_singleton] at hu; subst hu
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · simp only [if_neg hw'] at hu
      exact List.mem_append_left _ (hm.sound u w' hu)
  · -- complete
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨w', hw'⟩ := hm.complete u hu
      by_cases hww : w' = w
      · exact ⟨w, by simp only [if_pos rfl]; exact List.mem_append_left _ (hww ▸ hw')⟩
      · exact ⟨w', by simp only [if_neg hww]; exact hw'⟩
    · simp only [List.mem_singleton] at hu; subst hu
      exact ⟨w, by simp only [if_pos rfl]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
  · -- worker_nodup
    intro w'
    by_cases hw' : w' = w
    · simp only [hw', if_pos rfl]
      exact nodup_append_singleton (hm.worker_nodup w) (hfresh w)
    · simp only [if_neg hw']; exact hm.worker_nodup w'
  · -- global_unique
    intro u w1 w2 h1 h2
    -- Reduce each membership to: either (u = t ∧ w = wᵢ) or (u ≠ t ∧ u ∈ wqs wᵢ)
    have classify : ∀ wi, u ∈ (if wi = w then wqs w ++ [t] else wqs wi) →
        (u = t ∧ wi = w) ∨ u ∈ wqs wi := by
      intro wi hwi
      by_cases hwiw : wi = w
      · simp only [hwiw, if_pos rfl] at hwi
        rcases List.mem_append.mp hwi with hwi | hwi
        · exact Or.inr (hwiw ▸ hwi)
        · simp only [List.mem_singleton] at hwi; exact Or.inl ⟨hwi, hwiw⟩
      · simp only [if_neg hwiw] at hwi; exact Or.inr hwi
    rcases classify w1 h1 with ⟨hut1, rfl⟩ | hm1
    · rcases classify w2 h2 with ⟨hut2, rfl⟩ | hm2
      · rfl
      · exact absurd hm2 (hut1 ▸ hfresh w2)
    · rcases classify w2 h2 with ⟨hut2, rfl⟩ | hm2
      · exact absurd hm1 (hut2 ▸ hfresh w1)
      · exact hm.global_unique u w1 w2 hm1 hm2

/-- `Filter w t` removes `t` from worker `w`'s queue, mirroring henret's
    `readyQ.filter (· ≠ t)`.  Membership relation preserved. -/
theorem multi_bridge_filter {s : RuntimeState} {wqs : WorkerQueues}
    (hm : MultiBridgeState s wqs) (w : WorkerIdx) (t : TaskId)
    (hplace : ∀ w', w' ≠ w → t ∉ wqs w') :
    MultiBridgeState { s with readyQ := s.readyQ.filter (· ≠ t) }
                     (applyMQOp wqs (.Filter w t)) := by
  simp only [applyMQOp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- sound
    intro u w' hu
    by_cases hw' : w' = w
    · subst hw'
      have hu' : u ∈ (wqs w').filter (· ≠ t) := by simpa only [if_pos rfl] using hu
      have hp := List.mem_filter.mp hu'
      exact List.mem_filter.mpr ⟨hm.sound u w' hp.1, hp.2⟩
    · simp only [if_neg hw'] at hu
      have hut : u ≠ t := fun he => hplace w' hw' (he ▸ hu)
      exact List.mem_filter.mpr ⟨hm.sound u w' hu, by simpa using hut⟩
  · -- complete
    intro u hu
    have hp := List.mem_filter.mp hu
    obtain ⟨w', hw'⟩ := hm.complete u hp.1
    by_cases hww : w' = w
    · exact ⟨w, by simp only [if_pos rfl]; exact List.mem_filter.mpr ⟨hww ▸ hw', hp.2⟩⟩
    · exact ⟨w', by simp only [if_neg hww]; exact hw'⟩
  · -- worker_nodup
    intro w'
    by_cases hw' : w' = w
    · simp only [hw', if_pos rfl]; exact (hm.worker_nodup w).filter _
    · simp only [if_neg hw']; exact hm.worker_nodup w'
  · -- global_unique
    intro u w1 w2 h1 h2
    have hmem1 : u ∈ wqs w1 := by
      by_cases hw1 : w1 = w
      · subst hw1
        have h1' : u ∈ (wqs w1).filter (· ≠ t) := by simpa only [if_pos rfl] using h1
        exact (List.mem_filter.mp h1').1
      · simp only [if_neg hw1] at h1; exact h1
    have hmem2 : u ∈ wqs w2 := by
      by_cases hw2 : w2 = w
      · subst hw2
        have h2' : u ∈ (wqs w2).filter (· ≠ t) := by simpa only [if_pos rfl] using h2
        exact (List.mem_filter.mp h2').1
      · simp only [if_neg hw2] at h2; exact h2
    exact hm.global_unique u w1 w2 hmem1 hmem2

/-- `Steal src dst` moves the head of `src`'s queue to `dst`'s tail.  The
    union of ready tasks is unchanged, so the membership relation against
    a fixed henret `readyQ` is preserved. -/
theorem multi_bridge_steal {s : RuntimeState} {wqs : WorkerQueues}
    (hm : MultiBridgeState s wqs) (src dst : WorkerIdx) (hne : src ≠ dst) :
    MultiBridgeState s (applyMQOp wqs (.Steal src dst)) := by
  simp only [applyMQOp]
  cases hsrc : wqs src with
  | nil => simpa [hsrc] using hm
  | cons t ts =>
    simp only [hsrc]
    -- t is the stolen head; it moves from src to dst's tail
    have ht_src : t ∈ wqs src := by rw [hsrc]; exact List.mem_cons_self t ts
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- sound
      intro u w' hu
      by_cases hws : w' = src
      · simp only [hws, if_pos rfl] at hu
        exact hm.sound u src (by rw [hsrc]; exact List.mem_cons_of_mem t hu)
      · simp only [if_neg hws] at hu
        by_cases hwd : w' = dst
        · simp only [hwd, if_pos rfl] at hu
          rcases List.mem_append.mp hu with hu | hu
          · exact hm.sound u dst hu
          · simp only [List.mem_singleton] at hu; subst hu; exact hm.sound u src ht_src
        · simp only [if_neg hwd] at hu; exact hm.sound u w' hu
    · -- complete
      intro u hu
      obtain ⟨w', hw'⟩ := hm.complete u hu
      by_cases hws : w' = src
      · -- u was in src; either it is t (now in dst) or it is in ts (still in src)
        rw [hws, hsrc] at hw'
        rcases List.mem_cons.mp hw' with rfl | hmem
        · refine ⟨dst, ?_⟩
          simp only [if_neg (Ne.symm hne), if_pos rfl]
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        · exact ⟨src, by simp only [if_pos rfl]; exact hmem⟩
      · by_cases hwd : w' = dst
        · refine ⟨dst, ?_⟩
          simp only [if_neg (hwd ▸ hws), if_pos rfl]
          rw [hwd] at hw'; exact List.mem_append_left _ hw'
        · exact ⟨w', by simp only [if_neg hws, if_neg hwd]; exact hw'⟩
    · -- worker_nodup
      intro w'
      by_cases hws : w' = src
      · simp only [hws, if_pos rfl]
        have := hm.worker_nodup src; rw [hsrc, List.nodup_cons] at this; exact this.2
      · simp only [if_neg hws]
        by_cases hwd : w' = dst
        · simp only [hwd, if_pos rfl]
          refine nodup_append_singleton (hm.worker_nodup dst) ?_
          intro hmem
          exact (Ne.symm hne) (hm.global_unique t dst src hmem ht_src)
        · simp only [if_neg hwd]; exact hm.worker_nodup w'
    · -- global_unique
      intro u w1 w2 h1 h2
      -- Reduce both memberships to original-queue memberships, tracking t's move
      have mem_of : ∀ w', u ∈ (if w' = src then ts
                               else if w' = dst then wqs dst ++ [t] else wqs w') →
                    (u = t ∧ w' = dst) ∨ (u ≠ t ∧ u ∈ wqs w') := by
        intro w' hw'
        by_cases hws : w' = src
        · simp only [hws, if_pos rfl] at hw'
          have hu_ne : u ≠ t := fun he => by
            have hnd := hm.worker_nodup src; rw [hsrc, List.nodup_cons] at hnd
            exact hnd.1 (he ▸ hw')
          exact Or.inr ⟨hu_ne, by rw [hws, hsrc]; exact List.mem_cons_of_mem t hw'⟩
        · simp only [if_neg hws] at hw'
          by_cases hwd : w' = dst
          · simp only [hwd, if_pos rfl] at hw'
            rcases List.mem_append.mp hw' with hw' | hw'
            · have hu_ne : u ≠ t := fun he => by
                have ht_dst : t ∈ wqs dst := he ▸ hw'
                exact (Ne.symm hne) (hm.global_unique t dst src ht_dst ht_src)
              exact Or.inr ⟨hu_ne, by rw [hwd]; exact hw'⟩
            · simp only [List.mem_singleton] at hw'; subst hw'
              exact Or.inl ⟨rfl, hwd⟩
          · simp only [if_neg hwd] at hw'
            have hu_ne : u ≠ t := fun he => by
              have := hm.global_unique t w' src (he ▸ hw') ht_src
              exact hws this
            exact Or.inr ⟨hu_ne, hw'⟩
      rcases mem_of w1 h1 with ⟨he1, hd1⟩ | ⟨hne1, hm1⟩
      · rcases mem_of w2 h2 with ⟨he2, hd2⟩ | ⟨hne2, _⟩
        · rw [hd1, hd2]
        · exact absurd he1 hne2
      · rcases mem_of w2 h2 with ⟨he2, _⟩ | ⟨_, hm2⟩
        · exact absurd he2 hne1
        · exact hm.global_unique u w1 w2 hm1 hm2

/-! ## Reachability corollary -/

/-- Every reachable henret state has a worker-queue witness satisfying the
    multi-worker `MultiBridgeState`.  Follows from the single-worker
    `bridge_run_tracks_single_worker` together with `reachable_wf`'s
    `readyQ_nodup` field, via `single_bridge_implies_multi_bridge`. -/
theorem reachable_multi_bridge (ops : List RuntimeOp) :
    ∃ wqs : WorkerQueues, MultiBridgeState (run RuntimeState.init ops) wqs :=
  ⟨applyQOps WorkerQueues.init (toQOpsTrace RuntimeState.init ops),
   single_bridge_implies_multi_bridge
     (bridge_run_tracks_single_worker ops)
     (reachable_wf ops).readyQ_nodup⟩

end Henret.Bridge
