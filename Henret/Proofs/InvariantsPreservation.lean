import Henret.Proofs.Invariants
import Henret.Proofs.Ownership

namespace Henret

/-! ## Invariant preservation (RFC 013)

`step_preserves_wf` walks all ten operations and shows the
`WellFormed` discipline survives each.  `run_preserves_wf` lifts it to
programs, and `reachable_wf` instantiates at `init`: **every reachable
state is well-formed**. -/

/-- Every operation preserves well-formedness. -/
theorem step_preserves_wf {s : RuntimeState} (h : WellFormed s)
    (op : RuntimeOp) : WellFormed ((step s op).1) := by
  cases op with
  | spawn a =>
    cases hts : s.taskState s.nextId with
    | some _ => simpa [step, hts] using h
    | none =>
      have hnq : s.nextId ∉ s.readyQ := fun hm => by
        have h1 := h.readyQ_queued _ hm
        rw [hts] at h1
        simp [Option.any] at h1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- readyQ_nodup
        simp only [step, hts]
        exact nodup_append_singleton h.readyQ_nodup hnq
      · -- readyQ_queued
        intro u hm
        simp only [step, hts] at hm ⊢
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · have hu : u ≠ s.nextId := fun he => hnq (he ▸ hm)
          simp only [upd, if_neg hu]
          exact h.readyQ_queued u hm
        · simp [upd, Option.any, TaskState.isRunnable]
      · -- running_runs
        intro u hr
        simp only [step, hts] at hr ⊢
        have h1 := h.running_runs u hr
        have hu : u ≠ s.nextId := fun he => by rw [he, hts] at h1; cases h1
        simp only [upd, if_neg hu]
        exact h1
      · -- timers_nodup
        simp only [step, hts]
        exact h.timers_nodup
      · -- timers_sleep
        intro e he
        simp only [step, hts] at he ⊢
        have h1 := h.timers_sleep e he
        have hu : e.task ≠ s.nextId := fun heq => by rw [heq, hts] at h1; cases h1
        simp only [upd, if_neg hu]
        exact h1
      · -- fresh_none
        intro u hu
        simp only [step, hts] at hu ⊢
        have h1 : u ≠ s.nextId := Nat.ne_of_gt hu
        have h2 : s.nextId ≤ u := Nat.le_of_succ_le hu
        simp only [upd, if_neg h1]
        exact h.fresh_none u h2
  | schedule =>
    cases hr : s.running with
    | some _ => simpa [step, hr] using h
    | none =>
      cases hq : s.readyQ with
      | nil => simpa [step, hr, hq] using h
      | cons t q =>
        by_cases hrun : (s.taskState t).any TaskState.isRunnable = true
        · have hnodup := h.readyQ_nodup
          rw [hq, List.nodup_cons] at hnodup
          have htsome : ∃ x, s.taskState t = some x := by
            cases hto : s.taskState t with
            | none => rw [hto] at hrun; simp [Option.any] at hrun
            | some x => exact ⟨x, rfl⟩
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [step, hr, hq, if_pos hrun]
            exact hnodup.2
          · intro u hm
            simp only [step, hr, hq, if_pos hrun] at hm ⊢
            have hu : u ≠ t := fun he => hnodup.1 (he ▸ hm)
            simp only [upd, if_neg hu]
            exact h.readyQ_queued u (by rw [hq]; exact List.mem_cons_of_mem t hm)
          · intro u hru
            simp only [step, hr, hq, if_pos hrun] at hru ⊢
            cases hru
            simp [upd]
          · simp only [step, hr, hq, if_pos hrun]
            exact h.timers_nodup
          · intro e he
            simp only [step, hr, hq, if_pos hrun] at he ⊢
            have h1 := h.timers_sleep e he
            have hu : e.task ≠ t := fun heq => by
              rw [heq] at h1
              rw [h1] at hrun
              simp [Option.any, TaskState.isRunnable] at hrun
            simp only [upd, if_neg hu]
            exact h1
          · intro u hu
            simp only [step, hr, hq, if_pos hrun] at hu ⊢
            obtain ⟨x, hx⟩ := htsome
            have h1 : u ≠ t := fun he => by
              rw [← he] at hx
              rw [h.fresh_none u hu] at hx
              cases hx
            simp only [upd, if_neg h1]
            exact h.fresh_none u hu
        · simp at hrun; simpa [step, hr, hq, hrun] using h
  | yield t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simpa [step, hrt, hts] using h
      | some s' =>
        cases s' with
        | running =>
          have hnq : t ∉ s.readyQ := fun hm => by
            have h1 := h.readyQ_queued t hm
            rw [hts] at h1
            simp [Option.any, TaskState.isRunnable] at h1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [step, hrt, hts, if_pos rfl]
            simp only [if_pos]
            exact nodup_append_singleton h.readyQ_nodup hnq
          · intro u hm
            simp [step, hrt, hts] at hm ⊢
            rcases hm with hm | rfl
            · have hu : u ≠ t := fun he => hnq (he ▸ hm)
              simp only [upd, if_neg hu]
              exact h.readyQ_queued u hm
            · simp [upd, Option.any, TaskState.isRunnable]
          · intro u hru
            simp [step, hrt, hts] at hru
          · simp only [step]
            simp [hrt, hts]
            exact h.timers_nodup
          · intro e he
            simp [step, hrt, hts] at he ⊢
            have h1 := h.timers_sleep e he
            have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
            simp only [upd, if_neg hu]
            exact h1
          · intro u hu
            simp [step, hrt, hts] at hu ⊢
            have h1 : u ≠ t := fun he => by
              rw [← he] at hts
              rw [h.fresh_none u hu] at hts
              cases hts
            simp only [upd, if_neg h1]
            exact h.fresh_none u hu
        | new => simpa [step, hrt, hts] using h
        | ready => simpa [step, hrt, hts] using h
        | yielded => simpa [step, hrt, hts] using h
        | sleeping => simpa [step, hrt, hts] using h
        | completed => simpa [step, hrt, hts] using h
        | cancelled => simpa [step, hrt, hts] using h
    · simpa [step, hrt] using h
  | complete t =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simpa [step, hrt, hts] using h
      | some s' =>
        cases s' with
        | running =>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [step, hrt, hts]
            exact h.readyQ_nodup
          · intro u hm
            simp [step, hrt, hts] at hm ⊢
            have h1 := h.readyQ_queued u hm
            have hu : u ≠ t := fun he => by
              rw [he, hts] at h1
              simp [Option.any, TaskState.isRunnable] at h1
            simp only [upd, if_neg hu]
            exact h1
          · intro u hru
            simp [step, hrt, hts] at hru
          · simp [step, hrt, hts]
            exact h.timers_nodup
          · intro e he
            simp [step, hrt, hts] at he ⊢
            have h1 := h.timers_sleep e he
            have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
            simp only [upd, if_neg hu]
            exact h1
          · intro u hu
            simp [step, hrt, hts] at hu ⊢
            have h1 : u ≠ t := fun he => by
              rw [← he] at hts
              rw [h.fresh_none u hu] at hts
              cases hts
            simp only [upd, if_neg h1]
            exact h.fresh_none u hu
        | new => simpa [step, hrt, hts] using h
        | ready => simpa [step, hrt, hts] using h
        | yielded => simpa [step, hrt, hts] using h
        | sleeping => simpa [step, hrt, hts] using h
        | completed => simpa [step, hrt, hts] using h
        | cancelled => simpa [step, hrt, hts] using h
    · simpa [step, hrt] using h
  | cancel t =>
    cases hts : s.taskState t with
    | none => simpa [step, hts] using h
    | some s' =>
      by_cases hterm : s'.isTerminal = true
      · simpa [step, hts, hterm] using h
      · simp at hterm
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [step, hts, hterm]
          exact h.readyQ_nodup.filter _
        · intro u hm
          simp [step, hts, hterm] at hm ⊢
          obtain ⟨hm, hu⟩ := hm
          simp only [upd, if_neg hu]
          exact h.readyQ_queued u hm
        · intro u hru
          simp only [step, hts, hterm, Bool.false_eq_true, if_false] at hru ⊢
          by_cases hcase : s.running = some t
          · rw [if_pos hcase] at hru; cases hru
          · rw [if_neg hcase] at hru
            have h1 := h.running_runs u hru
            have hu : u ≠ t := fun he => hcase (he ▸ hru)
            simp only [upd, if_neg hu]
            exact h1
        · simp [step, hts, hterm]
          exact nodup_of_sublist
            (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup
        · intro e he
          simp [step, hts, hterm] at he ⊢
          obtain ⟨he, hu⟩ := he
          simp only [upd, if_neg hu]
          exact h.timers_sleep e he
        · intro u hu
          simp [step, hts, hterm] at hu ⊢
          have h1 : u ≠ t := fun he => by
            rw [← he] at hts
            rw [h.fresh_none u hu] at hts
            cases hts
          simp only [upd, if_neg h1]
          exact h.fresh_none u hu
  | send a m =>
    cases hmb : s.mailboxes a with
    | none => simpa [step, hmb] using h
    | some mb =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [step, hmb] <;>
        first
          | exact h.readyQ_nodup
          | exact h.readyQ_queued
          | exact h.running_runs
          | exact h.timers_nodup
          | exact h.timers_sleep
          | exact h.fresh_none
  | receive a =>
    cases hmb : s.mailboxes a with
    | none => simpa [step, hmb] using h
    | some mb =>
      cases hd : mb.dequeue with
      | none => simpa [step, hmb, hd] using h
      | some p =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [step, hmb, hd] <;>
          first
            | exact h.readyQ_nodup
            | exact h.readyQ_queued
            | exact h.running_runs
            | exact h.timers_nodup
            | exact h.timers_sleep
            | exact h.fresh_none
  | sleep t d =>
    by_cases hrt : s.running = some t
    · cases hts : s.taskState t with
      | none => simpa [step, hrt, hts] using h
      | some s' =>
        cases s' with
        | running =>
          have hnotin : t ∉ s.timers.map TimerEntry.task := by
            intro hm
            rw [List.mem_map] at hm
            obtain ⟨e, he, hee⟩ := hm
            have h1 := h.timers_sleep e he
            rw [hee, hts] at h1
            cases h1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [step, hrt, hts]
            exact h.readyQ_nodup
          · intro u hm
            simp [step, hrt, hts] at hm ⊢
            have h1 := h.readyQ_queued u hm
            have hu : u ≠ t := fun he => by
              rw [he, hts] at h1
              simp [Option.any, TaskState.isRunnable] at h1
            simp only [upd, if_neg hu]
            exact h1
          · intro u hru
            simp [step, hrt, hts] at hru
          · simp [step, hrt, hts]
            exact insertSorted_task_nodup hnotin h.timers_nodup
          · intro e he
            simp [step, hrt, hts] at he ⊢
            rcases Timer.mem_insertSorted.mp he with rfl | he
            · simp [upd]
            · have h1 := h.timers_sleep e he
              have hu : e.task ≠ t := fun heq => by rw [heq, hts] at h1; cases h1
              simp only [upd, if_neg hu]
              exact h1
          · intro u hu
            simp [step, hrt, hts] at hu ⊢
            have h1 : u ≠ t := fun he => by
              rw [← he] at hts
              rw [h.fresh_none u hu] at hts
              cases hts
            simp only [upd, if_neg h1]
            exact h.fresh_none u hu
        | new => simpa [step, hrt, hts] using h
        | ready => simpa [step, hrt, hts] using h
        | yielded => simpa [step, hrt, hts] using h
        | sleeping => simpa [step, hrt, hts] using h
        | completed => simpa [step, hrt, hts] using h
        | cancelled => simpa [step, hrt, hts] using h
    · simpa [step, hrt] using h
  | tick t =>
    by_cases hle : s.now ≤ t
    · obtain ⟨woken, hwdef⟩ : ∃ w, w = ((Timer.expired s.timers t).map TimerEntry.task).filter
          (fun u => s.taskState u = some .sleeping) := ⟨_, rfl⟩
      have hwoken_sleep : ∀ u ∈ woken, s.taskState u = some .sleeping := by
        intro u hm
        rw [hwdef] at hm
        have := (List.mem_filter.mp hm).2
        simpa using this
      have hwoken_nodup : woken.Nodup := by
        rw [hwdef]
        exact (nodup_of_sublist
          (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup).filter _
      have hdisj : ∀ a ∈ s.readyQ, a ∉ woken := by
        intro a ha hm
        have h1 := h.readyQ_queued a ha
        rw [hwoken_sleep a hm] at h1
        simp [Option.any, TaskState.isRunnable] at h1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [step, if_pos hle]
        rw [← hwdef]
        exact nodup_append h.readyQ_nodup hwoken_nodup hdisj
      · intro u hm
        simp only [step, if_pos hle] at hm ⊢
        rw [← hwdef] at hm ⊢
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · rw [wakeMany_preserves_other (hdisj u hm)]
          exact h.readyQ_queued u hm
        · rw [wakeMany_wakes hm (hwoken_sleep u hm)]
          simp [Option.any, TaskState.isRunnable]
      · intro u hru
        simp only [step, if_pos hle] at hru ⊢
        rw [← hwdef]
        have h1 := h.running_runs u hru
        rw [wakeMany_preserves_of_ne_sleeping h1 (by simp) woken]
      · simp only [step, if_pos hle]
        exact nodup_of_sublist
          (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup
      · intro e he
        simp only [step, if_pos hle] at he ⊢
        rw [← hwdef]
        have hmem : e ∈ s.timers := (Timer.mem_remaining.mp he).1
        have hfut : t < e.deadline := (Timer.mem_remaining.mp he).2
        have h1 := h.timers_sleep e hmem
        have hnot : e.task ∉ woken := by
          intro hm
          rw [hwdef] at hm
          have hmm := (List.mem_filter.mp hm).1
          rw [List.mem_map] at hmm
          obtain ⟨e', he', hee⟩ := hmm
          have he'mem : e' ∈ s.timers := (Timer.mem_expired.mp he').1
          have he'due : e'.deadline ≤ t := (Timer.mem_expired.mp he').2
          have : e = e' := nodup_task_inj h.timers_nodup hmem he'mem hee.symm
          rw [this] at hfut
          omega
        rw [wakeMany_preserves_other hnot]
        exact h1
      · intro u hu
        simp only [step, if_pos hle] at hu ⊢
        rw [← hwdef]
        have h1 := h.fresh_none u hu
        have hnot : u ∉ woken := by
          intro hm
          rw [hwoken_sleep u hm] at h1
          cases h1
        rw [wakeMany_preserves_other hnot]
        exact h1
    · simpa [step, hle] using h
  | wake t =>
    cases hts : s.taskState t with
    | none => simpa [step, hts] using h
    | some s' =>
      cases s' with
      | sleeping =>
        have hnq : t ∉ s.readyQ := fun hm => by
          have h1 := h.readyQ_queued t hm
          rw [hts] at h1
          simp [Option.any, TaskState.isRunnable] at h1
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [step, hts]
          exact nodup_append_singleton h.readyQ_nodup hnq
        · intro u hm
          simp [step, hts] at hm ⊢
          rcases hm with hm | rfl
          · have hu : u ≠ t := fun he => hnq (he ▸ hm)
            simp only [upd, if_neg hu]
            exact h.readyQ_queued u hm
          · simp [upd, Option.any, TaskState.isRunnable]
        · intro u hru
          simp [step, hts] at hru ⊢
          have h1 := h.running_runs u hru
          have hu : u ≠ t := fun he => by rw [he, hts] at h1; cases h1
          simp only [upd, if_neg hu]
          exact h1
        · simp [step, hts]
          exact nodup_of_sublist
            (List.Sublist.map _ (List.filter_sublist s.timers)) h.timers_nodup
        · intro e he
          simp [step, hts] at he ⊢
          obtain ⟨he, hu⟩ := he
          simp only [upd, if_neg hu]
          exact h.timers_sleep e he
        · intro u hu
          simp [step, hts] at hu ⊢
          have h1 : u ≠ t := fun he => by
            rw [← he] at hts
            rw [h.fresh_none u hu] at hts
            cases hts
          simp only [upd, if_neg h1]
          exact h.fresh_none u hu
      | new => simpa [step, hts] using h
      | ready => simpa [step, hts] using h
      | running => simpa [step, hts] using h
      | yielded => simpa [step, hts] using h
      | completed => simpa [step, hts] using h
      | cancelled => simpa [step, hts] using h

/-- Whole-program invariant preservation. -/
theorem run_preserves_wf {s : RuntimeState} (h : WellFormed s) :
    ∀ ops : List RuntimeOp, WellFormed (run s ops) := by
  intro ops
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih => exact ih (step_preserves_wf h op)

/-- **Every reachable state is well-formed** (RFC 013 headline).
In particular: the ready queue never contains duplicates, every queued
task is runnable, every timer task is sleeping, and the
ownership-location disjointness corollaries hold throughout every
program. -/
theorem reachable_wf (ops : List RuntimeOp) :
    WellFormed (run RuntimeState.init ops) :=
  run_preserves_wf wf_init ops

end Henret

/-!
# Henret.Proofs.InvariantsPreservation

Preservation of the `WellFormed` invariant (RFC 013).

* `step_preserves_wf` — all ten operations preserve well-formedness.
* `run_preserves_wf` / `reachable_wf` — every reachable state is
  well-formed.  Corollaries via `Henret.Proofs.Invariants`:
  no duplicate ready entries, location disjointness (a task is queued,
  running, or sleeping-with-timer — never two at once).
-/
