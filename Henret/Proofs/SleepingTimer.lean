import Henret.Scheduler.Model
import Henret.Proofs.Lifecycle

/-!
# Henret.Proofs.SleepingTimer  (RFC 089 — RFC 057 Tier 2 groundwork)

A structural coherence invariant the model's `WellFormed` did not previously
carry: **every sleeping task has a registered timer**. `WellFormed.timers_sleep`
records only the converse (a timer's task is sleeping or waiting-timed), so
`timers = []` alone could not previously rule out a sleeping task — the gap that
left RFC 088's drained-permanence single-step.

* `SleepingHasTimer s` — `∀ t, taskState t = some .sleeping → ∃ e ∈ timers, e.task = t`.
* `step_preserves_sleepingHasTimer` — preserved by every operation: `sleep`
  registers a timer for the newly-sleeping task; every timer-removing operation
  (`wake`, `tick`, `cancel`, `fail`, `cancelTree`, `send`/`inject` waking a
  waiter) simultaneously un-sleeps the affected task, so a still-sleeping task
  keeps its timer; no other operation introduces a sleeping task.
* `reachable_sleepingHasTimer` — holds in every reachable state.
* `quiescent_no_sleeping` — the payoff: a quiescent runtime (in particular an
  empty timer queue) has no sleeping tasks. This is the fact that unblocks
  multi-step drained permanence and "stopped stays quiescent".

Proven as a standalone reachable invariant (not a 34th `WellFormed` field) to
keep the blast radius off the preservation files, mirroring RFC 057's
`reachable_released_resource_never_live`.
-/

namespace Henret

def SleepingHasTimer (s : RuntimeState) : Prop :=
  ∀ t, s.taskState t = some .sleeping → ∃ e ∈ s.timers, e.task = t

theorem sleepingHasTimer_init : SleepingHasTimer RuntimeState.init := by
  intro t ht; simp [RuntimeState.init] at ht

theorem step_preserves_sleepingHasTimer {s : RuntimeState}
    (h : SleepingHasTimer s) (op : RuntimeOp) :
    SleepingHasTimer (step s op).1 := by
  intro t' ht'
  revert ht'
  cases op with
  | sleep u d =>
    simp only [step]; split
    · split
      · intro ht'
        by_cases hu : t' = u
        · subst hu; exact ⟨⟨d, t'⟩, Timer.mem_insertSorted.2 (Or.inl rfl), rfl⟩
        · simp only [upd_ne _ _ hu] at ht'
          obtain ⟨e, hem, het⟩ := h t' ht'
          exact ⟨e, Timer.mem_insertSorted.2 (Or.inr hem), het⟩
      · intro ht'; exact h t' ht'
    · intro ht'; exact h t' ht'
  | wake u =>
    simp only [step]; split
    · intro ht'
      by_cases hu : t' = u
      · subst hu; simp [upd_self] at ht'
      · simp only [upd_ne _ _ hu] at ht'
        obtain ⟨e, hem, het⟩ := h t' ht'
        exact ⟨e, List.mem_filter.2 ⟨hem, by simp [het]; exact hu⟩, het⟩
    · intro ht'; exact h t' ht'
  | cancel u =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first
        | exact h t' ht'
        | (by_cases hu : t' = u
           · subst hu; simp [upd_self] at ht'
           · simp only [upd_ne _ _ hu] at ht'
             obtain ⟨e, hem, het⟩ := h t' ht'
             exact ⟨e, List.mem_filter.2 ⟨hem, by simp [het]; exact hu⟩, het⟩)
  | tick now =>
    simp only [step]; split
    · intro ht'
      rename_i hle
      by_cases hmemw : t' ∈ (((Timer.expired s.timers now).map TimerEntry.task).filter
          (fun u => s.taskState u = some .sleeping) ++
          ((Timer.expired s.timers now).map TimerEntry.task).filter
          (fun u => s.taskState u = some .waitingTimed))
      · exfalso
        have hst : s.taskState t' = some .sleeping ∨ s.taskState t' = some .waitingTimed := by
          rcases List.mem_append.1 hmemw with hL | hR
          · exact Or.inl (by simpa using (List.mem_filter.1 hL).2)
          · exact Or.inr (by simpa using (List.mem_filter.1 hR).2)
        have hw := wakeMany_wakes hmemw hst
        simp [hw] at ht'
      · simp only [wakeMany_preserves_other hmemw] at ht'
        obtain ⟨e, hem, het⟩ := h t' ht'
        refine ⟨e, Timer.mem_remaining.2 ⟨hem, ?_⟩, het⟩
        rcases Nat.lt_or_ge now e.deadline with hlt | hge
        · exact hlt
        · exfalso; apply hmemw
          apply List.mem_append.2; left
          apply List.mem_filter.2
          refine ⟨List.mem_map.2 ⟨e, Timer.mem_expired.2 ⟨hem, hge⟩, het⟩, ?_⟩
          simpa using ht'
    · intro ht'; exact h t' ht'
  | fail u =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first
        | exact h t' ht'
        | (by_cases hu : t' = u
           · subst hu; simp [upd_self] at ht'
           · simp only [upd_ne _ _ hu] at ht'
             obtain ⟨e, hem, het⟩ := h t' ht'
             exact ⟨e, List.mem_filter.2 ⟨hem, by simp [het]; exact hu⟩, het⟩)
  | cancelTree root =>
    simp only [step, applyCancelTree]; intro ht'
    by_cases hmem : t' ∈ descendantsOf s root
    · rw [if_pos hmem] at ht'; (repeat' split at ht') <;> simp_all [TaskState.isTerminal]
    · rw [if_neg hmem] at ht'
      obtain ⟨e, hem, het⟩ := h t' ht'
      exact ⟨e, List.mem_filter.2 ⟨hem, by simp [het]; exact hmem⟩, het⟩
  | spawn a =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd] at ht'; split at ht' <;> first | exact h t' ht' | simp_all)
  | schedule =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd] at ht'; split at ht' <;> first | exact h t' ht' | simp_all)
  | yield u =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd] at ht'; split at ht' <;> first | exact h t' ht' | simp_all)
  | complete u =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd] at ht'; split at ht' <;> first | exact h t' ht' | simp_all)
  | spawnChild u a =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd] at ht'; split at ht' <;> first | exact h t' ht' | simp_all)
  | restartOne p c a =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd] at ht'; split at ht' <;> first | exact h t' ht' | simp_all)
  | send u b m =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd, wakeOne] at ht'; (repeat' split at ht') <;>
                 first
                 | exact h t' ht'
                 | exact absurd ht' (by simp)
                 | (obtain ⟨e, hem, het⟩ := h t' ht'
                    refine ⟨e, ?_, het⟩; simp_all [List.mem_filter]))
  | inject a m =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd, wakeOne] at ht'; (repeat' split at ht') <;>
                 first
                 | exact h t' ht'
                 | exact absurd ht' (by simp)
                 | (obtain ⟨e, hem, het⟩ := h t' ht'
                    refine ⟨e, ?_, het⟩; simp_all [List.mem_filter]))
  | receive u =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd] at ht'; (repeat' split at ht') <;>
                 first | exact h t' ht' | simp_all)
  | receiveByOccurrence u occ =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd] at ht'; (repeat' split at ht') <;>
                 first | exact h t' ht' | simp_all)
  | receiveFrom u src =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd] at ht'; (repeat' split at ht') <;>
                 first | exact h t' ht' | simp_all)
  | receiveUntil u d =>
    simp only [step]; (repeat' split) <;> intro ht' <;>
      first | exact h t' ht'
            | (simp only [upd] at ht'; (repeat' split at ht') <;>
                 first
                 | exact h t' ht'
                 | exact absurd ht' (by simp)
                 | (obtain ⟨e, hem, het⟩ := h t' ht'
                    exact ⟨e, Timer.mem_insertSorted.2 (Or.inr hem), het⟩)
                 | simp_all)
  | acquire u => simp only [step]; (repeat' split) <;> intro ht' <;> exact h t' ht'
  | acquireActor a => simp only [step]; (repeat' split) <;> intro ht' <;> exact h t' ht'
  | release u r => simp only [step]; (repeat' split) <;> intro ht' <;> exact h t' ht'
  | finalize r => simp only [step]; (repeat' split) <;> intro ht' <;> exact h t' ht'
  | setPriority u p => simp only [step]; (repeat' split) <;> intro ht' <;> exact h t' ht'
  | setDeadline u d => simp only [step]; (repeat' split) <;> intro ht' <;> exact h t' ht'
  | closeActor a => simp only [step]; (repeat' split) <;> intro ht' <;> exact h t' ht'
  | shutdown => intro ht'; exact h t' ht'
  | stopWhenIdle => simp only [step]; (repeat' split) <;> intro ht' <;> exact h t' ht'
  | stopWhenDrained => simp only [step]; (repeat' split) <;> intro ht' <;> exact h t' ht'

theorem run_preserves_sleepingHasTimer {s : RuntimeState} (h : SleepingHasTimer s)
    (ops : List RuntimeOp) : SleepingHasTimer (run s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih => exact ih (step_preserves_sleepingHasTimer h op)

theorem reachable_sleepingHasTimer (ops : List RuntimeOp) :
    SleepingHasTimer (run RuntimeState.init ops) :=
  run_preserves_sleepingHasTimer sleepingHasTimer_init ops

/-- A quiescent runtime (no running task, empty ready queue, **empty timer
queue**) has no sleeping tasks: a sleeping task would need a timer, but there
are none. This is the fact that unblocks multi-step drained permanence. -/
theorem quiescent_no_sleeping {s : RuntimeState} (h : SleepingHasTimer s)
    (hq : RuntimeQuiescent s) (t : TaskId) : s.taskState t ≠ some .sleeping := by
  intro ht
  obtain ⟨e, hem, _⟩ := h t ht
  rw [hq.2.2] at hem
  exact absurd hem (List.not_mem_nil e)

end Henret
