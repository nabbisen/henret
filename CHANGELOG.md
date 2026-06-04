# Changelog

## v0.2.1 — review-hardening release (RFCs 019–023)

Resolves all five must-fixes of the v0.2.0 follow-up review.

### Added
- `WellFormed` strengthened to nine fields: `timers_sorted`,
  `spawned_has_owner`, `owned_has_mailbox`; preservation re-proved for all
  ten operations; new headlines `reachable_spawned_has_owner`,
  `reachable_owner_has_mailbox`, `reachable_timers_sorted` (RFC 019).
- `scripts/axiom_audit.py` — exact per-theorem axiom allowlist; rejects any
  unexpected project axiom; negative cases validated (RFC 020).
- `scripts/check.sh` gate 6 — documentation-consistency grep (RFC 021).
- Demo scenario 6 rebuilt: arbitrary-state stale-timer entry, asserting the
  tick filter consumes it and wakes nothing (RFC 021).
- `wakeOne_none` / `wakeMany_none` — waking never spawns.

### Changed
- `drivePopB` renamed `driveStackB` with an explicit orientation note
  relative to `DequeModel.toList`; `execDemo` framing removed (RFC 023).
- Message non-duplication claims scoped to per-operation value semantics;
  occurrence identity recorded as future work (RFC 022).
- Scenario counts and changelog history corrected (RFC 021).


## v0.2.0 — invariant discipline (review-resolution release)

Resolves all seven must-fix findings of the v0.1.0 architecture review
(`docs/reviews/v0.1.0-review-resolution.md`). Model changes: `RuntimeState`
gains `taskOwner` (RFC 014) and `now` (RFC 015); `tick` is guarded monotone
and wakes only genuinely sleeping tasks.

### Added
- `WellFormed` reachability invariant; `step/run_preserves_wf`,
  `reachable_wf`; ownership-location disjointness corollaries (RFC 013).
- `taskOwner` field; `spawn_sets_owner`, `step/run_preserves_owner`,
  `step_preserves_spawned` (RFC 014).
- `now` field; monotonic tick guard; `tick_advances_clock`,
  `tick_backwards_invalid`, `step_clock_monotone` (RFC 015).
- `step_invalid_unchanged` (RFC 016).
- `scripts/check.sh` five-gate release script + GitHub Actions CI (RFC 017).
- Documentation consistency sweep: accurate lifecycle transition tables,
  standardized native-boundary wording (RFC 018).
- Demo scenario 6: seven regression checks for the v0.2.0 model.
- Examples 02/05 extended (`taskOwner`, monotone clock).

### Changed
- `tick now` filters its woken list to tasks whose state is `.sleeping`,
  keeping the ready queue clean in arbitrary states (review must-fix 4).
- Timer theorems take a `s.now ≤ now` validity hypothesis.


## v0.1.0 — 2026-06-04

First public release: the Lean-only actor/task model.

### Added
- `Henret` Lean-only core package (Lean 4.15.0 / Lake; no native deps).
- Actor/task model: `TaskId`/`ActorId`, `TaskState` lifecycle with terminal
  `completed`/`cancelled`, `Message`/`Mailbox`/`ActorState` (RFC 004).
- Scheduler semantics: `RuntimeOp` grammar, total executable
  `step`/`run`/`runTrace`, invalid ops are guaranteed no-ops (RFC 005).
- Message/wake semantics with ownership and exactness proofs (RFC 006).
- Logical-time timers: sorted queue, `sleep`/`tick`/`wake`, no-early-wake and
  expired-wake proofs, sortedness preservation (RFC 007).
- Drivers: op-level fueled `driveOps` (tested) and model-level `drain` with
  proven liveness `drain_completes`.
- Refinement: `MailboxBackend` contract and two proven reference backends (RFC 008).
- Proof/trust/test matrix and proof/assumption/test indexes (RFC 009).
- `henret-demo` executable with five self-checking scenarios.
- Docs: README, positioning, naming/scope, prior-art, guided tour,
  refinement-contract pattern.
- RFC lifecycle directories per RFC 000 (`proposed/`, `done/`, `archive/`).

### Trust status
- 0 `sorry`, 0 custom axioms, 0 `native_decide`; `#print axioms` reports only
  `propext`/`Quot.sound` for all exported theorems.

### Added (continued — examples and full RFC closure)
- `examples/` directory with 9 self-contained educational examples
  (`01_task_lifecycle` through `09_optional_ffi_boundary`), each teaching one
  concept, all verified with `lake env lean`.
- `examples/README.md` learning-order index.
- RFC 011 (Examples and Guided Tour) → `rfcs/done/`.
- RFC 012 (Release, Docsite, and Community) → `rfcs/done/`; all 11 of 12 RFCs
  now done; RFC 010 (optional FFI boundary) landed later within v0.1.0
  (see the dedicated section below).

### Added (RFC 010 — Optional Native Backend Boundary)
- `Henret/Native/DequeModel.lean` — `DequeModel` abstract contract (6 laws,
  `toList` observation, analogous to `MailboxBackend`); `listDeque` reference
  implementation (laws by `rfl`); `qRun_tracks` (whole-program refinement,
  PROVEN, `propext` only); `drivePopB_complete` (LIFO driver liveness, PROVEN).
- `Henret/Native/Assumptions.lean` — 6 typed axioms for `NativeDeque`; 
  `nativeDequeModel : DequeModel`; `nativeDequeModel_qRun_tracks` (PROVEN given
  the 6 axioms); axiom audit: `#print axioms` lists exactly 6 named axioms.
- `lakefile.lean` — `HenretNative` lib target (`lake build HenretNative`).
- `docs/native-backend-boundary.md` — the trust discipline, audit script,
  OUTSCOPE claims, conformance testing plan.
- `docs/assumption-index.md` — updated with 6 `NativeDeque` axioms.
- `docs/proof-trust-test-matrix.md` — rows 18–28 for native layer.
- `docs/proof-index.md` — native theorem inventory.
- `examples/09_optional_ffi_boundary.lean` — updated to use real modules.
- RFC 010 → `rfcs/done/`. All 12 RFCs now done.
