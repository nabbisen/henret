# Henret Development Handoff — v0.4.0 → v0.5.0

**Date:** 2026-06-05
**Versions covered:** v0.4.0 (RFC 028–029), v0.4.1 (RFC 030), v0.5.0 (RFC 031, 034)
**Context:** This document covers the three rounds of work since the external
architecture review of v0.3.1. The v0.4.0 review identified two semantic
frontier items as priorities; this document records what shipped, what was
deliberately excluded, and what the next round inherits.

---

## Part 1 — v0.4.0: schedulable completeness + blocked receive (RFC 028–029)

### What the v0.3.1 review named as priorities

The v0.3.1 reviewer approved the work as public-quality and named two specific
next steps: "the ready-queue completeness direction and the blocked-receive
direction." Both shipped in v0.4.0.

### RFC 028 — schedulable completeness

**What it added.** `WellFormed.runnable_queued` became the tenth WellFormed
field: every runnable task is in the ready queue. This is the converse of
`readyQ_queued` (which was already field 1 since v0.2.0): the queue is
exactly the runnable tasks, neither more nor less. The headline theorems are
`reachable_runnable_is_queued` and `reachable_queue_exact`.

**Why it matters.** Without this, the model could "lose" a runnable task: a
task transitions to `.ready` and no operation ever puts it in the queue, so
it waits forever. RFC 028 makes this provably impossible in every reachable
state.

**How it was proved.** Each of the nine preservation theorems was extended
with a tenth sub-proof. For most operations the sub-proof is a
contradiction-from-taskState argument: e.g. spawn creates `.new` tasks (not
runnable), so the runnable_queued obligation is vacuous. The interesting cases
are `schedule` (which moves `.new`/`.ready`/`.yielded` to the queue) and
`complete`/`cancel` (which must show the terminal state isn't runnable, hence
no obligation). The `tick` case required threading the woken-list disjointness
lemma (`hdisj : ∀ a ∈ readyQ, a ∉ woken`) to show the woken tasks are newly
runnable and appear exactly once.

### RFC 029 — blocked receive semantics

**What it added.** A new `StepResult.blocked` distinct from `.invalid`. An
empty own-mailbox receive was changed from returning `(s, .invalid)` to
`(s, .blocked)` — the state is still unchanged, but the result label is now
a legal "I need to wait" signal rather than a protocol error. The theorems
`receive_empty_blocked` and `step_blocked_unchanged` made this machine-checked.

**The transitional framing.** RFC 029 deliberately said the following in the
README and matrix: *"blocked is currently a no-op result, not a
waiting-state transition — wait queues and blocked-task parking are future
work."* This was intentional: the semantic decision (blocking is legal, not
invalid) was worth proving early even though the execution-management
consequence (actually park the task) was not yet modeled. RFC 031 completes
that arc.

**What it did not do.** The running task stays in `.running`. The task
remains in `running`. The ready queue is unchanged. No `mailboxWaiters`
field exists yet. Nothing about when a blocked task would be re-scheduled is
modeled or claimed. These were all explicitly deferred to RFC 031.

### v0.4.0 headline proof count

After v0.4.0: 10 WellFormed fields, 49 proof-matrix entries, `reachable_wf`
as the crown theorem integrating all ten.

---

## Part 2 — v0.4.1: public claim cleanup (RFC 030)

The v0.4.0 review found five release-blockers, all editorial rather than
semantic:

1. `inject` was missing from the README operation list.
2. The proof index described an old grammar (fewer operations).
3. `WellFormed` was described by a stale field count.
4. The `Henret.Proofs` barrel had a hard-coded count in its docstring.
5. The blocked/invalid framing was added in the matrix but not yet reflected
   in the README proof summary.

All five were fixed in v0.4.1. Additionally, demo scenario 7 was split to
show blocked vs invalid receive as distinct behaviors. No proof content
changed; axiom audit is byte-identical to v0.4.0.

---

## Part 3 — v0.5.0: preservation-proof modularity + blocked waiting state (RFC 034, 031)

### RFC 034 — preservation-proof modularity (infrastructure)

**What it did.** `InvariantsPreservation.lean` was a single 780-line file
containing all nine per-operation WellFormed preservation proofs.
RFC 034 split it into three focused files plus a 102-line assembly:

```
Henret/Proofs/Preservation/
  Lifecycle.lean   — spawn, schedule, yield, complete, cancel
  Messaging.lean   — send, receive, inject
  Time.lean        — sleep, tick, wake
Henret/Proofs/InvariantsPreservation.lean  (dispatch only)
```

**Why it was done before RFC 031.** RFC 031 adds four new WellFormed fields
and touches every preservation proof. Doing the split first means the RFC 031
changes go into three short focused files rather than one 800-line monolith.
The reviewer's sequencing advice ("034 first, then 031 or 032") was correct.

**Zero semantic change.** Every theorem name, statement, and axiom-audit
result is identical to v0.4.1. The refactor was pure reorganization.

### RFC 031 — blocked waiting state + mailbox wait queue

#### The design decision

RFC 029 left a task in `.running` state after a blocked receive. RFC 031
changes that: a blocked receive parks the task, and message delivery wakes
a waiter. Three design alternatives were considered and recorded:

**Alternative A (rejected): `waitingOn : TaskId → Option ActorId`.** Under
the actor-local receive discipline (RFC 024), a task can only ever wait on
its own actor's mailbox, so `waitingOn t` would always equal `taskOwner t`.
Redundant field with its own coherence obligation. Rejected.

**Alternative B (rejected): `mailboxWaiters` alone, no new TaskState.** The
task's situation would be invisible in `taskState`, breaking the model's
convention that `taskState` is the authoritative lifecycle view (sleeping
tasks are visible both as `.sleeping` and as timer entries). Rejected.

**Decision: hybrid — `TaskState.waiting` + `mailboxWaiters`.** This mirrors
the timer pattern exactly:

| domain | task-state field | side structure | coherence invariant |
|---|---|---|---|
| time | `.sleeping` | `timers : List TimerEntry` | `timers_sleep` |
| messaging | `.waiting` | `mailboxWaiters : ActorId → List TaskId` | `waiters_waiting` |

Every proof pattern needed for RFC 031 already existed in the timer corpus.
This symmetry was a maintainability argument that held up through
implementation.

#### What shipped

**Model changes:**
- `TaskState.waiting` constructor.
- `RuntimeState.mailboxWaiters : ActorId → List TaskId` (init: `fun _ => []`).
- `receive` (empty-mailbox valid branch): parks the running task, clears
  `running`, appends to `mailboxWaiters a`. Result remains `.blocked`.
- `send`/`inject` (valid branch): if `mailboxWaiters a = w :: ws`, wakes `w`
  to `.ready`, appends to `readyQ`, trims `mailboxWaiters a` to `ws`. If
  `mailboxWaiters a = []`, behavior is unchanged from v0.4.1.
- `cancel`: filters the task from its owner's `mailboxWaiters`.

**Four new WellFormed fields (11–14):**
- `waiters_waiting`: every task in `mailboxWaiters a` has `taskState =
  some .waiting`.
- `waiters_owned`: every task in `mailboxWaiters a` has `taskOwner = some a`.
- `waiting_queued`: every `.waiting` task appears in its owner's
  `mailboxWaiters`.
- `waiters_nodup`: each `mailboxWaiters` list is duplicate-free.

These four fields plus the existing `timers_sleep`/`timers_nodup` constitute
the complete coherence discipline: the waiting state and its queue are always
consistent with the rest of the state.

**Headline theorem delivered:**
- `receive_empty_parks`: states the exact step result for a parking receive
  (in `Messaging.lean`). Kernel-checked.

**Preservation proofs (the bulk of the implementation effort):**
- All nine per-operation preservation theorems extended to prove all 14 WF
  fields (up from 10).
- The Lifecycle file's `cancel` proof required a case split on `taskOwner t`
  to handle the filtered `mailboxWaiters` update correctly.
- The Messaging file's send/inject proofs required full case trees over the
  nil (no waiter) and cons (wake-one) branches. The receive proof required
  three branches: valid dequeue (no parking), parking (the new branch), and
  all the invalid cases.
- The Time file's sleep/tick/wake proofs needed four new sub-proofs each, but
  all four close by pass-through — time operations do not touch
  `mailboxWaiters`.

#### Mesa semantics: a deliberate choice with consequences

The woken task does **not** atomically consume the message. It is made
`.ready`, is scheduled at some future point, and then re-issues `receive`.
If another task consumed the message first, the re-issued receive parks
again — legal and well-defined.

This was a deliberate rejection of Hoare-monitor semantics (atomic handoff).
The reason: atomic handoff would make one task's `send` produce a result on
behalf of a different task, breaking the one-operation-one-subject shape of
`step` and most of the proof corpus. The consequence, which is documented and
not hidden: **no per-message delivery guarantee is claimed**. If a woken task
is cancelled before it runs, the message waits for the next delivery's
wake-one.

#### What RFC 031 explicitly excludes

The RFC text lists these as out of scope and records them as decided
alternatives:

- **`reachable_waiters_exact`** (the RFC's own acceptance-criteria theorem):
  "every waiting task is in exactly one `mailboxWaiters` list, and
  `mailboxWaiters a` contains exactly the tasks waiting on `a`." The four
  new WellFormed fields establish the weaker properties (a waiting task IS
  in some list, the list IS only waiting tasks), but the "exactly one" global
  uniqueness claim — comparable to `reachable_queue_exact` for the ready
  queue — was not proved. The fields imply it derivably, but the derivation
  was not written. This is the gap between the RFC's acceptance criteria and
  what shipped.

- **End-to-end demo scenario**: the RFC acceptance criteria called for a
  demo scenario showing park → deliver → wake → re-receive → consume as a
  checked scenario. This was not added to `henret-demo`. The model behavior
  is exercised by `receive_empty_parks` (a direct step-result theorem), but
  not as an `#eval`-able scenario with runtime assertions.

- **Selective receive**: a task receiving only messages matching a predicate.
  Out of scope.

- **Receive with timeout**: a sleeping + waiting combination (wait for a
  message OR a timer). Out of scope. The composition point would be: a
  waiting task with a deadline that `wake` can fire. The RFC notes this would
  require `wake` to be able to target a `.waiting` task — currently `wake`
  rejects non-sleeping targets.

- **Wake-all semantics**: waking every waiter on delivery. Rejected because
  it causes thundering herd (all but one immediately re-block) and makes
  woken-set reasoning non-trivial.

- **Fairness and liveness**: "a waiting task is eventually woken." Out of
  scope. The model makes no scheduling policy claims.

- **Blocked sends**: a `send` that parks if the mailbox is full. Out of scope.
  Mailboxes are unbounded in this model.

---

## Part 4 — Engineering notes: Lean 4 proof obstacles

Two systematic obstacles consumed significant implementation effort and are
worth recording for the next round:

### Obstacle 1: `subst` on outer pattern variables

In tactic proofs inside refine bullets, when a variable comes from a case
pattern (`| cons w ws =>`) and another variable comes from an intro
(`intro u`), using `rintro rfl` or `subst` on an equality `u = w` can
eliminate `w` (the outer pattern variable) rather than `u` (the inner
intro variable), leaving `w` as "unknown identifier" in subsequent steps.

**The fix**: avoid `subst` entirely when one side of the equality is a
case-pattern variable. Use `by_cases hue : u = w` without subst, or
`h ▸ e` term-mode rewrites that rewrite in the type without variable
elimination.

### Obstacle 2: `if True then` after `simp [hrt]`

Using `hrt : s.running = some t` in a `simp only [...]` set causes simp
to rewrite `if s.running = some t then …` to `if True then …` — but
`if True then …` does not reduce further unless `if_true` is in the simp
set. The result: step expressions appeared only partially evaluated.

**The fix**: use full `simp` (not `simp only`) for any step-reduction tactic
that includes `hrt`, because full simp includes `if_true` automatically.
Alternatively, add `if_pos rfl` explicitly to `simp only` calls after the
outer condition has been rewritten.

### A structural note on the preservation architecture

The Messaging preservation proofs grew substantially in v0.5.0: the file went
from ~60 lines to ~700 lines for send/receive/inject. The nil (no-waiter)
branches are close to the pre-RFC-031 proofs; the cons (wake-one) branches and
the parking branch are new and each require 14 sub-proofs. The main structural
pattern that works reliably is:

1. `have hstep : (step s .op).1 = { s with field₁ := ..., ... } := by simp [...]`
2. `rw [hstep]`
3. `refine ⟨?_, ?_, ..., ?_⟩` (14 holes)
4. For fields that are genuinely unchanged (e.g. timers, taskOwner), pass
   `h.field` directly.
5. For fields that touch `upd`: use `upd_ne _ _ hue` (u ≠ w) or `upd_self`
   (u = w) to reduce the if-expression. Do not use `subst`.
6. For mailboxWaiters membership: use `by_cases hab : a' = b` then
   `simp only [if_pos hab]` (not `rw [hab]`) to normalize the membership
   in a lambda-applied if-expression.

---

## Part 5 — What the next round inherits

### Proof surface as of v0.5.0

- 56 proof-matrix entries (all PROVEN or TESTED or OUTSCOPE, none with `sorry`)
- `WellFormed`: 14 fields, `wf_init` proves all 14 for the initial state
- `reachable_wf`: every reachable state satisfies all 14 fields
- Axiom audit: `[propext, Quot.sound]` only for all theorems in the core

### Two open gaps from this round

1. **`reachable_waiters_exact`** is derivable from the four new WellFormed
   fields but was not written. It is the most natural next proof in the RFC
   031 story: every `.waiting` task appears in exactly one `mailboxWaiters`
   list (uniqueness), and that list contains exactly the tasks waiting on that
   actor (completeness). The uniqueness half follows from `waiters_owned`
   (a waiter's owner is determined, so it can only appear in one list) plus
   `waiters_nodup` within each list. A future session could add this as a
   derived corollary to `InvariantsPreservation.lean`.

2. **The end-to-end parking demo** was listed in RFC 031's acceptance
   criteria but not implemented. A scenario showing the park → deliver →
   wake → re-receive → consume round-trip as a checked `henret-demo`
   scenario would complete RFC 031 as written.

### The two proposed RFCs (032 and 033)

**RFC 032 — actor-scoped spawn and supervision groundwork.** Adds
`spawnChild t a` (running task creates a child task) and a
`taskParent : TaskId → Option TaskId` field. The headline theorem is
`parent_lt` (child ids are strictly greater than parent ids), from which
`parent_chain_terminates` (the parenthood chain reaches a root in finitely
many steps) follows. This is groundwork for supervision trees — cascade
cancel and restart policies are explicitly deferred. RFC 032 is independent
of RFC 033.

**RFC 033 — message envelope and occurrence identity.** Wraps the bare
`Message` type in an `Envelope` carrying an occurrence id (fresh per
delivery) and a source actor. This closes two documented gaps: (1) the RFC
022 deferral ("occurrence identity not modeled") and (2) the PROVENANCE NOTE
in RFC 024/026 ("the model cannot connect a received message to its sending
actor"). The headline theorem is `reachable_occurrence_unique` (occurrence
ids are injective across all delivered messages in any reachable state). RFC
033 is a breaking change to the grammar type signature (mailboxes change from
`List Message` to `List Envelope`).

**Sequencing note.** RFC 032 is pure additive (new field, new operation
variant, new invariants). RFC 033 is a breaking change. If both are
targeted, RFC 032 first avoids doing the Envelope migration twice.

### Claim gaps to be aware of

The proof-trust-test matrix OUTSCOPE entries have been stable since v0.3.1
and represent genuine model-level decisions, not omissions:

- **Liveness and fairness** (`WellFormed` is a safety invariant; progress
  claims require a scheduling policy model that is deliberately absent).
- **Concurrency** (the model is a sequential state machine; concurrent
  access, race conditions, and lock-freedom are all OUTSCOPE).
- **C FFI conformance** (`Henret.Native` axioms are declared but the `extern`
  linkage and differential tests remain planned follow-up work since v0.1.0).
- **Occurrence identity within the current `Message` type** (RFC 022 gap,
  addressed by RFC 033 when it ships).

---

## Summary table

| Version | RFCs | Key additions | Gaps carried forward |
|---|---|---|---|
| v0.4.0 | 028, 029 | `runnable_queued` (10th WF field); `StepResult.blocked`; `receive_empty_blocked`; `step_blocked_unchanged` | Blocked receive is a no-op result only; no `.waiting` state |
| v0.4.1 | 030 | Editorial fixes (5 release-blockers); demo scenario 7 | None (no semantic change) |
| v0.5.0 | 034, 031 | Preservation-proof split (RFC 034); `TaskState.waiting`; `mailboxWaiters`; 4 new WF fields (→ 14); park/wake-one semantics; `receive_empty_parks` | `reachable_waiters_exact` not proved; no end-to-end parking demo scenario; Mesa-semantics liveness not claimed |

