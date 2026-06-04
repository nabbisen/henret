# Henret Development Handoff — RFC 019–025

**Date:** 2026-06-04
**Versions covered:** v0.2.1 (RFC 019–023), v0.3.0 (RFC 024–025)
**Context:** This document covers the two rounds of work that followed the
external architecture review of Henret v0.2.0. The first round (v0.2.1,
RFC 019–023) responded directly to the reviewer's five must-fixes and two
actionable should-fixes. The second round (v0.3.0, RFC 024–025) implemented
the two "named next frontier" items the same reviewer left for future work.

---

## Part 1 — v0.2.1: Responding to the architecture review (RFC 019–023)

### What the reviewer found

The v0.2.0 review verdict was: *approve as internal work, but not yet a
clean public v0.2.x release.* The reviewer praised the v0.2.0 model changes
(ownership, logical time, tick filter, invalid-no-op theorem) as
directionally correct, and identified five must-fixes and two should-fixes.

The must-fixes in order of weight:

**Must-fix 1 — `WellFormed` was incomplete.**
The six-field invariant introduced in v0.2.0 was missing three things that
any honest global correctness claim needs. Timer sortedness was already proved
separately via `run_preserves_sorted`, but `reachable_wf` didn't subsume it —
you needed two theorems to say "this state is reachable and well-shaped."
More seriously, `WellFormed` said nothing about the ownership fields added in
v0.2.0: a well-formed state could have `taskState t = some .ready` and
`taskOwner t = none`, which is incoherent for an actor/task runtime model.
And it said nothing about whether the owning actor's mailbox actually exists.

**Must-fix 2 — Owner immutability was proved, but not owner existence.**
RFC 014 delivered `spawn_sets_owner` and `step/run_preserves_owner`, which
prove "if a task has an owner, the owner never changes." That's useful, but
the headline Henret should be able to deliver is "every reachable spawned
task has an owner" — the stronger positive claim. Without it, the ownership
theorems require callers to supply the existence as a hypothesis, which
pushes the burden back onto the user rather than grounding it in the model.

**Must-fix 3 — Demo scenario 6 did not actually test the stale-timer filter.**
This was the sharpest catch in the review. The scenario tested:
```lean
let s9 := run .init [.spawn 1, .schedule, .sleep 0 5, .cancel 0]
let (s9b, _) := step s9 (.tick 10)
check "stale timer task not re-queued" (!(s9b.readyQ.contains 0))
```
But `cancel` removes its target's timer entries in the same step. By the
time `.tick 10` runs, there is no stale entry left — the scenario was
testing that cancel did its job, not that the tick filter handled an
arbitrary-state entry. The test passed but claimed to prove something it
wasn't actually exercising.

**Must-fix 4 — The axiom audit was grep-based, not exact.**
Gate 5 of `scripts/check.sh` rejected `NativeDeque|sorryAx` from the
`#print axioms` output. That would miss a new project-specific axiom under
any other name — `axiom UnsafeRuntimeMagic`, for example, would sail
through. For a package whose central public claim is an explicit, bounded
trust surface, the audit must be exact: allowlist in, reject out,
bidirectionally.

**Must-fix 5 — Documentation consistency gaps remained after RFC 018.**
The demo count said "five scenarios" after scenario 6 was added.
`docs/test-index.md` listed scenarios 1–5 only. The CHANGELOG v0.1.0 section
contained the line "RFC 010 (optional FFI boundary) remains in `proposed/`"
— historically wrong, since RFC 010 had landed in v0.1.0. These are small
but they undermine RFC 018 ("documentation consistency sweep"), which was
specifically supposed to eliminate this class of drift.

The two should-fixes:

**Should-fix 6 — Message "ownership" was overclaimed.**
The `Messaging.lean` module docstring said a message "is never duplicated by
the model." This is only true per-operation: one `send` does one append. It
is not true globally: two separate `send` operations can deliver the same
`Message` *value* to any mailbox. Since `Message` is a value type (`id` and
`payload`), not an occurrence type, the non-duplication claim was misleading.

**Should-fix 7 — `drivePopB` had an orientation mismatch.**
`DequeModel.toList` is documented top → bottom, meaning the owner's end is
the list *back* and `popLast` removes it. `drivePopB` treated the list
*front* as the owner's end (a stack view, the natural recursion structure for
the fuel proof). The same file used both orientations without an explicit
bridge, and the docstring referenced `execDemo`, an executable Henret no
longer shipped.

---

### What was done, and why, for each

#### RFC 019 — Strengthened WellFormed Invariant

The six-field `WellFormed` structure gained three fields:

```lean
  timers_sorted : Timer.Sorted s.timers
  spawned_has_owner :
    ∀ t st, s.taskState t = some st → ∃ a, s.taskOwner t = some a
  owned_has_mailbox :
    ∀ t a, s.taskOwner t = some a → ∃ mb, s.mailboxes a = some mb
```

A few design decisions are worth explaining.

**Why add fields to `WellFormed` rather than keep them separate?**
The reviewer's acceptance criterion was explicit: "`reachable_wf` alone
should imply ready uniqueness, timer sortedness, timer/sleep coherence, owner
existence, owner-mailbox existence, and location disjointness." The point is
that a future maintainer (or a user) needs only one theorem to reason about
reachable states. Having `reachable_wf` and `reachable_timers_sorted` as two
independent theorems with separate preservation proofs is worse: it means
more moving parts, more places to forget to update when the model changes,
and a weaker story for users of the library.

**Why is `owned_has_mailbox` stated unconditionally over `taskOwner`, not
gated on spawnedness?**
The field `∀ t a, s.taskOwner t = some a → ∃ mb, s.mailboxes a = some mb`
doesn't require `taskState t = some st` as a precondition. This is
intentional. In practice, `taskOwner t = some a` only ever holds in reachable
states when the task was spawned (spawn is the sole write site, and spawn
sets both `taskState` and `taskOwner` atomically). But stating the stronger
form — owning-actor-exists regardless of spawnedness status — is both
simpler to apply and simpler to preserve. The preservation proof for
`owned_has_mailbox` under `spawn` just needs to show that the spawning actor's
mailbox exists after spawn (it does — spawn guarantees it) and that mailboxes
never disappear (they don't — no operation removes a mailbox). There is no
need to case-split on whether the task was previously spawned.

**Three new reachability headlines.**
With the nine-field invariant, the preservation theorem subsumes what had
previously been separate theorems:

```lean
theorem reachable_spawned_has_owner (ops) {t st}
    (h : (run .init ops).taskState t = some st) :
    ∃ a, (run .init ops).taskOwner t = some a

theorem reachable_owner_has_mailbox (ops) {t a}
    (h : (run .init ops).taskOwner t = some a) :
    ∃ mb, (run .init ops).mailboxes a = some mb

theorem reachable_timers_sorted (ops) :
    Timer.Sorted (run .init ops).timers
```

All three are one-liners projecting `reachable_wf ops`.

**The proof rework.** Extending `step_preserves_wf` from six to nine fields
meant adding three sub-proofs to each of the ten operation branches in
`Henret/Proofs/InvariantsPreservation.lean`. The new sub-proofs follow
mechanical patterns:

- `timers_sorted`: per branch, look up which timer operation happened (none,
  filter, insertSorted, remaining) and apply the corresponding existing
  sortedness lemma.
- `spawned_has_owner`: for operations that write `taskState` at a specific
  key `k`, check whether the queried id equals `k`. If yes, the old state
  had a `some` value there (guarded by the branch condition) so the old
  invariant gives the owner; the owner field is unchanged. If no, both
  `taskState` and `taskOwner` project through unchanged, so the old
  invariant applies directly.
- `owned_has_mailbox`: operations that don't touch mailboxes delegate to the
  old invariant; operations that do (spawn, send, receive, inject) need the
  per-op mailbox analysis. Two new lemmas in `Ownership.lean` —
  `wakeOne_none` and `wakeMany_none` — handle the tick branch: if
  `taskState t = none` before a tick, `wakeMany` leaves it `none` (waking
  never spawns), so the query for an owner is vacuously satisfied.

#### RFC 020 — Strict Axiom Audit Gate

The audit was rebuilt as `scripts/axiom_audit.py`, a 60-line Python script
that:

1. Parses `#print axioms` output for every allowlisted theorem. The output
   can wrap across lines, so the script collects the full bracketed list
   per theorem before comparing.
2. Checks each theorem's axiom set against a hardcoded allowlist:
   - Core and pure-native theorems: must be a subset of
     `{propext, Quot.sound}`.
   - `nativeDequeModel_qRun_tracks`: must *contain* all six `NativeDeque`
     axioms and be a subset of those six plus the standard set plus
     `Classical.choice` (which appears because the opaque `NativeDeque` type
     is constructed via `NonemptyType`).
3. Fails if any theorem has an unexpected axiom, if an expected axiom is
   missing, if a theorem appears in output but is not in the allowlist, or if
   an allowlisted theorem was not printed at all.

The bidirectionality is important: it prevents the audit from silently passing
if someone renames or removes a theorem from the audit file without updating
the allowlist. The negative case was validated explicitly by feeding the
script fabricated output containing a `UnsafeRuntimeMagic` dependency — exit
code 1, correct message.

A sixth gate was added to `check.sh` alongside the audit: a `grep` that
rejects a small set of known-stale phrases across the source tree. The gate
excludes `docs/reviews/` (which may legitimately quote the phrases it
documented fixing). This prevents the documentation consistency state from
silently regressing across releases.

#### RFC 021 — Documentation/Test Index Repair

The three documentation errors were straightforward fixes. The interesting
one was scenario 6.

The stale-timer scenario was rebuilt as an *arbitrary-state* test:

```lean
let stale : RuntimeState :=
  { RuntimeState.init with
      taskState := upd RuntimeState.init.taskState 0 (some .cancelled)
      timers    := [⟨5, 0⟩]
      nextId    := 1 }
let (stale', r9) := step stale (.tick 10)
check "stale timer entry consumed by tick" stale'.timers.isEmpty
check "stale timer task not woken" (r9 matches .woke [])
check "stale timer task not re-queued" (!(stale'.readyQ.contains 0))
check "cancelled stale-timer task unchanged" (stale'.taskState 0 == some .cancelled)
```

This state is not reachable (in a reachable state, `WellFormed.timers_sleep`
guarantees every timer entry's task is `sleeping`, never `cancelled`), which
is precisely the point. The filter `fun u => s.taskState u = some .sleeping`
in the tick operation exists to harden the model against *arbitrary* states.
The regression test must exercise that hardening, not just confirm that a
reachable-state invariant holds.

The reachable-state path is tested separately:

```lean
let s9 := run .init [.spawn 1, .schedule, .sleep 0 5, .cancel 0]
check "cancel drops the pending timer" s9.timers.isEmpty
```

This confirms that in reachable states the issue doesn't arise because
`cancel` removes the timer eagerly — but that's a separate fact, tested
separately.

#### RFC 022 — Message Occurrence Semantics

This was a documentation-only fix. The `Messaging.lean` module docstring was
updated to scope the non-duplication claim to per-operation value semantics:
one `send` does one append; one `receive` does one head removal. The global
claim that "a message is never duplicated" was removed.

The RFC also records the design sketch for a future occurrence model: a fresh
`MessageId` counter in `RuntimeState`, a `WellFormed` field asserting each
message occurrence lives in exactly one mailbox, and send/receive preservation
proofs over that. This is left for a future RFC once actor-scoped semantics
demonstrate the need.

#### RFC 023 — Deque Driver Orientation Cleanup

`drivePopB` was renamed `driveStackB`. The docstring now carries an explicit
orientation note explaining that the driver works in the owner's-eye (stack)
view — list front as owner's end — which is the reverse of `DequeModel.toList`'s
top → bottom orientation. The translation between the two views is
`List.reverse`. The `execDemo` framing was removed; the liveness theorem
stands on its own merits.

The rename touched seven files (`DequeModel.lean`, `Assumptions.lean`,
`check.sh`, `docs/proof-index.md`, `docs/proof-trust-test-matrix.md`,
`docs/native-backend-boundary.md`, `examples/09`). Historical RFC and
CHANGELOG entries were left with the old name (they describe their release
accurately); only live code and current documentation were updated.

---

## Part 2 — v0.3.0: The actor-scoped frontier (RFC 024–025)

### Why these two items, and why now

The v0.2.0 reviewer named two items as the natural next frontier after the
v0.2.1 hardening was done: actor-scoped send/receive (should-fix 8) and
import granularity (should-fix 9). Both had been deferred from v0.2.0 on the
grounds that invariant discipline should come first. With `WellFormed` now
nine fields strong, `reachable_spawned_has_owner` and `reachable_owner_has_mailbox`
proven, and the release gate exact, the model was stable enough to carry a
breaking change.

The two items are related. Actor-scoped operations require the ownership
relation to exist in the model *and* be provably stable — both of which
`WellFormed.spawned_has_owner` and `WellFormed.owned_has_mailbox` establish.
And adding operations to the grammar is the kind of change that benefits
from import granularity: users who only want to run the model shouldn't have
to elaborate the expanded proof corpus.

---

### RFC 024 — Actor-Scoped Operations

#### The problem with the v0.2.1 grammar

Through v0.2.1, the messaging operations were:

```lean
| send (a : ActorId) (m : Message) : RuntimeOp
| receive (a : ActorId) : RuntimeOp
```

Both are *global*: any caller can name any actor's mailbox without any task
involvement. This means the model cannot say anything about who does the
sending or receiving — there is no actor-local receive discipline to prove,
because the operation has no task reference.

From a modelling standpoint this is wrong. In an actor model, messages are
sent *by actors* (acting through their running tasks) and received *by
actors* (from their own mailboxes). The delivery path from outside the system
(the environment, a test harness, the initial setup) is distinct and should
be named explicitly. Collapsing both paths into one operation obscures the
distinction and makes the model weaker.

From a proof standpoint, the absence of task involvement also means the
preservation proofs for `WellFormed.owned_has_mailbox` under `send` had to do
substantial work: they needed to cover every combination of guards to show
the mailbox update was safe. With task-scoped operations, most of that
complexity moves into the operation's own guards.

#### The design

The grammar was refactored to three operations (eleven total):

```lean
| send    (t : TaskId) (b : ActorId) (m : Message)
| receive (t : TaskId)
| inject  (a : ActorId) (m : Message)
```

**`send t b m`** — the running task `t` sends message `m` to actor `b`.
Guards: `t` is the currently running task, `t` is in `running` state
(defensive — the running slot implies this in reachable states, but we
guard explicitly for arbitrary-state robustness), `t` has an owning actor
(sender provenance — the operation records that a real actor's task performed
the send), and `b`'s mailbox exists.

**`receive t`** — the running task `t` dequeues from its **own** actor's
mailbox. The critical design point: the actor's identity is *derived* from
`taskOwner t`, never passed by the caller. This is not a convenience feature;
it is the thing that makes actor-local receive discipline a theorem rather
than a convention. If the caller named the mailbox, you could write `.receive
t` against any actor's mailbox, and the model would be no stronger than
before.

**`inject a m`** — the environment (or test harness, or setup code) appends a
message to actor `a`'s mailbox with no task involvement. This is what the
old `send` was. It is kept because it is legitimate: messages arrive from
outside the modeled system, and the model should have a name for that path.
Removing it would make the demo and setup code awkward. The name `inject`
distinguishes it clearly from the actor-to-actor path.

Note that `spawn` remains an environment operation. Extending it to parent-task
spawn (supervision trees) is the natural next step but was out of scope —
that is a richer semantic territory (parent-child relationships, restart
policies, actor hierarchies) that deserves its own RFC.

#### The headline theorem

The design goal was a single provable statement of actor-local receive
discipline:

```lean
theorem receive_only_own {s : RuntimeState} {t : TaskId} {m : Message}
    (h : (step s (.receive t)).2 = .received m) :
    ∃ a mb mb',
      s.taskOwner t = some a ∧
      s.mailboxes a = some mb ∧
      mb.dequeue = some (m, mb') ∧
      ((step s (.receive t)).1).mailboxes a = some mb' ∧
      ∀ b, b ≠ a → ((step s (.receive t)).1).mailboxes b = s.mailboxes b
```

Given any successful receive (result `.received m`), the theorem witnesses
the unique actor whose mailbox was touched, the exact pre- and post-dequeue
states of that mailbox, and the non-disturbance of every other mailbox. The
hypothesis is purely on the result — no guards need to be supplied by the
caller. The proof works by full case analysis: every guard-failure branch
returns `.invalid`, so `.received m` in the result immediately rules them
out.

The guard theorems are separately proved:

```lean
theorem send_not_running_invalid (h : s.running ≠ some t) (m) :
    step s (.send t b m) = (s, .invalid)

theorem send_unowned_invalid (how : s.taskOwner t = none) (m) :
    (step s (.send t b m)).2 = .invalid

theorem receive_unowned_invalid (how : s.taskOwner t = none) :
    (step s (.receive t)).2 = .invalid
```

These make the operation guards explicit as theorems rather than conventions.

#### `Henret.Proofs.StepProjections` — the engineering insight

Adding `inject` and changing `send`/`receive` to task-scoped forms meant
every case-analysis proof in the codebase needed new branches — at minimum
one for `inject`, and modified cases for `send`/`receive`. There are five
such proofs: `step_preserves_terminal`, `step_invalid_unchanged`,
`step_clock_monotone`, `step_preserves_sorted`, `step_preserves_spawned`,
`step_preserves_owner`, and the nine-field `step_preserves_wf`.

The key observation: all three messaging operations touch *only* `mailboxes`.
Every other field — `taskState`, `taskOwner`, `readyQ`, `running`, `timers`,
`now`, `nextId` — is unchanged by send, receive, and inject in every branch
(valid or invalid). Proving this once per projection, as a `@[simp]` lemma,
eliminates the entire problem for six of the seven proofs:

```lean
@[simp] theorem send_taskState : ((step s (.send t b m)).1).taskState = s.taskState
@[simp] theorem receive_readyQ : ((step s (.receive t)).1).readyQ = s.readyQ
@[simp] theorem inject_timers  : ((step s (.inject a m)).1).timers  = s.timers
-- ... 21 lemmas total (7 projections × 3 operations)
```

With these as `@[simp]` lemmas, the send/receive/inject cases in every
downstream proof reduce to a single `simp [h]` line — Lean's simp procedure
fires the relevant projection lemma, rewrites the step expression away, and
the conclusion follows immediately from the old hypothesis.

The `step_preserves_wf` case for `owned_has_mailbox` is the one that can't
use projections (mailboxes do change), but even there the pattern is
compressed by three mailbox-monotonicity lemmas proved once in
`Messaging.lean`:

```lean
theorem send_mailbox_isSome    (h : s.mailboxes c = some mb) (m) :
    ∃ mb', ((step s (.send t b m)).1).mailboxes c = some mb'

theorem inject_mailbox_isSome  (h : s.mailboxes c = some mb) (m) :
    ∃ mb', ((step s (.inject a m)).1).mailboxes c = some mb'

theorem receive_mailbox_isSome (h : s.mailboxes c = some mb) :
    ∃ mb', ((step s (.receive t)).1).mailboxes c = some mb'
```

Each says: if a mailbox existed before, it still exists after (with possibly
a different contents). These carry `owned_has_mailbox` through every messaging
branch in `step_preserves_wf` in two lines: retrieve the existing mailbox from
the old invariant, apply the monotonicity lemma.

**Total file sizes after the refactor:**
- `StepProjections.lean`: 157 lines (21 projection lemmas)
- `Messaging.lean`: 290 lines (rewritten from ~80 lines, now includes
  scoped theorems, guard theorems, monotonicity, and the discipline headline)
- `InvariantsPreservation.lean`: 658 lines (up from ~520; the added lines
  are the inject branch plus the simplified send/receive branches)

#### The demo and examples

The `mailboxScenario` in `Henret/Examples/Basic.lean` was reworked to reflect
the new grammar:

```lean
def mailboxScenario : RuntimeState × List StepResult :=
  runTrace .init
    [.spawn 7,               -- task 0, owned by actor 7
     .schedule,              -- task 0 becomes running
     .send 0 7 ⟨1, 100⟩,   -- running task 0 sends to its own actor
     .send 0 7 ⟨2, 200⟩,
     .receive 0]             -- task 0 receives from actor 7's mailbox
```

The assertions are unchanged (the demo still checks that message 1 was
received and message 2 remains), but the scenario is now semantically honest:
the sends are performed by a scheduled task acting on behalf of its actor.

Example 04 was rewritten as a showcase of the whole messaging discipline:
actor-to-actor send, environment inject, actor-local receive, and live
`invalid` results demonstrating that unscheduled and unowned tasks cannot
message.

---

### RFC 025 — Import Granularity

#### The problem

Through v0.2.1, `import Henret` imported:

```lean
import Henret.Proofs.Lifecycle
import Henret.Proofs.Messaging
import Henret.Proofs.Timers
import Henret.Proofs.Ownership
import Henret.Proofs.Invariants
import Henret.Proofs.InvariantsPreservation
import Henret.Refinement.Contract
import Henret.Refinement.ReferenceBackend
import Henret.Examples.Basic       -- <-- was here
```

Users who only want to run the model — write some scenarios, test some
behaviours, copy the pattern — had to elaborate the entire proof corpus,
including the nine-field `step_preserves_wf` and the multi-level
`receive_only_own` case analysis. At ~2,000 lines of proof total (growing
with each RFC), this is a real cost.

More pointedly, `Henret.Examples.Basic` being a default library import is
wrong in principle. Example files demonstrate; they are not part of the
library's public API. Including them by default means any renaming or
restructuring of the scenarios becomes a breaking change to users of the
library.

#### The solution

Four import paths now cover the natural user personas:

**`import Henret.Model`** — the light model import. Core identifiers,
task/actor state, the operation grammar, timers, `step`, `run`, the drivers,
plus the lightweight structural lemmas those modules carry inline (`upd`
lemmas, `Mailbox.dequeue_spec`, timer sortedness, `drain_completes`). It does
not import the heavy proof corpus under `Henret.Proofs` — `#check
@Henret.reachable_wf` is an unknown identifier after this import — but it is
a *light* import, not a definition-only one (clarified by RFC 027; a true
definition/lemma split is recorded there as possible future work).

**`import Henret.Proofs`** — all theorems about the model. Brings in
`Henret.Model` transitively. This is what a Lean developer wants when they
are proving properties of programs that use the Henret model.

**`import Henret.Refinement`** — the `MailboxBackend` contract and its
reference implementation. Brings in `Henret.Model` transitively. Useful for
developers implementing or verifying custom backends.

**`import Henret`** — `Henret.Model` + `Henret.Proofs` + `Henret.Refinement`.
The kitchen-sink import, unchanged in content from v0.2.1 except that
`Henret.Examples.Basic` is no longer included.

`Henret.Examples.Basic` is now explicitly imported by `Main.lean` (the demo
executable). Users who want to build on the example scenarios must opt in.
`Henret.Native.*` remains opt-in as before (RFC 010).

#### Verification

RFC 025's acceptance criterion was verified at package time:

```bash
echo "#check @Henret.reachable_wf" | lake env lean <file with import Henret.Model>
```

Lean reports `unknown identifier 'Henret.reachable_wf'` — the proof module
was not elaborated. The import barrier works.

---

## State of the project after v0.3.0

### What `reachable_wf` now means

The single theorem `reachable_wf (ops : List RuntimeOp) : WellFormed (run .init ops)` subsumes:

- The scheduler never duplicates a ready task.
- Every queued task is in a runnable state.
- The running slot holds a task in `running` state.
- Every timer task is sleeping; the timer queue is sorted by deadline.
- A task occupies at most one ownership location (derived from state
  uniqueness across the six location fields).
- Every spawned task has an owning actor.
- Every owning actor has a mailbox.
- Tasks above the fresh-id counter have never been spawned.

This is the invariant discipline the v0.2.0 reviewer asked for.

### What the actor-scoped grammar now means

In every reachable state, if a receive succeeds (`.received m`):
- The message came from the receiving task's own actor's mailbox.
- The actor was derived from ownership (`taskOwner`), not named by the caller.
- No other mailbox was touched.

This is not a policy or convention. It is `receive_only_own`, kernel-checked,
audit-clean (`propext` and `Quot.sound` only).

### What remains

The natural next items, in rough priority order:

**Supervision.** Parent-task `spawn` — the running task spawns a child,
establishing a parent-child relationship in the state — and actor-wide cancel
that follows the supervision tree. This requires adding `taskParent : TaskId
→ Option TaskId` to `RuntimeState` (analogous to `taskOwner`) and a new
`WellFormed` field for tree integrity. The ownership substrate from RFC 019
and the eleven-operation grammar from RFC 024 make this tractable.

**Message occurrence identity (RFC 022 deferred path).** If the model needs
to prove that a specific message was not duplicated at the occurrence level
(not just per-operation), a fresh `MessageId` counter in `RuntimeState` and a
`WellFormed` field asserting each occurrence lives in exactly one mailbox
would give that. The per-operation non-duplication theorems in `Messaging.lean`
are the necessary first step; this would be the sufficient one.

**Actor-scoped `spawn`.** Completing the actor-locality story for all
operations. Currently `spawn` names an actor but is performed by the
environment (not a running task). Making it task-scoped — "the running task
spawns a child for actor `a`" — would let the model prove that spawning is
always traceable to a parent task, which is the foundation for supervision.

**Import granularity further.** The current barrels work but are coarse.
A `Henret.Proofs.Core` containing only the lifecycle and ownership theorems
(the most commonly used), separate from `Henret.Proofs.Invariants` which is
heavy, would let proof-aware users avoid the full nine-field preservation
proof unless they need it. This is optimization rather than correctness.
