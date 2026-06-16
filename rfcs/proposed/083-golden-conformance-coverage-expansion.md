---
rfc: 83
title: Golden Conformance Coverage Expansion
status: Proposed
implemented_in: null
supersedes: []
superseded_by: []
depends_on: [80]
blocks: []
category: conformance
---

# RFC 083 — Golden Conformance Coverage Expansion

## Status

Proposed strategic RFC. Approved in the v0.17.0 audit review (item A3,
decision **A+B**, priority **P1**); amendments 083-A..E applied from the
RFCs 080-086 review. All `*_as_designed` placeholders are now resolved
against the **actual current model semantics** (`Henret/Scheduler/Model.lean`).

## Summary

Bring the golden conformance suite (RFC 047) back in line with the grammar.
It currently has 10 scenarios covering only features at or before RFC 033.
Extend it with positive and negative scenarios for every operation added
since, each with an **exact expected `StepResult` sequence and final-state
predicate** (not placeholders), require **semantic-branch** coverage rather
than mere constructor coverage, and add a durable coverage gate so the suite
can never silently drift behind the grammar again.

## Motivation

The golden suite is Henret's external-design regression artifact — what an
external runtime implementer runs to claim conformance. If it is a public
contract (RFC 047), it must track the grammar and must *define* behavior,
not defer it. Examples are not a substitute for scenarios with named
expected results.

## Goals

- A golden scenario for every operation/branch added since RFC 033.
- Exact expected results, extracted from the model, for each scenario.
- Negative/security scenarios proving forbidden operations reject / no-op.
- A coverage gate tying each `RuntimeOp` *branch* to evidence.

## Non-goals

- Replacing the example folder (examples stay as pedagogy).
- The external-adapter negative suite (RFC 073); see 083-C.
- Asserting anything about how an external runtime reports errors.

## 083-A — Scenario specification format

Each scenario specifies: initial state / op sequence; expected `StepResult`
sequence; expected final-state predicate; positive or negative; covered
`RuntimeOp` branches.

## Positive scenarios (exact results, from the model)

```text
receiveUntil_timeout_fast_path        (empty mailbox, deadline <= now)
  result: .timedOut ; state UNCHANGED (t stays .running, still running,
          no timer/waiter added, mailbox unchanged)

receiveUntil_park_future_deadline     (empty mailbox, deadline > now)
  result: .blocked ; taskState t = .waitingTimed ; running = none ;
          t in timedMailboxWaiters a ; timer <deadline,t> present ;
          waitDeadline t = some deadline

receiveUntil_park_then_tick_wakes     (continue prior, tick t' >= deadline)
  result: .woke [t] ; taskState t = .ready ; t in readyQ ;
          t not in timedMailboxWaiters a ; waitDeadline t = none ; timer gone

receiveUntil_message_before_deadline  (non-empty mailbox)
  result: .received env ; head env removed ; t stays .running

receiveByOccurrence_hit               (matching occurrence present)
  result: .received env ; matched env removed ; other order preserved

receiveByOccurrence_miss_parks        (no match)   [resolves "miss" branch]
  result: .blocked ; taskState t = .waiting ; running = none ;
          t in mailboxWaiters a    (it PARKS; it is not .invalid)

receiveFrom_source_hit                (matching source)
  result: .received env ; matched env removed ; other order preserved

receiveFrom_source_miss_parks         (no match)
  result: .blocked ; taskState t = .waiting ; t in mailboxWaiters a

fail_marks_failed                     (non-terminal t)
  result: .ok ; taskState t = .failed ; t removed from readyQ, timers,
          owner mailboxWaiters, all timedMailboxWaiters ; waitDeadline t =
          none ; running cleared if it was t

restartOne_spawns_replacement         [resolves "restores child/actor"]
  pre: parent running ; taskParent failedChild = some parent ;
       taskState failedChild = .failed ; nextId = n fresh
  result: .spawned n ; taskState n = .new ; taskOwner n = some actor ;
          taskParent n = some parent ; n appended to readyQ ;
          restartOf n = some failedChild ; nextId = n+1
  NOTE: a FRESH replacement task is spawned; the failed task is NOT revived.

closeActor_preserves_mailbox          [resolves "drains or preserves"]
  pre: mailbox a exists
  result: .ok ; actorStatus a = .closed ; mailbox a CONTENTS UNCHANGED
  NOTE: closeActor PRESERVES contents; it does not drain.

shutdown_sets_status
  result: .ok ; runtimeStatus = .shuttingDown ; idempotent (2nd shutdown:
          .ok, still .shuttingDown)

stopWhenIdle_quiescent                (running=none && readyQ=[] && timers=[])
  result: .ok ; runtimeStatus = .stopped

stopWhenIdle_nonquiescent             (otherwise)
  result: .invalid ; state UNCHANGED
```

## Negative / security scenarios (model-level)

```text
non_running_send_invalid          send t b m with running != some t -> .invalid; mailbox b unchanged
unowned_receive_invalid           receive t with taskOwner t = none   -> .invalid
waiting_task_cannot_send          send by a .waiting/.waitingTimed task -> .invalid (needs .running)
waiting_task_cannot_receive       receive/receiveUntil by non-.running  -> .invalid
cancelled_task_not_schedulable    after cancel t: t not in readyQ; schedule never selects it
closed_actor_rejects_send         actorStatus b = .closed -> send  -> .invalid; mailbox unchanged
closed_actor_rejects_inject       actorStatus a = .closed -> inject -> .invalid
shutdown_rejects_spawn            runtimeStatus != .running -> spawn  -> .invalid
shutdown_rejects_inject           runtimeStatus != .running -> inject -> .invalid
stale_timer_cannot_wake_cancelled cancel removes t's timers; tick wakes only
                                  .sleeping/.waitingTimed, never .cancelled
```

## 083-B — Branch coverage, not just constructor coverage

A constructor covered once is insufficient; cover semantic branches. E.g.
`receive` has: valid non-empty own-mailbox; valid empty own-mailbox parks;
invalid non-running; invalid unowned. Coverage unit:

```yaml
operation: receive
branch: empty-own-mailbox-parks
golden: empty_receive_parks
negative: false
```

## 083-C — Golden (model) vs adapter-negative (RFC 073)

```text
A golden negative scenario proves the Henret MODEL rejects or no-ops a bad
operation. It does not assert anything about how an external runtime reports
adapter errors. Adapter-side negative testing is RFC 073.
```

## 083-D — Coverage source of truth

Maintain coverage in `Henret/Conformance/Coverage.lean` (or generate it from
Lean declarations via RFC 084) — **not** a hand-maintained
`docs/conformance-coverage.md`, which would drift again. The coverage gate
runs in the RFC 080 suite (stage 6).

## Final-pass amendments (RFCs 080-086 v2 review)

**083-1 — Golden is the default for executable branches.** Every executable
`RuntimeOp` branch must be covered by a **golden scenario** unless explicitly
marked `OUTSCOPE` with a reason. Examples and theorem-index entries may
provide *supplemental* coverage but do **not** satisfy golden conformance
(they may satisfy coverage only for non-executable, proof-only properties).

**083-2 — Stable, namespaced branch IDs.**

```yaml
operation: receiveUntil
branch: timeout-fast-path
scenario: receiveUntil_timeout_fast_path
kind: positive
```

Prose branch names are not relied upon.

**083-3 — Executable final-state predicates.** Scenarios are a Lean value,
not Markdown alone:

```lean
structure GoldenScenario where
  name     : String
  ops      : List RuntimeOp
  expected : List StepResult
  finalCheck : RuntimeState → Bool
  covers   : List BranchId
```

**083-4 — Mesa re-park regression.** Add `mesa_woken_task_can_repark`: a
waiter woken by `send` finds another task consumed first, so it re-receives
and parks again — a key Mesa-semantics design choice, made golden.

**083-5 — Closed-actor / shutdown are branches.** The closed-actor and
shutdown rejection cases are explicit branches in `Coverage.lean`, not
merely scenario names.

## Acceptance criteria

```text
- Every EXECUTABLE RuntimeOp branch is covered by a golden scenario unless
  marked OUTSCOPE with a reason. Examples/theorem-index are supplemental only.
- Each golden scenario is a Lean GoldenScenario value (ops, expected
  StepResult list, executable finalCheck, covered BranchIds) — no
  Markdown-only scenarios.
- Branch IDs are stable and namespaced (083-2).
- Negative/security scenarios above present and passing, incl. the Mesa
  re-park regression; closed-actor and shutdown rejections are Coverage.lean
  branches.
- Coverage source is Lean/generated, not hand-maintained markdown.
- The coverage gate runs as RFC 080 stage 6.
```

## Priority and sequencing

P1. Per the review, conformance coverage (externally visible) lands before
proof ergonomics (082, internal); the coverage gate is an RFC 080 stage.

## References

- v0.17.0 audit review item A3 and its security note; RFCs 080-086 review
  amendments 083-A..E.
- RFC 047 (golden trace conformance suite) — this extends it.
- RFC 073 (runtime adapter negative tests) — adapter-side counterpart.
- Exact results extracted from `Henret/Scheduler/Model.lean` (RFC 040/041/
  049/055 step cases).
