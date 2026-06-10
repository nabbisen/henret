import Henret.Explore.Gen
import Henret.Bridge
/-!
  # Henret.Explore.Check  (RFC 048)

  Executable boolean property checkers over bounded domains.

  **These checkers are testing-only.**  `WellFormed` and the occurrence
  invariants quantify over the *infinite* `TaskId`/`ActorId` domains; a
  Bool checker can only inspect a finite range.  So these are *necessary*
  conditions evaluated over the bounded world, not a decision procedure
  for the propositions — they are deliberately **not** connected to a
  soundness theorem (which would be false).  Their role is empirical
  model search: confirm the proven invariants over a sample and catch
  regressions, never to substitute for `reachable_wf` et al.
-/
namespace Henret.Explore

open Henret Henret.Bridge

/-- A property over programs: `true` = holds, `false` = violated. -/
abbrev Property := List RuntimeOp → Bool

/-! ## Bounded well-formedness check

    Checks the easily-decidable structural fields over the bounded world:
    `readyQ` has no duplicates, and the running task is not also queued. -/
def checkWellFormedBool (s : RuntimeState) : Bool :=
  let nodupReady := decide s.readyQ.Nodup
  let runningNotQueued :=
    match s.running with
    | some t => decide (t ∉ s.readyQ)
    | none   => true
  nodupReady && runningNotQueued

/-- The well-formedness property: the reachable state passes the bounded
    structural check. -/
def propWellFormed : Property := fun prog =>
  checkWellFormedBool (run RuntimeState.init prog)

/-! ## Bounded occurrence-uniqueness check

    Collects every envelope occurrence id across mailboxes in the bounded
    actor range and checks the list has no duplicates. -/
def occurrenceIds (w : SmallWorld) (s : RuntimeState) : List MessageId :=
  (List.range w.maxActor).flatMap (fun a =>
    match s.mailboxes a with
    | some mb => mb.messages.map Envelope.occurrence
    | none    => [])

def checkOccUniqueBool (w : SmallWorld) (s : RuntimeState) : Bool :=
  decide (occurrenceIds w s).Nodup

def propOccurrenceUnique (w : SmallWorld) : Property := fun prog =>
  checkOccUniqueBool w (run RuntimeState.init prog)

/-! ## Bridge skeleton consistency

    The meaningful single-worker bridge check, made executable: run the
    `toQOpsTrace` translation and confirm worker 0's queue tracks
    `readyQ`.  Proven always-true by `bridge_run_tracks_single_worker`,
    so the explorer confirms it over the sample. -/
def checkBridgeBool (prog : List RuntimeOp) : Bool :=
  let s := run RuntimeState.init prog
  let wqs := applyQOps WorkerQueues.init (toQOpsTrace RuntimeState.init prog)
  wqs 0 == s.readyQ

def propBridge : Property := checkBridgeBool

/-! ## A deliberately false property (for the shrinker demo)

    "The ready queue is always empty" — obviously false after a single
    `spawn`.  Used to demonstrate counterexample minimization. -/
def propReadyAlwaysEmpty : Property := fun prog =>
  (run RuntimeState.init prog).readyQ.isEmpty

end Henret.Explore
