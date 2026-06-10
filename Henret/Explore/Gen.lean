import Henret.Scheduler.Model
/-!
  # Henret.Explore.Gen  (RFC 048)

  A bounded operation generator for model exploration.  Enumerates small
  `RuntimeOp` sequences over finite task/actor/message/time domains.

  This module is **outside** the default `import Henret` path — it is a
  development/testing tool, not part of the verified model.  See the
  `HenretExplore` Lake library.
-/
namespace Henret.Explore

open Henret

/-- Finite domains bounding the search space. -/
structure SmallWorld where
  maxTask  : Nat := 2
  maxActor : Nat := 2
  maxMsg   : Nat := 1
  maxTime  : Nat := 2
deriving Repr

/-- A tiny default world: two tasks, two actors, one message body, two
    time points.  Keeps exhaustive search tractable. -/
def SmallWorld.tiny : SmallWorld := {}

/-- All candidate operations in a small world.  A curated subset chosen
    to exercise the interesting semantics (lifecycle, messaging, parking,
    timers, supervision) without exploding the branching factor. -/
def genOps (w : SmallWorld) : List RuntimeOp :=
  let tasks  := List.range w.maxTask
  let actors := List.range w.maxActor
  let msgs   := (List.range w.maxMsg).map (fun i => Message.mk i (i * 100))
  let times  := List.range w.maxTime
  -- lifecycle
  (actors.map RuntimeOp.spawn) ++
  [RuntimeOp.schedule] ++
  (tasks.map RuntimeOp.yield) ++
  (tasks.map RuntimeOp.complete) ++
  (tasks.map RuntimeOp.cancel) ++
  -- spawnChild: task × actor
  (tasks.flatMap (fun t => actors.map (fun a => RuntimeOp.spawnChild t a))) ++
  -- messaging
  (tasks.map RuntimeOp.receive) ++
  (tasks.flatMap (fun t => actors.flatMap (fun a =>
      msgs.map (fun m => RuntimeOp.send t a m)))) ++
  (actors.flatMap (fun a => msgs.map (fun m => RuntimeOp.inject a m))) ++
  -- timers
  (tasks.flatMap (fun t => times.map (fun d => RuntimeOp.sleep t d))) ++
  (times.map RuntimeOp.tick) ++
  (tasks.map RuntimeOp.wake)

/-- All operation sequences of length exactly `d`. -/
def genProgramsExact (w : SmallWorld) : Nat → List (List RuntimeOp)
  | 0     => [[]]
  | d + 1 =>
    let shorter := genProgramsExact w d
    (genOps w).flatMap (fun op => shorter.map (fun prog => op :: prog))

/-- All operation sequences of length up to `d` (inclusive). -/
def genPrograms (w : SmallWorld) (d : Nat) : List (List RuntimeOp) :=
  (List.range (d + 1)).flatMap (genProgramsExact w)

end Henret.Explore
