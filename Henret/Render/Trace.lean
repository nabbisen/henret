import Henret.Trace
/-!
  # Henret.Render.Trace  (RFC 050)

  Human-readable renderers for trace events.  Pure `String` functions —
  no proofs, no axioms, outside the proof-critical path.  A formal model
  is easier to trust and adopt when its behavior is inspectable.
-/
namespace Henret.Trace

/-- Render a single trace event as a compact line. -/
def TraceEvent.render : TraceEvent → String
  | .invalid op           => s!"invalid          {repr op}"
  | .spawned t a          => s!"spawned          task {t} (actor {a})"
  | .spawnChild p c a      => s!"spawnChild       task {p} → child {c} (actor {a})"
  | .scheduled t          => s!"scheduled        task {t}"
  | .yielded t            => s!"yielded          task {t}"
  | .completed t          => s!"completed        task {t}"
  | .cancelled t          => s!"cancelled        task {t}"
  | .slept t d            => s!"slept            task {t} until {d}"
  | .timerWoke now t      => s!"timerWoke        task {t} (now {now})"
  | .directWoke t         => s!"directWoke       task {t}"
  | .sent s tgt occ       => s!"sent             task {s} → actor {tgt} (occ {occ})"
  | .injected tgt occ     => s!"injected         actor {tgt} (occ {occ})"
  | .received t a occ     => s!"received         task {t} ← actor {a} (occ {occ})"
  | .parked t a           => s!"parked           task {t} on actor {a}"
  | .waiterWoke a t       => s!"waiterWoke       task {t} on actor {a}"
  | .failed t             => s!"failed           task {t}"
  | .restarted p o n a    => s!"restarted        task {o} → fresh {n} by {p} (actor {a})"
  | .actorClosed a        => s!"actorClosed      actor {a}"
  | .shutdownBegun        => s!"shutdownBegun"
  | .stoppedWhenIdle      => s!"stoppedWhenIdle"
  | .noEffect op r        => s!"noEffect         {repr op} ⇒ {repr r}"

end Henret.Trace

namespace Henret.Render

open Henret.Trace

/-- Render a full event trace as a numbered table. -/
def traceTable (evs : List TraceEvent) : String :=
  let header := "step | event"
  let rule   := "-----+------------------------------------------------"
  let rows := evs.enum.map (fun (i, e) =>
    let n := toString i
    let pad := String.mk (List.replicate (4 - min 4 n.length) ' ')
    s!"{pad}{n} | {e.render}")
  String.intercalate "\n" (header :: rule :: rows)

end Henret.Render
