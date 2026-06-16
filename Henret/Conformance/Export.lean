import Henret.Conformance.Golden
/-!
  # Henret.Conformance.Export  (RFC 047)

  Human-readable rendering of trace events and golden scenarios.  A
  JSON serialization can be added here later if an external adapter needs
  it; the first version renders to readable text for review and for the
  executable checker's output.
-/
namespace Henret.Conformance

open Henret Henret.Trace

/-- Render a single event compactly. -/
def renderEvent : TraceEvent → String
  | .invalid op           => s!"invalid({repr op})"
  | .spawned t a          => s!"spawned(task={t}, actor={a})"
  | .spawnChild p c a      => s!"spawnChild(parent={p}, child={c}, actor={a})"
  | .scheduled t          => s!"scheduled(task={t})"
  | .yielded t            => s!"yielded(task={t})"
  | .completed t          => s!"completed(task={t})"
  | .cancelled t          => s!"cancelled(task={t})"
  | .slept t d            => s!"slept(task={t}, deadline={d})"
  | .timerWoke now t      => s!"timerWoke(now={now}, task={t})"
  | .directWoke t         => s!"directWoke(task={t})"
  | .sent s tgt occ       => s!"sent(sender={s}, target={tgt}, occ={occ})"
  | .injected tgt occ     => s!"injected(target={tgt}, occ={occ})"
  | .received t a occ     => s!"received(task={t}, actor={a}, occ={occ})"
  | .parked t a           => s!"parked(task={t}, actor={a})"
  | .waiterWoke a t       => s!"waiterWoke(actor={a}, task={t})"
  | .failed t             => s!"failed(task={t})"
  | .restarted p o n a    => s!"restarted(parent={p}, old={o}, new={n}, actor={a})"
  | .actorClosed a        => s!"actorClosed(actor={a})"
  | .shutdownBegun        => s!"shutdownBegun"
  | .stoppedWhenIdle      => s!"stoppedWhenIdle"
  | .noEffect op r        => s!"noEffect({repr op}, {repr r})"

/-- Render an event trace as a numbered list. -/
def renderTrace (evs : List TraceEvent) : String :=
  String.intercalate "\n"
    (evs.enum.map (fun (i, e) => s!"  [{i}] {renderEvent e}"))

/-- Render a scenario: its purpose and golden trace. -/
def renderScenario (sc : GoldenScenario) : String :=
  s!"{sc.name}: {sc.description}\n{renderTrace sc.expected}"

/-- Render the whole golden suite. -/
def renderSuite : String :=
  String.intercalate "\n\n" (goldenScenarios.map renderScenario)

end Henret.Conformance
