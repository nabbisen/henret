import Lake
open Lake DSL

package henret

/-- Lean-only core.  `import Henret` brings in Core/Actor/Scheduler/Proofs/Refinement/Examples.
    The native-boundary modules (Henret.Native.*) are NOT in the default import tree —
    users opt in with explicit `import Henret.Native.DequeModel`. -/
@[default_target]
lean_lib Henret

@[default_target]
lean_exe «henret-demo» where
  root := `Main

/-- Optional native-boundary layer (RFC 010).
    Build:  lake build HenretNative
    Import: import Henret.Native.DequeModel (or .Assumptions)
    No C compiler needed — pure Lean axiom-pattern files.
    See docs/native-backend-boundary.md. -/
lean_lib HenretNative where
  globs := #[.submodules `Henret.Native]
