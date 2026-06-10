import Lake
open Lake DSL

package henret

/-- Lean-only core.  `import Henret` brings in Model + Proofs + Refinement
    (RFC 025; examples are opt-in via `Henret.Examples.Basic`).
    The native-boundary modules (Henret.Native.*) are NOT in the default import tree —
    users opt in with explicit `import Henret.Native.DequeModel`. -/
@[default_target]
lean_lib Henret

@[default_target]
lean_exe «henret-demo» where
  root := `Main

@[default_target]
lean_exe «henret-conformance» where
  root := `Conformance

/-- Optional native-boundary layer (RFC 010).
    Build:  lake build HenretNative
    Import: import Henret.Native.DequeModel (or .Assumptions)
    No C compiler needed — pure Lean axiom-pattern files.
    See docs/native-backend-boundary.md. -/
lean_lib HenretNative where
  globs := #[.submodules `Henret.Native]
