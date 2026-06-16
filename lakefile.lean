import Lake
open Lake DSL

-- Henret — executable actor/task runtime models for Lean 4.
-- License: Apache-2.0.  Author: nabbisen.
-- Repository: <REPO-URL-PLACEHOLDER>
-- Keywords: lean4, formal-verification, actor-model, scheduler, semantics,
--           refinement, concurrency, runtime-model.
-- Toolchain: leanprover/lean4:v4.15.0 (see lean-toolchain).
package henret where
  -- Conservative versioning until RFC 052 (see docs/release-policy.md).
  version := v!"0.23.0"

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

/-- Optional bounded model explorer (RFC 048).
    Build:  lake build HenretExplore
    A development/testing tool — outside the default `import Henret` path.
    See docs/model-explorer.md. -/
lean_lib HenretExplore where
  globs := #[.submodules `Henret.Explore]

lean_exe «henret-explore» where
  root := `Explore

/-- Documentation-metadata descriptors (RFC 084 / RFC 075).
    Build:  lake build HenretMeta
    The checked source of truth for the generated model tables; import-cheap
    (no model/proof dependency). See `scripts/extract_model_docs.py`. -/
lean_lib HenretMeta where
  globs := #[.submodules `Henret.Meta]
