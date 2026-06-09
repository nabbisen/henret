# RFC 042 — Preservation Proof Automation and Maintainability

**Status.** Proposed  
**Target version.** v0.10.x infrastructure track  
**Priority.** Ongoing; implement before RFC 040 if preservation cost rises  
**Track.** Proof engineering  
**Depends on.** Current preservation split from RFC 034  
**Touches.** preservation proof files, helper lemma modules, optional tactics/macros, contributor docs

## Summary

Introduce small, auditable proof-engineering helpers to reduce repetitive `WellFormed` preservation code as the invariant grows beyond 19 fields.

The goal is not clever automation. The goal is to prevent proof drift, reduce copy/paste errors, and keep preservation proofs reviewable.

## Motivation

Henret's preservation files are becoming mechanically repetitive:

- each operation case proves every `WellFormed` field;
- many fields are unchanged by most operations;
- occurrence-related and parent-related bullets are often identical pass-through arguments;
- future RFCs such as cascade cancel and timed receive will add more branches.

Manual repetition is acceptable at small scale but becomes a maintenance risk in a formal-verification project.

## Design principles

1. **Auditability over magic.** Helpers must make proofs shorter without hiding semantic case splits.
2. **Local automation.** Use small tactics or simp sets scoped to Henret proof files.
3. **Field-specific lemmas first.** Prefer reusable lemmas over metaprogramming.
4. **No generated opaque proof blobs.** The resulting proof terms should remain inspectable.

## Work items

### 1. Define operation-family unchanged-field lemmas

For each operation family, create structured lemmas:

```lean
namespace Henret.PreservationUnchanged

theorem send_preserves_taskOwner : ...
theorem send_preserves_taskParent : ...
theorem send_preserves_timers_unless_waiter : ...

theorem tick_preserves_mailboxes_except_timeout : ...
...
end Henret.PreservationUnchanged
```

Do not over-generalize. Use names that encode the semantic reason.

### 2. Define localized simp sets

Create attributes:

```lean
attribute [henret_preservation] upd_self upd_ne
attribute [henret_step_proj] send_taskState receive_taskState inject_taskState
```

If custom attributes are too much, use namespaces and documented `simp` lists.

### 3. Provide a small tactic for unchanged fields

Example shape:

```lean
macro "close_unchanged_wf" : tactic => ...
```

or avoid macro syntax and use theorem combinators.

The tactic may close goals where the target is exactly an old `WellFormed` field after rewriting an operation that does not touch relevant state.

### 4. Factor `WellFormed` constructor proof pattern

Instead of repeatedly writing:

```lean
refine ⟨?_, ?_, ... ?_⟩
```

consider helper theorem schemas:

```lean
theorem mk_wf_after_state_update
  (h_old : WellFormed s)
  ... : WellFormed s'
```

Use this only when the state update pattern is common enough.

### 5. Improve proof comments

Every preservation file should have a short header explaining:

- which operation family it handles;
- which fields are genuinely changed;
- which fields are pass-through;
- which helpers are safe to use.

## Acceptance criteria

- At least one preservation file becomes materially shorter or clearer.
- No theorem statement is weakened.
- Axiom audit remains unchanged.
- Proof scripts remain readable to a Lean developer who does not know the macro internals.
- Contributor docs explain the helper strategy.

## Suggested first target

Start with occurrence-related preservation bullets. They are often unchanged under lifecycle/time operations and have predictable proof shape.

Then target mailboxWaiters pass-through under time operations.

## Risks

### Automation can hide semantic mistakes

Avoid tactics that close arbitrary `WellFormed` fields without checking the operation's actual state effects.

### Simp loops

A localized simp set must be tested carefully. Do not add broad recursive unfold rules globally.

### Review difficulty

If a macro is used, provide before/after examples in `docs/proof-engineering.md`.

## Non-goals

- Replacing all preservation proofs with automation.
- Custom proof search engine.
- Changing model semantics.
- Reducing proof count for its own sake.
