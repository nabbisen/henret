# Migration: vA.B → vC.D — <one-line summary>

**Grammar change.** <Which of `RuntimeOp` / `RuntimeState` / `StepResult`
/ `TaskState` changed, and whether the change is additive or breaking.>

## What changed

<Plain-language description of the change and the RFC that introduced it.>

## Impact on downstream code

<Who needs to act. For additive grammar changes, the break is usually
limited to exhaustive `match` / `cases` over the changed type, which the
compiler flags. For breaking changes, list every affected signature.>

## What to update

### Exhaustive matches

If you `match`/`cases` exhaustively over the changed type, add the new
arm(s):

```lean
-- before
match op with
| ...existing arms...

-- after
match op with
| ...existing arms...
| .<newConstructor> ... => ...
```

### Field access

<If a `RuntimeState` field was added/changed, note any constructors or
record-update sites that need the new field.>

### Theorem renames

<If any theorem was renamed, give the old → new mapping.>

## What did not change

<Reassure on what is stable: existing operations' behavior, the axiom
budget, the proof/trust/test classifications, etc.>
