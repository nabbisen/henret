import Henret.Core.Id

/-!
# Henret.Resource.Ledger  (RFC 057)

The pure resource-lifetime ledger. A resource models a runtime cleanup
obligation (a file descriptor, reactor registration, native handle) as a
small state machine, **without** any claim about OS handles or that a native
finalizer actually runs (see `docs/resource-lifetime.md`).

Tier 1 resources are **task-owned**: every resource is created by `acquire t`
and carries a non-optional `owner : TaskId` (RFC 057 review, D1). The state
machine has two paths:

```text
allocated → released                     -- synchronous, by the owner (release)
allocated → closing → released           -- owner gone (cancel/fail/complete);
                                            the environment reclaims via finalize
```
-/

namespace Henret

/-- Identity of a resource. Plain `Nat` like `TaskId`/`ActorId`; a fresh-id
counter (`RuntimeState.nextResourceId`) guarantees uniqueness. -/
abbrev ResourceId := Nat

/-- Ledger state of one resource (RFC 057).

* `allocated` — live; the owning task may use or `release` it.
* `closing`   — the owner can no longer release normally (it became terminal);
                a finalization obligation remains.
* `released`  — terminal ledger state; the id never becomes live again. -/
inductive ResourceState where
  | allocated
  | closing
  | released
deriving Repr, DecidableEq, Inhabited

/-- One resource's ledger entry: its owning task and its lifecycle state. -/
structure ResourceRecord where
  owner : TaskId
  state : ResourceState
deriving Repr, DecidableEq, Inhabited

/-- Mark every `allocated` resource whose owner satisfies `p` as `closing`,
leaving `closing`/`released` resources and resources owned by other tasks
unchanged. This is the single primitive behind the terminal-transition
coupling: `cancel`/`fail`/`complete`/`cancelTree` all reduce to one
`markClosingIf` application, so preservation is proved once around it
(RFC 057 review §19). -/
def markClosingIf (p : TaskId → Bool)
    (resources : ResourceId → Option ResourceRecord) :
    ResourceId → Option ResourceRecord :=
  fun r =>
    match resources r with
    | some ⟨o, .allocated⟩ => if p o then some ⟨o, .closing⟩ else some ⟨o, .allocated⟩
    | other                => other

@[simp] theorem markClosingIf_none (p : TaskId → Bool)
    (res : ResourceId → Option ResourceRecord) (r : ResourceId)
    (h : res r = none) : markClosingIf p res r = none := by
  simp [markClosingIf, h]

end Henret
