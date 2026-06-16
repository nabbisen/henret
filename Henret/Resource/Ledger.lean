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

/-- Who owns a resource (RFC 091). Tier 1 added **task** owners; RFC 091 adds
**actor** owners, whose resources outlive any single task and close only when
the actor itself closes. The sum type keeps one ledger and one drain predicate
rather than a parallel actor-resource ledger. -/
inductive ResourceOwner where
  | task  : TaskId → ResourceOwner
  | actor : ActorId → ResourceOwner
deriving Repr, DecidableEq, Inhabited

/-- One resource's ledger entry: its owner (task or actor) and lifecycle state. -/
structure ResourceRecord where
  owner : ResourceOwner
  state : ResourceState
deriving Repr, DecidableEq, Inhabited

/-- Mark every `allocated` resource whose **owner** satisfies `p` as `closing`,
leaving `closing`/`released` resources and resources owned by others unchanged.
The single owner-generic primitive behind every terminal-transition coupling
(RFC 057 review §19, generalized in RFC 091). -/
def markClosingIfOwner (p : ResourceOwner → Bool)
    (resources : ResourceId → Option ResourceRecord) :
    ResourceId → Option ResourceRecord :=
  fun r =>
    match resources r with
    | some ⟨o, .allocated⟩ => if p o then some ⟨o, .closing⟩ else some ⟨o, .allocated⟩
    | other                => other

/-- Task-owner specialization: a terminating task closes its **task-owned**
`allocated` resources and never touches actor-owned ones. This is exactly the
RFC 057 behavior (`cancel`/`fail`/`complete`/`cancelTree` reduce to it). -/
def markClosingIf (p : TaskId → Bool)
    (resources : ResourceId → Option ResourceRecord) :
    ResourceId → Option ResourceRecord :=
  markClosingIfOwner (fun o => match o with | .task t => p t | .actor _ => false) resources

/-- Actor-owner specialization (RFC 091): `closeActor a` closes actor `a`'s
**actor-owned** `allocated` resources, leaving task-owned ones untouched. -/
def markActorResourcesClosing (a : ActorId)
    (resources : ResourceId → Option ResourceRecord) :
    ResourceId → Option ResourceRecord :=
  markClosingIfOwner (fun o => o == .actor a) resources

@[simp] theorem markClosingIfOwner_none (p : ResourceOwner → Bool)
    (res : ResourceId → Option ResourceRecord) (r : ResourceId)
    (h : res r = none) : markClosingIfOwner p res r = none := by
  simp [markClosingIfOwner, h]

@[simp] theorem markClosingIf_none (p : TaskId → Bool)
    (res : ResourceId → Option ResourceRecord) (r : ResourceId)
    (h : res r = none) : markClosingIf p res r = none := by
  simp [markClosingIf, h]

@[simp] theorem markActorResourcesClosing_none (a : ActorId)
    (res : ResourceId → Option ResourceRecord) (r : ResourceId)
    (h : res r = none) : markActorResourcesClosing a res r = none := by
  simp [markActorResourcesClosing, h]

end Henret
