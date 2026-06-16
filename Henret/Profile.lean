/-!
  # Henret.Profile  (RFC 054)

  A small **semantic profile** vocabulary so a consumer can say which
  subset of Henret's semantics it depends on, and so a theorem can be
  labelled with the minimum profile it requires.

  Profiles are metadata, not a runtime feature flag and not a different
  `RuntimeState`: they do not change any existing theorem or the behavior
  of `step`/`run`. The named profiles carry kernel-proven facts — no
  duplicate features, and the inclusion chain `core ≤ actor ≤ full` — so
  the vocabulary itself is checked, while the per-theorem mapping lives in
  `docs/profile-index.md`.
-/
namespace Henret

/-- The semantic features Henret can model. `schedulingPolicy` is reserved
    for a future RFC (058) and does not yet appear in any named profile;
    `resourceLifetime` (RFC 057) is part of the `full` profile. -/
inductive SemanticFeature where
  | lifecycle
  | actorMessaging
  | timers
  | parking
  | supervision
  | occurrenceIdentity
  | bridge
  | schedulingPolicy
  | resourceLifetime
  | boundedMailbox
deriving DecidableEq, Repr, Inhabited

/-- A semantic profile: a duplicate-free set of features. -/
structure SemanticProfile where
  /-- The features included in this profile. -/
  features : List SemanticFeature
  /-- Features are listed without duplicates. -/
  nodup    : features.Nodup
deriving Repr

namespace SemanticProfile

/-- Profile inclusion: every feature of `p` is a feature of `q`. -/
def Subset (p q : SemanticProfile) : Prop := p.features ⊆ q.features

instance : LE SemanticProfile := ⟨Subset⟩

instance (p q : SemanticProfile) : Decidable (p ≤ q) :=
  inferInstanceAs (Decidable (p.features ⊆ q.features))

/-- Membership of a feature in a profile. -/
def Has (p : SemanticProfile) (f : SemanticFeature) : Prop := f ∈ p.features

instance (p : SemanticProfile) (f : SemanticFeature) : Decidable (p.Has f) :=
  inferInstanceAs (Decidable (f ∈ p.features))

theorem le_refl (p : SemanticProfile) : p ≤ p := fun _ h => h

theorem le_trans {p q r : SemanticProfile} (hpq : p ≤ q) (hqr : q ≤ r) : p ≤ r :=
  fun _ h => hqr (hpq h)

end SemanticProfile

namespace Profile

/-- **core** — the bare task lifecycle: spawn, schedule, yield, complete,
    cancel. -/
def core : SemanticProfile :=
  ⟨[.lifecycle], by decide⟩

/-- **actor** — core plus actor messaging, parking on empty mailboxes, and
    message occurrence identity. -/
def actor : SemanticProfile :=
  ⟨[.lifecycle, .actorMessaging, .parking, .occurrenceIdentity], by decide⟩

/-- **full** — every currently-implemented feature: the actor profile plus
    timers, supervision (fail/restart), and the bridge. -/
def full : SemanticProfile :=
  ⟨[.lifecycle, .actorMessaging, .timers, .parking, .supervision,
    .occurrenceIdentity, .bridge, .boundedMailbox, .resourceLifetime], by decide⟩

end Profile

/-! ## Profile inclusion chain (kernel-proven) -/

/-- The core profile is included in the actor profile. -/
theorem core_le_actor : Profile.core ≤ Profile.actor := by decide

/-- The actor profile is included in the full profile. -/
theorem actor_le_full : Profile.actor ≤ Profile.full := by decide

/-- The core profile is included in the full profile. -/
theorem core_le_full : Profile.core ≤ Profile.full :=
  SemanticProfile.le_trans core_le_actor actor_le_full

/-- The full profile carries every feature of every named profile. -/
theorem actor_has_occurrence : Profile.actor.Has .occurrenceIdentity := by decide

/-- The full profile includes supervision (fail/restart, RFC 049). -/
theorem full_has_supervision : Profile.full.Has .supervision := by decide

/-- The full profile includes bounded mailboxes / backpressure (RFC 056). -/
theorem full_has_boundedMailbox : Profile.full.Has .boundedMailbox := by decide

/-- The full profile includes resource lifetime / finalization (RFC 057). -/
theorem full_has_resourceLifetime : Profile.full.Has .resourceLifetime := by decide

end Henret
