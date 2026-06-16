import Henret
/-!
# Example 15 — Semantic Profiles (RFC 054)

Henret's semantics are grouped into named profiles so a consumer can
declare which subset it depends on. Profiles are metadata: they do not
change any theorem or the behavior of `step`/`run`. The inclusion chain
is kernel-proven.

Run with:  `lake env lean examples/15_semantic_profiles.lean`
-/
open Henret

-- The named profiles and their features.
#eval Profile.core.features    -- [lifecycle]
#eval Profile.actor.features   -- [lifecycle, actorMessaging, parking, occurrenceIdentity]
#eval Profile.full.features    -- [..., timers, supervision, bridge]

-- Profile membership is decidable.
#eval decide (Profile.actor.Has .occurrenceIdentity)  -- true
#eval decide (Profile.core.Has .bridge)               -- false

-- The inclusion chain is kernel-proven (depends only on propext).
example : Profile.core ≤ Profile.actor := core_le_actor
example : Profile.actor ≤ Profile.full := actor_le_full
example : Profile.core ≤ Profile.full := core_le_full

-- Inclusion is a preorder.
example : Profile.full ≤ Profile.full := SemanticProfile.le_refl _
example (h1 : Profile.core ≤ Profile.actor) (h2 : Profile.actor ≤ Profile.full) :
    Profile.core ≤ Profile.full := SemanticProfile.le_trans h1 h2

-- Named profiles have no duplicate features (the `nodup` field).
example : Profile.full.features.Nodup := Profile.full.nodup

#check @core_le_full
