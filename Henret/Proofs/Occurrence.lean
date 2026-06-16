import Henret.Proofs.InvariantsPreservation
import Henret.Proofs.Messaging

namespace Henret

/-! ## Occurrence identity theorems (RFC 033) -/

/-- Local helper: if a mapped list is Nodup, the mapping function is
injective on the list. Used to derive envelope equality from id equality. -/
private theorem nodup_map_inj {α β} {f : α → β} {l : List α}
    (hnd : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (heq : f x = f y) : x = y := by
  induction l with
  | nil => cases hx
  | cons a rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hna, hnd_rest⟩ := hnd
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx_rest <;> rcases hy with rfl | hy_rest
    · rfl
    · exact absurd (heq ▸ List.mem_map_of_mem f hy_rest) hna
    · exact absurd (heq ▸ List.mem_map_of_mem f hx_rest) hna
    · exact ih hnd_rest hx_rest hy_rest

/-- **Global occurrence uniqueness** (RFC 033 headline): in every
reachable state, if two envelopes in any (possibly equal) mailboxes
share an occurrence id, they are the same envelope in the same mailbox.

More precisely: occurrence ids are globally unique — each id identifies
exactly one delivery event across the entire system. -/
theorem reachable_occurrence_unique (ops : List RuntimeOp)
    {a b : ActorId} {mba mbb : Mailbox}
    (hmba : (run RuntimeState.init ops).mailboxes a = some mba)
    (hmbb : (run RuntimeState.init ops).mailboxes b = some mbb)
    {ea eb : Envelope}
    (hea : ea ∈ mba.messages)
    (heb : eb ∈ mbb.messages)
    (hocc : ea.occurrence = eb.occurrence) :
    a = b ∧ ea = eb := by
  have hwf := reachable_wf ops
  by_cases hab : a = b
  · subst hab
    have hmb : mba = mbb := Option.some.inj (hmba.symm.trans hmbb)
    subst hmb
    exact ⟨rfl, nodup_map_inj (hwf.occ_nodup a mba hmba) hea heb hocc⟩
  · exact absurd hocc (hwf.occ_disjoint a b mba mbb hab hmba hmbb ea hea eb heb)

/-- **Send stamps the sender's actor** (RFC 033): the envelope appended
by `send t b m` in a state where task `t` is running and owned by actor
`o` carries `source = some o`.  The source field is the delivery provenance
record — it identifies which actor's task issued the send. -/
theorem send_stamps_source {s : RuntimeState} {t : TaskId} {b o : ActorId} {mb : Mailbox}
    (hrt : s.running = some t) (hts : s.taskState t = some .running)
    (how : s.taskOwner t = some o) (hmb : s.mailboxes b = some mb)
    (hac : s.actorStatus b ≠ .closed)
    (hfull : s.mailboxFull b mb = false)
    (m : Message) :
    let env : Envelope := ⟨s.nextMsgId, s.taskOwner t, m⟩
    ((step s (.send t b m)).1).mailboxes b = some ⟨mb.messages ++ [env]⟩ ∧
    env.source = some o := by
  exact ⟨send_appends hrt hts how hmb hac hfull m, by simp [how]⟩

/-- **Inject stamps `none` as source** (RFC 033): the envelope appended
by `inject a m` carries `source = none`, marking it as an environment
injection rather than a task-to-task message. -/
theorem inject_stamps_none {s : RuntimeState} {a : ActorId} {mb : Mailbox}
    (hmb : s.mailboxes a = some mb) (hrs : s.runtimeStatus = .running)
    (hac : s.actorStatus a ≠ .closed)
    (hfull : s.mailboxFull a mb = false) (m : Message) :
    let env : Envelope := ⟨s.nextMsgId, none, m⟩
    ((step s (.inject a m)).1).mailboxes a = some ⟨mb.messages ++ [env]⟩ ∧
    env.source = none :=
  ⟨inject_appends hmb hrs hac hfull m, rfl⟩

end Henret

/-!
# Henret.Proofs.Occurrence

Occurrence identity theorems (RFC 033).

`send` and `inject` stamp every delivered envelope with a `MessageId`
allocated from `nextMsgId`. Three `WellFormed` fields — `occ_fresh`,
`occ_nodup`, `occ_disjoint` — together guarantee that occurrence ids
are globally unique across all mailboxes in every reachable state.

Public theorems:

* `reachable_occurrence_unique` — **headline**: equal occurrence ids
  in any two (possibly same) reachable mailboxes imply it is the same
  envelope in the same mailbox. Globally unique delivery identity.

* `send_stamps_source` — the envelope appended by `send t b m` carries
  `source = s.taskOwner t` (the sending actor).

* `inject_stamps_none` — the envelope appended by `inject a m` carries
  `source = none` (environment origin, no sending actor).

Trust level: **kernel-proven** — these are theorems derived from the
abstract model and its WellFormed invariant.  The connection between the
model's `nextMsgId` and any concrete allocator (C runtime, OS, clock)
is a **trusted** boundary documented in `Henret.FFI.Spec`.
-/
