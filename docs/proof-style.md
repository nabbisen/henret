# Henret proof-style guide

> **Status:** RFC 062 Phase 1 (introduced in v0.30.0). Phases 2–3 are gated on a
> separate architect review; this document records the rules that hold *now* and
> flags what is deferred.

Henret's value is that its safety claims stay **named and auditable**. The
preservation corpus is large and repetitive, and RFC 062 reduces that repetition
— but only within a conservative policy that keeps every obligation inspectable.
The governing rule, from the architect review (RFC 062 §4):

> **Proof ergonomics may remove syntactic repetition, but it must not remove
> semantic accountability. Each preservation obligation must remain named either
> by a theorem, a field-specific lemma, or an explicit operation classification.**

If a change would make it *unclear which field is preserved* or *let a new
operation inherit an old proof path silently*, it is out of bounds regardless of
how many lines it saves.

---

## 1. Preservation proof principles

The model's safety invariant is `WellFormed` (33 fields). For every `RuntimeOp`
we prove a `preserves_wf_<op>` theorem, and the aggregate `reachable_wf` carries
`WellFormed` along any run. Two repeated *shapes* dominate the corpus:

* **Shape B — the 33-field record build.** A `preserves_wf_<op>` proof ends in a
  `refine ⟨?_, …⟩` with one bullet per `WellFormed` field. Most bullets for a
  given op are *pass-through*: the op does not touch the projections the field
  reads, so the field carries over.
* **Shape A — the inert-op enumeration.** A projection/preservation theorem that
  is uniform across many ops still lists each op explicitly (`cases op with …`)
  so that adding a new op forces a conscious decision.

The compression we allow targets Shape B's pass-through bullets (helper lemmas).
Shape A's explicit list is a **feature, not debt** — see §5.

Each `preserves_wf_<op>` keeps the *same statement and name*; only proof bodies
change. Axiom tiers (STD = ⊆ {`propext`, `Quot.sound`}; STD_C = STD ∪
{`Classical.choice`}) must not regress.

---

## 2. Allowed helper-lemma style

Pure lemma extraction is the **primary** sanctioned mechanism. The established
pattern lives in `Henret/Proofs/StepFields.lean` (and `Henret/Proofs/Resource.lean`
for the resource ledger). A *field-specific unchanged lemma* takes the stepped
state `s'` plus the projection equalities it depends on, and discharges exactly
one `WellFormed` field:

```lean
theorem wf_mailbox_capacity_pass {s s' : RuntimeState} (h : WellFormed s)
    (hpol : ∀ a, s'.mailboxPolicy a = s.mailboxPolicy a)
    (hmb  : ∀ a, s'.mailboxes a = s.mailboxes a)
    (a : ActorId) (n : Nat) (mb : Mailbox)
    (hcap : (s'.mailboxPolicy a).capacity = some n)
    (hmbx : s'.mailboxes a = some mb) :
    mb.messages.length ≤ n := …
```

Call site (the three time blocks now share this one helper):

```lean
· intro a' n mbx hcap hmbx
  exact wf_mailbox_capacity_pass h (by simp [step, …]) (by simp [step, …])
    a' n mbx hcap hmbx
```

Naming rules (architect §10):

* The name says **what is unchanged and why** the field survives:
  `wf_mailbox_capacity_pass`, `wf_timed_has_deadline_pass`, `wf_resource_inert`.
* **Banned** because they hide the obligation: `wf_everything_ok`, `solve_wf`,
  `preservation_trivial`.
* A helper closes **one** field (or one tightly-coupled bundle, like the four
  resource fields of `wf_resource_inert`). A helper must never fill a whole
  `WellFormed` record — that would erase per-field visibility.

`HENRET_HELPER_RESERVED` is the only sanctioned way to keep an exported
`wf_*_pass` helper that is not yet used (RFC 082); the helper-usage gate
otherwise requires every exported helper to have a real call site.

---

## 3. Simp-set policy

Named simp-sets are **allowed but governed** — per the architect (§13) they are
the main *hidden* risk, because a set can quietly become a de-facto tactic.

Rules for any named set introduced under RFC 062:

1. Every lemma in the set is listed, with a one-line rationale, in the module
   that populates it (and cross-referenced here).
2. No set unfolds `step` (or any large `def`) globally. Guarded `step` unfolding
   stays a local, explicit `simp [step, <guards>]`.
3. There is no `henret_all` mega-set. Each set has a single narrow domain
   (update lemmas, projection lemmas, resource-ledger lemmas, mailbox lemmas,
   timer lemmas).
4. If a set lemma causes proof-search blow-up — or simply fails to compose — it
   is removed from the set and invoked explicitly at the sites that need it.

### Phase 1 finding: no `henret_upd` set (deferred to Phase 2)

We prototyped the `henret_upd` set the review sketched
(`attribute [simp, henret_upd] upd_self upd_ne`) and **withdrew it**:

* `register_simp_attr` requires importing a `Lean.Meta.*` module. Henret's proof
  tree is otherwise prelude-only; pulling the simp *implementation* into the
  default `import Henret` graph is a real cost we will not pay for an unused set.
* The point-update lemmas **do not compose** under a named set: the conditional
  `upd_ne` (side condition `j ≠ i`) is not discharged by `simp only [henret_upd, h]`
  for variable indices, and the def-unfold form does not simplify cleanly either.
  Point updates are best invoked **explicitly** — `simp only [upd_ne _ _ h]` or
  the existing `simp only [upd, if_neg h]` idiom — which is also *more* auditable
  (the reviewer sees exactly which disequality discharges the case).

This is governance rule 4 applied at design time. Named simp-sets remain
sanctioned; the right place to evaluate them is **Phase 2 on `Messaging.lean` /
`Lifecycle.lean`**, where *unconditional* `upd`/mailbox/timer rewrites are dense
and the payoff is measurable. Any set added then must be built green against the
two largest proof files before landing (architect §13.5).

### Simp-set permission rule (RFC 062 Phase 1 lesson; Phase 2 evidence gate)

> Named simp-sets are permitted only when they demonstrably reduce repetition, do
> not add heavy imports to the default `import Henret` graph, and remain narrow
> enough that their contents are reviewable.

Concretely, a named simp-set may ship in Phase 2 only if **all** of these hold
(architect Phase-2 ruling §8):

1. it fires in real proofs, not just toy examples;
2. it reduces repeated local proof text;
3. it does not cause broad `step` expansion;
4. it does not require `Lean.Meta.*` in the default `import Henret` graph;
5. its complete lemma membership is documented;
6. it is tested against the two largest proof files;
7. removing a lemma from the set has a clear, local failure mode.

If no candidate qualifies, **ship no simp-set** — that is a valid RFC 062
outcome. Explicit lemma invocation is preferred over a marginal set.

---

## 4. Operation-classification rule

Preservation and projection theorems that range over operations classify **each
constructor explicitly**:

```lean
cases op with
| spawn _      => …
| schedule     => …
…
| releaseActor _ _ => …
```

Inert arms use the uniform discharge `simp only [step]; (repeat' split) <;> …`,
but they are still listed one constructor at a time (or via a `.shutdown | .stop…`
enumeration that names every constructor). The explicit list is what makes a new
op *fail to compile* until it is consciously handled everywhere.

If duplication of the *same* op list across several theorems becomes painful, the
sanctioned consolidation (Phase 2, review-gated) is an explicit classification
**function** with no catch-all, e.g.

```lean
def parentEffect : RuntimeOp → ParentEffect
  | .spawnChild _ _  => .changesBySpawnChild
  | .restartOne _ _ _ => .changesByRestart
  | …                => .inert   -- every other constructor listed, no `| _`
```

whose totality Lean checks by exhaustiveness. This reuses one named list across
the 3–8 sites that repeat it **without** hiding any constructor.

---

## 5. No catch-all rule

**Never** use `| _ =>` (or `| _ => …`) to classify operations in a
preservation/projection proof. This is non-negotiable.

The explicit enumeration is a **regression gate**: when a `RuntimeOp` is added,
Lean must force every relevant theorem to decide whether the new op is inert for
this invariant, active-but-preserving, invalid-branch-only, structurally
changing, or impossible under the hypotheses. A catch-all lets a new op silently
inherit an old proof path — unacceptable in a formal execution-management model.

The per-op cascade (adding one op currently touches ~13 proof files) is therefore
a *cost we keep on purpose* for the classification theorems. RFC 062 reduces the
cost of the *record-build* repetition (§2), not the classification cost.

---

## 6. Macro policy

**No macros and no tactic-like automation in Phase 1 or Phase 2.** Adding
metaprogramming during a corpus-wide style change would make it impossible to
tell good abstraction from hidden proof fragility. Phases 1–2 use only ordinary
Lean lemmas, ordinary namespaces, governed simp-sets, and (if ever) transparent
local notation.

A single small macro may be *proposed* in a future Phase 3 review, and only if it
(architect §5): replaces a precisely documented recurring shape; expands to
ordinary, readable proof text; is piloted in one proof family; is documented
here; does **not** classify operations; does **not** build a whole `WellFormed`
record; and could be removed without changing any theorem statement or axiom
tier. A goal-local helper like `close_unchanged_field` could qualify.

Permanently rejected for v1-bound Henret: a global `preserve_wf` tactic, a
`classify_inert_ops` macro, or anything that fills a `WellFormed` record or
classifies ops implicitly. These erase the safety ledger.

---

## 7. Public theorem stability

The **public theorem surface** is the set of names other proofs, docs, and the
trust matrix depend on. It is defined mechanically (see
`scripts/public_theorem_index.py`) as:

* every `theorem` in `Henret/` whose name begins with one of the stable public
  prefixes — `preserves_wf_`, `step_preserves_`, `reachable_`, `bridge_`,
  `run_preserves_` — and
* every key in the strict axiom-audit allowlist (`scripts/axiom_audit.py`).

The committed snapshot is `docs/generated/public-theorems.md`; the diff gate
(`public_theorem_index.py --check`, wired into `check.sh` gate 7) regenerates it
from source and fails if it drifts. A public theorem name therefore cannot
**disappear or be renamed** without a conscious update to the snapshot — that
update *is* the migration record. See `docs/proof-api-stability.md` for the
public / internal / generated / deprecated tiers and the migration procedure.

Internal helper names (e.g. `wf_*_pass`, local `have`s) may change freely; they
are not in the snapshot.

When a helper makes a public theorem redundant, do **not** delete the public
name — keep the theorem (it can delegate to the helper), or record an intentional
removal in `docs/proof-api-stability.md`.

---

## 8. How to add a `RuntimeOp`

Adding a constructor is the project's main cascade. The current touch-list (one
op ≈ 13 proof files + ~5 support files); each is a *conscious* classification:

* **Model/grammar:** `Scheduler/Op.lean` (the constructor), `Scheduler/Model.lean`
  (`step` case), `Bridge/Grammar.lean` (`toQOps`), `Trace/Run.lean` (`traceEvents`).
* **Classification theorems (Shape A — explicit arm each):**
  `Proofs/StepProjections.lean`, `Parenthood.lean`, `Restart.lean`,
  `Timers.lean`, `Ownership.lean`, `SleepingTimer.lean`,
  `ResourceReachable.lean`, `Frozen.lean`, `InvariantsPreservation.lean`
  (dispatcher), `Bridge/Preservation.lean` (`bridge_<op>` + dispatcher).
* **Preservation (Shape B):** the relevant `Preservation/*.lean` proof, building
  the 33-field record (reuse §2 helpers for pass-through fields).
* **Docs/gates:** `Meta/Docs.lean` (`runtimeOpDocs` + the `N-operation` count
  docstring), `Conformance/{Branch,Coverage}.lean` (≥1 scenario), the audit
  allowlist + `check.sh` heredoc for any new headline theorem, and the generated
  doc snapshots (`extract_model_docs.py`, `extract_theorem_docs.py`,
  `public_theorem_index.py`).

Do **not** shortcut the Shape-A arms with a catch-all (§5).

---

## 9. How to add a `WellFormed` field

Add a field **only when the property must hold across *all* operations** as a
genuine invariant. Optional or mutable metadata (e.g. `taskMeta`) is deliberately
*excluded* so that metadata ops preserve the record trivially and do not touch
every preservation file.

When a needed property holds only on reachable states but is awkward as a 34th
field, prefer a **standalone reachable invariant** (the RFC 057 / 089 / 090
pattern: a `def` predicate plus `step_preserves_…` / `reachable_…` theorems) over
growing the record. This keeps the cascade off the existing preservation proofs.

If you do add a field: extend `WellFormed` in `Proofs/Invariants.lean`, add a
`refine`-bullet in every `preserves_wf_<op>` (reuse or add a field-specific helper
per §2), update `Meta/Docs.lean` (`wellFormedFieldDocs` + field count), and
re-run the generated-doc gates.

---

## 10. Measurement

RFC 062 is **not** measured by raw LOC. The metric that matters (architect §14):

> How many proof files must be consciously touched when a new `RuntimeOp` is
> added, and are those touches meaningful?

Pass-through record bullets that a helper now discharges are *not* meaningful
touches and should shrink. Shape-A classification arms *are* meaningful and stay.
Secondary signals: public-theorem statements changed (target 0), helper lemmas
introduced, simp-set lemmas added (each governed by §3), proof lines removed.

**Method.** Add a dummy inert `RuntimeOp`, count the proof files that must change
to keep the build green, and classify each remaining touch as *meaningful* (a
genuine op-specific decision) or *mechanical* (a pass-through obligation a helper
should absorb). Record observations — not a permanent target number — in
`docs/proof-ergonomics-metrics.md`. This file defines the method; that file
carries the dated readings. The metric is **not** a CI gate (architect §7): it
informs design, it does not become a brittle performance bar.

A Shape-B refactor (intra-proof field bullets) typically leaves the file *count*
unchanged — the enumeration cascade is Shape A — while shrinking the per-op proof
*within* the file a new op already touches. Both effects are real; do not read an
unchanged file count as "no improvement."

---

## Appendix — RFC 062 phase status

* **Phase 1 (v0.30.0):** proof-style guide; public-theorem diff
  gate; `Time.lean` pilot — extracted `wf_mailbox_capacity_pass` (the three time
  blocks now share one field-specific helper for `mailbox_within_capacity`),
  same theorem statements/names, axioms unchanged, no simp-set added (§3
  finding).
* **Phase 2A (v0.31.0):** `Messaging.lean` only. Extracted the occurrence-identity
  fields under enqueue (`occ_fresh`/`occ_nodup`/`occ_disjoint`) into three
  `private` `*_under_enqueue` helpers shared by all five `send`/`inject` enqueue
  sites (the proof is occurrence-only, so source-agnostic). Capacity and
  waiter/timer reasoning left explicit (real per-op reasoning, architect §10). No
  public statement/name change; axioms unchanged; no simp-set, no macro, no
  Shape-A migration. Measurement recorded in `docs/proof-ergonomics-metrics.md`.
* **Phase 2B (review-gated, after 2A review):** `Lifecycle.lean`; optional
  one-projection Shape-A classification *pilot* only (architect §6). No catch-all,
  ever.
* **Phase 2C (only if warranted):** `Resource.lean`, only if a concrete repeated
  proof mass appears.
* **Phase 3 (new review required):** at most one small, goal-local macro, only if
  still justified after Phase 2 measurement.
