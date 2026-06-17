# Theorem Naming Style

These conventions make theorems discoverable from `docs/proof-index.md`
and predictable to a reader scanning a proof file. They document the
patterns the corpus already follows; new theorems should match.

## Reachability vs step-local

The corpus distinguishes facts about a *single* `step` from facts about
*every reachable* state (`run init ops`):

- `step_*` — a property of one transition, usually given a precondition.
  Examples: `step_preserves_wf`, `step_preserves_terminal`,
  `step_clock_monotone`, `step_invalid_unchanged`.
- `reachable_*` — the same property promoted to every reachable state,
  with no precondition beyond reachability. Examples: `reachable_wf`,
  `reachable_occurrence_unique`, `reachable_parent_lt`,
  `reachable_restart_fresh`.

A `reachable_X` theorem is typically the headline; the `step_X` /
`preserves_X` lemmas are its machinery.

## Preservation lemmas

`preserves_wf_<op>` proves that operation `<op>` preserves the
`WellFormed` invariant — e.g. `preserves_wf_cancel`,
`preserves_wf_spawnChild`, `preserves_wf_fail`, `preserves_wf_restartOne`.
These are dispatched by `step_preserves_wf`.

## Operation-effect lemmas

`<op>_<effect>` names a specific effect of an operation:
`spawn_has_owner`, `send_appends`, `receive_only_own`,
`wake_exact`, `spawnChild_sets_parent`, `cancelTree_cancels_root`.

## Invariant fields

`WellFormed` fields are lowercase-with-underscores noun phrases naming the
property: `readyQ_nodup`, `running_runs`, `waiters_owned`, `parent_lt`,
`occ_fresh`, `owner_spawned`. The separate `RestartWellFormed` fields
follow the same shape with a `restart_` prefix: `restart_fresh`,
`restart_old_failed`, `restart_parent_consistent`.

## Bridge theorems

`bridge_<op>` proves the single-worker bridge preserves `BridgeState`
across `<op>`: `bridge_spawn`, `bridge_schedule`, `bridge_cancel`,
`bridge_fail`, `bridge_restartOne`. The headline is
`bridge_step_single_worker` / `bridge_run_tracks_single_worker`.

## Renderers and tooling

Renderers (RFC 050) and other non-proof helpers use plain descriptive
names without the `step_`/`reachable_` prefixes, since they are not
theorems: `RuntimeState.render`, `TraceEvent.render`, `traceTable`,
`locationMap`, `parentTreeMermaid`.

## Discoverability rules

- A new headline theorem is added to `docs/proof-index.md` with its file
  location and to the `scripts/axiom_audit.py` allowlist.
- Prefer the `reachable_`/`step_`/`preserves_wf_` prefix that matches the
  theorem's scope; do not invent a new prefix when an existing one fits.
- Keep the suffix a readable noun phrase describing the guarantee, not an
  abbreviation.
