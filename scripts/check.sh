#!/usr/bin/env bash
# Henret release gate (RFC 017, extended through RFC 080).
#
# Modes (RFC 080-A, split by RFC 097):
#   check.sh --fast               local/constrained developer mode (default).
#                                 Core gates only; emits NO manifest.
#   check.sh --release-core       CI-authoritative, sidecar-publishing profile.
#                                 Core gates (build/proofs/audit/docs/package) +
#                                 hashed manifest. Blocks sidecar publication.
#                                 (`--release` is an alias for this.)
#   check.sh --release-validation advisory executable validation: demo +
#                                 exhaustive conformance, run interpreted, emitted
#                                 as a separate validation report. NON-blocking.
#
# RFC 097: the demo and exhaustive conformance executables cannot complete on the
# standard GitHub runner, so they are advisory validation, not release-blocking.
# Authoritative release evidence still comes from CI running --release-core on the
# exact release commit/tag (RFC 080-D); a local run is a pre-check only.
set -euo pipefail
cd "$(dirname "$0")/.."

MODE="${1:---fast}"
case "$MODE" in
  --fast|--release|--release-core|--release-validation) ;;
  *) echo "usage: check.sh [--fast|--release-core|--release-validation]"; exit 2 ;;
esac
[ "$MODE" = "--release" ] && MODE="--release-core"   # backward-compat alias
case "$MODE" in
  --fast)               CORE=1; VALID=0; PACKAGE=0 ;;
  --release-core)       CORE=1; VALID=0; PACKAGE=1 ;;
  --release-validation) CORE=0; VALID=1; PACKAGE=0 ;;
esac

RECORDS="$(mktemp /tmp/henret-records-XXXX.jsonl)"
LOGDIR="$(mktemp -d /tmp/henret-gatelogs-XXXX)"
: > "$RECORDS"
cleanup() { rm -rf "$LOGDIR" "$RECORDS"; }
trap cleanup EXIT

# run_gate <id> <name> <gate-fn> : run a gate, capture/time/hash its output,
# append a manifest record, fail-fast on error. (The declaration form
# `run_gate <id> "<name>"` is what check_selftest.py parses.)
run_gate() {
  local id="$1" name="$2"; shift 2
  local outf="$LOGDIR/gate-$id.out" errf="$LOGDIR/gate-$id.err"
  local start end ms rc status advisory=0 tmo=0
  # RFC 097: gates 2 (demo) and 4 (exhaustive conformance) are advisory. In
  # --release-validation they run time-bounded and NON-fatally: a timeout is
  # recorded (status "timeout"), so a slow/hanging interpreted run never reddens
  # the non-blocking validation job. A real scenario FAILURE is surfaced after
  # all validation gates run (so conformance still runs even if demo fails).
  if [ "$VALID" = 1 ]; then
    case "$id" in
      2) advisory=1; tmo="${HENRET_DEMO_TIMEOUT:-300}" ;;
      4) advisory=1; tmo="${HENRET_CONF_TIMEOUT:-1500}" ;;
    esac
  fi
  echo "== gate $id ($MODE): $name =="
  start=$(date +%s%3N)
  set +e
  if [ "$advisory" = 1 ]; then
    # `timeout` execs a command, not a shell function; re-enter bash with the
    # gate function's definition so it can be wrapped. Gate bodies are nullary.
    timeout -k 10 "${tmo}s" bash -c "$(declare -f "$1"); $1" >"$outf" 2>"$errf"
  else
    "$@" >"$outf" 2>"$errf"
  fi
  rc=$?
  set -e
  end=$(date +%s%3N); ms=$((end - start))
  if [ "$rc" -eq 0 ]; then status=pass
  elif [ "$advisory" = 1 ] && { [ "$rc" -eq 124 ] || [ "$rc" -eq 137 ]; }; then status=timeout
  else status=fail; fi
  sed 's/^/    /' "$outf"
  [ -s "$errf" ] && sed 's/^/    [stderr] /' "$errf" || true
  local osha esha
  osha=$(sha256sum "$outf" | cut -c1-64)
  esha=$(sha256sum "$errf" | cut -c1-64)
  python3 -c 'import json,sys
print(json.dumps({"id":int(sys.argv[1]),"name":sys.argv[2],"command":sys.argv[3],
"status":sys.argv[4],"duration_ms":int(sys.argv[5]),
"stdout_log":sys.argv[6],"stdout_sha256":sys.argv[7],
"stderr_log":sys.argv[8],"stderr_sha256":sys.argv[9]}))' \
    "$id" "$name" "$name" "$status" "$ms" \
    "release/logs/gate-$id.out" "$osha" "release/logs/gate-$id.err" "$esha" >> "$RECORDS"
  echo "   -> $status (${ms}ms)"
  # Required gates abort on fail. Advisory gates never abort inline (timeout is
  # non-fatal; a real fail is surfaced after the validation run).
  if [ "$status" = fail ] && [ "$advisory" = 0 ]; then echo "FAIL: gate $id ($name)"; exit 1; fi
}

# ---------------------------------------------------------------- gate bodies
gate_selftest() { python3 scripts/check_selftest.py; }

gate_build_libs() { lake build Henret HenretNative HenretExplore HenretMeta HenretExamples; }

gate_demo() {
  # Run the demo INTERPRETED off the gate-1 oleans (henret-demo's import closure,
  # incl. HenretExamples). Natively compiling the executable means C codegen for
  # the whole project (~80 modules) + link, which alone takes the better part of
  # an hour on a stock CI runner. Interpreting runs and asserts every scenario in
  # seconds; the demo binary is not a shipped artifact.
  lake env lean --run Main.lean
}

gate_examples() {
  for f in examples/[0-9][0-9]_*.lean; do
    echo "  - $f"
    lake env lean "$f" > /dev/null || return 1
  done
}

gate_conformance() {
  # RFC 047 golden trace suite + RFC 083 branch-coverage suite and registry
  # completeness. Run INTERPRETED off the gate-1 oleans (Conformance imports only
  # Henret.Conformance, already built) to avoid native exe compilation. The run
  # exits non-zero if any trace/branch scenario fails or coverage is incomplete;
  # branch_suite_passes and coverage_complete are also kernel-checked at build
  # (gate 1) and axiom-audited (gate 6).
  lake env lean --run Conformance.lean
}

gate_doc_symbol() {
  local f; f="$LOGDIR/docsym.lean"
  python3 scripts/doc_symbol_check.py > "$f"
  if ! lake env lean "$f" > /dev/null 2>&1; then
    echo "FAIL: a backticked theorem name in docs does not resolve:"
    lake env lean "$f" 2>&1 | grep "unknown" | head -10
    return 1
  fi
  echo "doc symbols ok"
}

gate_axiom_audit() {
  local A rc; A="$LOGDIR/audit.lean"
  cat > "$A" << 'LEAN'
import Henret
import Henret.Native.DequeModel
import Henret.Native.Assumptions
open Henret Henret.Native Henret.Bridge
#print axioms step_preserves_terminal
#print axioms step_invalid_unchanged
#print axioms run_preserves_wf
#print axioms reachable_wf
#print axioms reachable_spawned_has_owner
#print axioms reachable_owner_has_mailbox
#print axioms step_clock_monotone
#print axioms receive_only_own
#print axioms reachable_runnable_is_queued
#print axioms reachable_queue_exact
#print axioms receive_empty_parks
#print axioms receive_blocked_parks
#print axioms reachable_waiters_exact
#print axioms reachable_waiter_actor_unique
#check @spawnChild_sets_parent
#check @spawnChild_queues_child
#check @step_preserves_parent
#check @reachable_parent_lt
#check @parent_chain_terminates
#print axioms reachable_parent_lt
#print axioms parent_chain_terminates
#print axioms qRun_tracks
#print axioms driveStackB_complete
#print axioms nativeDequeModel_qRun_tracks
-- RFC 036 bridge theorems (single-worker queue projection)
#print axioms bridge_step_single_worker
#print axioms bridge_run_tracks_single_worker
#print axioms bridge_run_general
#check @bridge_spawn
#check @bridge_spawnChild
#check @bridge_schedule
#check @bridge_cancel
#check @bridge_send
#check @bridge_inject
#check @bridge_tick
-- RFC 038 owner/parent exactness theorems
#print axioms reachable_owner_spawned
#print axioms reachable_parent_child_spawned
#check @spawnChild_child_spawned
#check @WellFormed.owner_spawned
#check @WellFormed.parent_child_spawned
-- RFC 039 cascade cancel theorems
#print axioms preserves_wf_cancelTree
#print axioms cancelTree_cancels_task
#print axioms cancelTree_preserves_task_state
#print axioms bridge_cancelTree
#check @cancelTree_cancels_root
#check @cancelTree_removes_from_readyQ
#check @descendantsOf_nodup
-- RFC 049 supervision restart policies
#print axioms reachable_restart_fresh
#print axioms reachable_restart_old_failed
#print axioms reachable_restart_parent_consistent
#print axioms restart_preserves_parent_acyclicity
#print axioms restarted_task_has_owner
#check @preserves_wf_fail
#check @preserves_wf_restartOne
#check @bridge_fail
#check @bridge_restartOne
-- RFC 054 semantic profile inclusion chain
#print axioms core_le_actor
#print axioms actor_le_full
#print axioms core_le_full
-- RFC 055 structured cancellation / shutdown
#print axioms closeActor_sets_closed
#print axioms closed_actor_rejects_send
#print axioms closed_actor_rejects_inject
#print axioms shutdown_rejects_spawn
#print axioms shutdown_sets_status
#print axioms stopWhenIdle_requires_quiescent
#print axioms stopWhenIdle_sets_stopped
#check @preserves_wf_closeActor
#check @preserves_wf_shutdown
#check @preserves_wf_stopWhenIdle
#check @bridge_closeActor
#check @bridge_shutdown
#check @bridge_stopWhenIdle
#check @closeActor_preserves_mailboxes
-- Coverage for the remaining allowlisted headline theorems
#print axioms reachable_occurrence_unique
#print axioms send_stamps_source
#print axioms inject_stamps_none
#print axioms Bridge.reachable_multi_bridge
#print axioms Bridge.single_bridge_implies_multi_bridge
#print axioms Conformance.conformance_suite_passes
#print axioms Conformance.branch_suite_passes
#print axioms Conformance.coverage_complete
#print axioms reachable_mailbox_within_capacity
#print axioms step_backpressured_unchanged
#print axioms send_full_backpressured
#print axioms inject_full_backpressured
#print axioms send_unbounded_not_backpressured
#print axioms inject_unbounded_not_backpressured
#print axioms Progress.ready_eventually_scheduled_under_bounded_fairness
#print axioms Progress.schedule_schedules_head
#print axioms Progress.head_scheduled_within_one
#print axioms Progress.unfairOps_not_bounded_fair_0
#print axioms Trace.stepTrace_state_eq_step
#print axioms Trace.stepTrace_result_eq_step
#print axioms Trace.runTraceLedger_state_eq_run
#print axioms Trace.event_received_sound
#print axioms Trace.event_parked_sound
#print axioms Trace.event_timerWoke_sound
#print axioms Trace.event_spawnChild_sound

-- RFC 057: resource lifetime & finalization ledger
#print axioms preserves_wf_acquire
#print axioms preserves_wf_release
#print axioms preserves_wf_finalize
#print axioms preserves_wf_acquireActor
#print axioms bridge_acquireActor
#print axioms preserves_wf_releaseActor
#print axioms bridge_releaseActor
#print axioms closeActor_marks_actor_resources_closing
#print axioms markActorResourcesClosing_eq_of_drained
#print axioms step_preserves_actor_exists
#print axioms reachable_resource_fresh
#print axioms reachable_resource_owner_spawned
#print axioms reachable_allocated_owner_nonterminal
#print axioms reachable_closing_owner_terminal
#print axioms nextResourceId_monotone_step
#print axioms nextResourceId_monotone_run
#print axioms complete_marks_owned_resource_closing
#print axioms cancel_marks_owned_resource_closing
#print axioms fail_marks_owned_resource_closing
#print axioms cancelTree_marks_descendant_resource_closing
#print axioms full_has_resourceLifetime
#print axioms full_has_schedulingPolicy
#print axioms acquire_running_allocates
#print axioms acquire_not_running_invalid
#print axioms acquire_non_running_state_invalid
#print axioms release_owner_allocated_ok
#print axioms release_non_owner_invalid
#print axioms release_released_invalid
#print axioms release_closing_invalid
#print axioms finalize_closing_ok
#print axioms finalize_allocated_invalid
#print axioms finalize_released_invalid
#print axioms released_resource_never_live_step
#print axioms released_resource_never_live_run
#print axioms reachable_released_resource_never_live
#print axioms blocked_not_invalid_class
#print axioms backpressured_not_invalid_class
#print axioms timedOut_not_invalid_class
#print axioms invalid_is_fault
#print axioms blocked_not_fault
#print axioms backpressured_not_fault
#print axioms timedOut_not_fault
#print axioms ok_not_fault
#print axioms reorder_preserves_wf
#print axioms policyStep_preserves_wf
#print axioms policy_does_not_create_task
#print axioms fifo_policy_equiv_schedule
#print axioms schedule_preserves_nextId
#print axioms wf_taskMeta_only
#print axioms preserves_wf_setPriority
#print axioms preserves_wf_setDeadline
#print axioms setPriority_meta_of_spawned
#print axioms setDeadline_meta_of_spawned
#print axioms pickBy_mem
#print axioms foldl_best_mem
#print axioms foldl_best_ge
#print axioms priority_policy_selects_max
#print axioms foldl_winner
#print axioms deadlineLt_irrefl
#print axioms deadline_policy_selects_min_deadline
#print axioms closing_finalize_releases
#print axioms resourceDrained_drained
#print axioms stopWhenDrained_stops_drained
#print axioms stopWhenDrained_stops
#print axioms stopWhenDrained_noop
#print axioms preserves_wf_stopWhenDrained
#print axioms bridge_stopWhenDrained
#print axioms step_resources_none_run_none
#print axioms drained_step_drained
#print axioms stopWhenDrained_then_step_drained
#print axioms sleepingHasTimer_init
#print axioms step_preserves_sleepingHasTimer
#print axioms run_preserves_sleepingHasTimer
#print axioms reachable_sleepingHasTimer
#print axioms quiescent_no_sleeping
#print axioms step_preserves_frozen
#print axioms stopWhenDrained_enters_frozen
#print axioms frozen_run_drained
#print axioms reachable_stopWhenDrained_stays_drained
#print axioms reachable_stopWhenDrained_stays_quiescent
#print axioms stopWhenDrained_enters_cleanStopped
#print axioms reachable_stopWhenDrained_enters_cleanStopped
#print axioms cleanStopped_drained
#print axioms cleanStopped_quiescent
#print axioms cleanStopped_stoppedDrained
#print axioms cleanStopped_step_stays_frozen
#print axioms cleanStopped_run_stays_frozen
#print axioms stopWhenIdle_can_stop_undrained
LEAN
  lake env lean "$A" | python3 scripts/axiom_audit.py
  rc=$?
  return $rc
}

gate_doc_consistency() {
  local targets="README.md docs/ examples/ CHANGELOG.md Henret/ Main.lean"
  local filt='\.lake\|docs/reviews/\|rfcs/done/\|docs/handoff-'
  # v0.2.x/v0.3.x era stale phrases (RFC 021)
  if grep -rn "five scenarios\|rfcs/proposed/010\|RFC 010 (proposed)\|remains in proposed\|send_preserves_tasks\|receive_preserves_tasks\|10-operation\|six-field reachability\|nine-field reachability\|\`send a m\`\|\`receive a\`\|five .#eval" \
       $targets 2>/dev/null | grep -v "$filt"; then
    echo "FAIL: stale documentation phrase found (v0.2.x/v0.3.x era)"; return 1
  fi
  # v0.8.0 review stale phrases (RFC 037)
  if grep -rn "six scenarios\|field 15 of 16\|all 16 fields\|carries no source actor\|requires an envelope or occurrence identity\|neither touches task state\|RFC 035.*Connecting" \
       $targets 2>/dev/null | grep -v "$filt"; then
    echo "FAIL: stale v0.8.0 phrase found (RFC 037 gates)"; return 1
  fi
  # Bridge claim rule + grammar-count drift (RFC 052 governance)
  if grep -rn "complete bridge preservation\|all 12 RuntimeOps\|12-operation\|the bridge is complete\|18 RuntimeOps\|18-operation" \
       $targets 2>/dev/null | grep -v "$filt"; then
    echo "FAIL: bridge-claim-rule / stale grammar-count phrase found (RFC 052 gates)"; return 1
  fi
  # Source-of-truth count check (RFC 084 stopgap)
  python3 scripts/doc_count_check.py || return 1
  # Evidence-ledger validation + forbidden-claim gate (RFC 081)
  python3 scripts/forbidden_claim_check.py || return 1
  # Preservation-helper adoption gate (RFC 082)
  python3 scripts/helper_usage_check.py || return 1
  # Generated-doc drift gate (RFC 084 full): regenerate the model tables,
  # theorem index, axiom budget, and RFC index and diff the committed copies.
  python3 scripts/extract_model_docs.py --check || return 1
  python3 scripts/extract_theorem_docs.py --check || return 1
  python3 scripts/extract_rfc_index.py --check || return 1
  # Public-theorem name diff gate (RFC 062 §9.2): the prefix-defined public
  # theorem surface must not silently drift.
  python3 scripts/public_theorem_index.py --check || return 1
  # Proof-dependency-budget diff gate (RFC 069): the per-theorem tier/weight/
  # stability budget must not silently drift (e.g. a constructive->classical move).
  python3 scripts/proof_dependency_budget.py --check || return 1
  # Fault-taxonomy doc<->code sync gate (RFC 064)
  python3 scripts/fault_taxonomy_check.py || return 1
  echo "docs consistency ok"
}

gate_rfc_metadata() { python3 scripts/rfc_metadata_check.py; }

gate_warning_budget() {
  # RFC 086: enforce a zero warning budget over the gate's build scope (086-4).
  # Consume the build/example/demo logs the earlier gates already captured; on a
  # fresh CI build these carry every warning, on a cached local build they carry
  # none (authoritative in CI, RFC 080-D).
  if [ -f scripts/warning_budget.py ]; then
    local log="$LOGDIR/warnings.log"; : > "$log"
    for g in gate-1.out gate-1.err gate-2.out gate-2.err gate-3.out gate-3.err; do
      [ -f "$LOGDIR/$g" ] && cat "$LOGDIR/$g" >> "$log"
    done
    python3 scripts/warning_budget.py "$log" --all-warnings 0 --unused-variables 0
  else
    echo "warning budget: gate wired; detector deferred to RFC 086"
  fi
}

# --------------------------------------------------------------------- stages
# RFC 097 gate criticality:
#   CORE (required, sidecar-blocking): 0,1,3,5,6,7,8,9
#   VALIDATION (advisory, non-blocking): 2 (demo), 4 (exhaustive conformance)
# Each `run_gate <id>` appears exactly once (check_selftest invariant); `if`
# guards select which run per mode (set -e safe).
run_gate 0 "gate-suite self-test"            gate_selftest
run_gate 1 "build libraries"                 gate_build_libs
if [ "$VALID" = 1 ]; then
  run_gate 2 "demo regression scenarios"     gate_demo
else
  echo "== gate 2 SKIPPED (advisory; runs in --release-validation) =="
fi
if [ "$CORE" = 1 ]; then
  run_gate 3 "examples compile + eval"       gate_examples
fi
if [ "$VALID" = 1 ]; then
  run_gate 4 "golden conformance suite"      gate_conformance
else
  echo "== gate 4 SKIPPED (advisory; runs in --release-validation) =="
fi
if [ "$CORE" = 1 ]; then
  run_gate 5 "doc-symbol checker"            gate_doc_symbol
  run_gate 6 "strict axiom audit"            gate_axiom_audit
  run_gate 7 "documentation consistency"     gate_doc_consistency
  run_gate 8 "RFC metadata schema"           gate_rfc_metadata
  run_gate 9 "linter warning budget"         gate_warning_budget
fi

# ------------------------------------------- release-core manifest (080-B / 097)
if [ "$PACKAGE" = 1 ]; then
  echo "== assembling release-core manifest (profile ci-core-v1) =="
  mkdir -p release/logs
  cp "$LOGDIR"/gate-*.out "$LOGDIR"/gate-*.err release/logs/ 2>/dev/null || true
  VERSION=$(grep -oE 'v!"[0-9]+\.[0-9]+\.[0-9]+"' lakefile.lean | grep -oE '[0-9]+\.[0-9]+\.[0-9]+' | head -1)
  # Filename convention (RFC 095): dev artifacts keep the v-prefix; the published
  # GitHub release uses no-v names (HENRET_PUBLISH_NAME=1 in CI).
  if [ -n "${HENRET_PUBLISH_NAME:-}" ]; then
    TARBALL="release/henret-${VERSION}.tar.gz"
  else
    TARBALL="release/henret-v${VERSION}.tar.gz"
  fi
  tar --exclude='./.lake' --exclude='./release' --exclude='./.git' \
      --exclude='__pycache__' --exclude='*.pyc' --exclude='./docs/book' \
      --exclude='./.elan' --exclude='./.cache' --exclude='./elan-init' \
      --exclude='./lean-runtime-workspace/.lake' \
      --sort=name --mtime='2020-01-01 00:00:00' --owner=0 --group=0 --numeric-owner \
      -czf "$TARBALL" --transform 's|^\./||' -C . . 2>/dev/null
  # release_manifest.py renders GATE-RUN.md and binds it by hash (RFC 095 §3.3);
  # HENRET_RELEASE_PROFILE tags gate criticality + advisory placeholders (RFC 097).
  HENRET_RELEASE_PROFILE=ci-core-v1 \
    python3 scripts/release_manifest.py "$RECORDS" "$VERSION" "$TARBALL" \
      release/GATE-RUN.md > release/release-verification.json
  echo "wrote release/release-verification.json + release/GATE-RUN.md"
  if [ "$(python3 -c 'import json;print(json.load(open("release/release-verification.json"))["git_dirty"])')" = "True" ]; then
    echo "FAIL: --release-core on a dirty source tree (080-4); offending paths:"
    python3 -c 'import json;print("\n".join("  "+p for p in json.load(open("release/release-verification.json")).get("git_dirty_paths",[])))'
    git status --porcelain || true
    exit 1
  fi
fi

# --------------------------------------- release-validation report (RFC 097)
if [ "$VALID" = 1 ]; then
  echo "== assembling release-validation report =="
  mkdir -p release/logs
  cp "$LOGDIR"/gate-*.out "$LOGDIR"/gate-*.err release/logs/ 2>/dev/null || true
  VERSION=$(grep -oE 'v!"[0-9]+\.[0-9]+\.[0-9]+"' lakefile.lean | grep -oE '[0-9]+\.[0-9]+\.[0-9]+' | head -1)
  if [ -n "${HENRET_PUBLISH_NAME:-}" ]; then VBASE="henret-${VERSION}"; else VBASE="henret-v${VERSION}"; fi
  python3 scripts/validation_report.py "$RECORDS" "$VERSION" \
      "release/${VBASE}.validation-GATE-RUN.md" > "release/${VBASE}.validation-report.json"
  echo "wrote release/${VBASE}.validation-report.json + .validation-GATE-RUN.md"
  # Non-blocking by design: a timeout on an advisory gate does NOT fail the
  # workflow (bounded interpreted runs). A genuine scenario FAILURE (regression)
  # is surfaced so it is not silently hidden.
  if python3 -c 'import json,sys
recs=[json.loads(l) for l in open(sys.argv[1]) if l.strip()]
sys.exit(1 if any(r.get("id") in (2,4) and r.get("status")=="fail" for r in recs) else 0)' "$RECORDS"; then
    echo "release-validation: advisory gates pass or time-bounded (non-blocking)"
  else
    echo "FAIL: an advisory validation gate reported a real failure (regression)"; exit 1
  fi
fi

echo "== all gates green ($MODE) =="
