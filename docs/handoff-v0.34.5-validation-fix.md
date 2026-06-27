# Handoff — v0.34.5: demo compile-blowup root-caused and fixed

**For:** maintainer / architect
**Scope:** `Main.lean` (demo) + `run_gate` advisory wrapper. No model/proof/theorem
change. v0.34.4 stays the published, frozen consumer release.

## You asked to root-cause, not paper over. Done.

I obtained a working **Lean 4.15.0 toolchain inside the sandbox** by downloading it
from GitHub releases (`github.com/leanprover/lean4/releases/.../lean-4.15.0-linux.tar.zst`)
— `release-assets.githubusercontent.com` is reachable, unlike the normally-used
`releases.lean-lang.org`. So I could build the library and reproduce the hang
directly, then bisect it.

### Root cause (measured, not guessed)

- `lake env lean --run Main.lean` hung with **zero output** -> the stall is before
  `main` runs. The profiler pinned it: **"compilation of main took 33 s"** for *one*
  scenario; the full `main` is 44 min. It is the **code generator**, not elaboration
  or runtime.
- Bisection isolated it to scenarios with `let (a, b) := step ...` **tuple-pattern
  binds** in the `do` block. Each such bind makes the Lean compiler duplicate the
  `do`-continuation across the match arm, so compile cost is **exponential in the
  number of destructurings** (one scenario's 5 binds = 33 s; the eight across `main`
  = 44 min).
- Proof: the *same* scenario rewritten with `.1`/`.2` projections compiled in
  **102 ms** vs 33 s — a ~320x difference.

### Fix

Rewrote the 8 `let (a, b) := ...` binds in `Main.lean` as `.1`/`.2` projections (which
don't split the continuation). Verified end-to-end against Lean 4.15.0:

- `main` compiles in **470 ms** (was 44 min); demo runs, **all 41 assertions pass**.
- Conformance has no such pattern (runs interpreted in ~0.5 s, **77 scenarios pass**).
- **`check.sh --release-validation` now exits 0 in ~3 s** with both advisory gates
  *passing* (real validation, not timeouts). `check.sh --fast` stays green.

### Retained safety net

The advisory gates (2 demo, 4 conformance) still run under a `timeout` (tunable via
`HENRET_DEMO_TIMEOUT`/`HENRET_CONF_TIMEOUT`); a timeout is recorded `status: timeout`
and is non-fatal, while a real regression still reddens the workflow. This now guards
against a *future* slowdown instead of masking the demo hang. (Also fixed a bug in my
earlier wrapper: `timeout` can't exec a bash function, so advisory gates are now
re-entered via `declare -f`.)

## Notable consequence

Demo and conformance are now cheap interpreted (off the gate-1 oleans). The original
reason for the two-tier split — those executables being too expensive — no longer
holds. Promoting them into release-core as required gates (architect section 8), or
even collapsing the split, is now viable. Left as a follow-up decision; v0.34.5 keeps
the split and simply makes validation pass.

## Lasting capability

The sandbox can now run Lean (toolchain from GitHub). Future Lean changes can be
built and verified here, not just statically reasoned about.

## Version

v0.34.5 (lakefile bumped). v0.34.4 remains the frozen, consumer-pinned release; this
fix touches only the demo + validation workflow, so consumers are unaffected.
