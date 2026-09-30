#!/usr/bin/env bash
# tools/ci/run_all.sh [-k] [--from STEP] [--list] [STEP...]
#
# THE CI SEQUENCE, as one entry point.  .github/workflows/lean-ci.yml runs exactly
# these steps, one `tools/ci/run_all.sh <step>` per workflow step, so what CI
# checks and what a developer can reproduce are the same commands:
#
#   toolchain        elan and the Lean that lean-toolchain pins (installed
#                    into $HOME/.elan if absent: no sudo, idempotent), then
#                    the packages lake-manifest.json pins, fetched not built
#   toolchain-check  tools/ci/toolchain_check.sh --with-lake: the lake on PATH
#                    and the fetched packages ARE the pinned ones
#   lint             tools/ci/lint.sh (layering, no sorry/axiom/native_decide,
#                    module drift, pins, roots)
#   check-gen        tools/check_gen.py: every generated file equals its
#                    generator's output.  NON-strict: a check that needs the
#                    riscv objdump is a SKIP (and a ::notice::) without it
#   build-deps       lake build of the Sail model, lean-sail and iris-lean
#                    (what the workflow caches: none of it moves with a proof)
#   build            the proofs, `lake build Xv6 MachCSL`, through
#                    tools/ci/timed_build.sh so the profile has its log
#   audit            tools/ci/audit.sh: axioms / opaques of the top theorems
#                    against tools/audit/baseline.json            (BLOCKING)
#   tcb              tools/ci/tcb.sh: what the STATEMENTS depend on, against
#                    tools/tcb/expected.json                      (BLOCKING)
#   reports          tools/ci/reports.sh: environment facts and proof coverage
#                    (BLOCKING), build profile and dead code (informational)
#   vtest            tools/ci/vtest.sh check-ci: the device-conformance suite
#                    (vtest-lean/) against the checked-in captures; fails iff
#                    a proof of the green set stopped compiling   (BLOCKING)
#   test-tools       make test-tools: the unit tests of the Python tools
#
# and, outside the default sequence (the scheduled workflow runs it):
#
#   dead-imports     tools/ci/dead_imports.sh, informational: never fails on
#                    what it finds
#
# With no STEP every step of the sequence runs, in that order, stopping at the
# first failure as the workflow does (-k: keep going; --from STEP: start
# there).  A table of per-step wall times is printed at the end.
#
# WHAT IT DOES NOT DO (nor does CI): regenerate the Sail model (needs the
# patched `sail`), rebuild the xv6 kernel or re-dump the kernel/user images,
# or run QEMU.  Those outputs are checked in; see the header of
# .github/workflows/lean-ci.yml.
#
# THE JOB SUMMARY.  Each step's markdown goes to $GITHUB_STEP_SUMMARY; outside
# GitHub it is collected in $XV6_CI_OUT/summary.md.  GitHub rejects a step
# summary over 1 MiB WHOLE (the upload fails and nothing is shown), so every
# step writes to a scratch file first and what is appended is cut to
# $XV6_SUMMARY_MAX bytes (default 1000 KiB) with a note saying so.  Today's
# largest is the trusted-base tables, ~85 KB.
#
# ENVIRONMENT
#   XV6_CI_OUT        where reports and logs go            (default .lake/ci)
#   XV6_BUILD_LOG     the timed build log                  (default $XV6_CI_OUT/lake-build.log)
#   ELAN_HOME         where elan lives                     (default $HOME/.elan)
#   XV6_SUMMARY_MAX   cap on one step's summary, in bytes  (default 1024000)
#
# EXIT STATUS: non-zero iff a step failed.  No pipe masks a status: the script
# runs under `pipefail` and every `| tee` below is checked through it.
#
# THIS RUNS LEAN (every step from build-deps to vtest, and dead-imports).
# The Lean steps need a machine sized for a Lean build (README: "Build"); the
# steps toolchain-check (without lake: tools/ci/toolchain_check.sh), lint,
# check-gen and test-tools are Python and shell only and run anywhere.  From
# the repository root:
#   tools/ci/run_all.sh
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.." || exit 1

SEQUENCE=(toolchain toolchain-check lint check-gen build-deps build audit tcb reports vtest test-tools)
EXTRA=(dead-imports)

export XV6_CI_OUT="${XV6_CI_OUT:-.lake/ci}"
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
BUILD_LOG="${XV6_BUILD_LOG:-$XV6_CI_OUT/lake-build.log}"
SUMMARY_MAX="${XV6_SUMMARY_MAX:-1024000}"
# elan's proxies first: `lake` must be the one that honours lean-toolchain.
case ":$PATH:" in *":$ELAN_HOME/bin:"*) ;; *) export PATH="$ELAN_HOME/bin:$PATH" ;; esac

say() { printf '\n==> %s\n' "$*"; }

# ---------------------------------------------------------------- the steps

step_toolchain() {
  local want; want=$(tr -d '[:space:]' < lean-toolchain)
  if [ ! -x "$ELAN_HOME/bin/elan" ]; then
    say "installing elan into $ELAN_HOME"
    local init; init=$(mktemp)
    # --default-toolchain none: the toolchain is whatever lean-toolchain says,
    # installed below.  --no-modify-path: no edit of the runner's dotfiles.
    curl -sSfL --retry 3 https://elan.lean-lang.org/elan-init.sh -o "$init" \
      || curl -sSfL --retry 3 https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$init" \
      || { echo "toolchain: could not download elan-init.sh" >&2; rm -f "$init"; return 1; }
    sh "$init" -y --default-toolchain none --no-modify-path || { rm -f "$init"; return 1; }
    rm -f "$init"
  fi
  if ! elan toolchain list | grep -qF "$want"; then
    say "installing $want"
    elan toolchain install "$want" || return 1
  fi
  lake --version || return 1
  # Later workflow steps get elan's proxies on PATH.
  if [ -n "${GITHUB_PATH:-}" ]; then echo "$ELAN_HOME/bin" >> "$GITHUB_PATH"; fi
  # Fetch (never build, never update) the packages the manifest pins.  A
  # restored cache already has them and this is then a no-op.
  say "fetching the packages of lake-manifest.json"
  local before; before=$(md5sum < lake-manifest.json)
  lake resolve-deps || return 1
  if [ "$before" != "$(md5sum < lake-manifest.json)" ]; then
    echo "toolchain: lake rewrote lake-manifest.json while fetching -- the manifest is stale" >&2
    return 1
  fi
}

step_toolchain_check() { tools/ci/toolchain_check.sh --with-lake; }

step_lint() { tools/ci/lint.sh; }

step_check_gen() {
  mkdir -p "$XV6_CI_OUT"
  local rc=0
  python3 tools/check_gen.py | tee "$XV6_CI_OUT/check-gen.txt" || rc=$?
  # The same checks once more for the summary table (2 s; nothing is cached
  # between the two, so they cannot disagree).
  python3 tools/check_gen.py --format md >> "$GITHUB_STEP_SUMMARY" || true
  if grep -q "no riscv objdump" "$XV6_CI_OUT/check-gen.txt"; then
    echo "::notice::check-gen: no riscv64-linux-gnu-objdump on this machine, so the user-ELF re-dump checks were SKIPPED (the md5 and derived-file checks still ran)."
  fi
  return "$rc"
}

step_build_deps() {
  mkdir -p "$XV6_CI_OUT"
  # The model's library, lean-sail's and iris-lean's, by name: everything the
  # proofs import that is not the proofs.  Batteries and Qq are built as far
  # as Iris imports them.
  lake build LeanRV64D Sail Iris 2>&1 | tee "$XV6_CI_OUT/lake-deps.log"
}

step_build() {
  mkdir -p "$(dirname "$BUILD_LOG")"
  : > "$BUILD_LOG"
  # timed_build.sh writes only to the log; follow it so the job log shows the
  # build as it happens.  lake prints each module's output whole, so lines of
  # two modules never interleave (the `make -O` problem of the Rocq build
  # does not arise), and the status is timed_build.sh's own -- no pipe here.
  # No --clean: a fresh checkout has no proof build to clean, and --clean
  # would also throw away the model build the previous step made (or the
  # cache restored).  Locally, `make timed-build` is the clean variant.
  tools/ci/timed_build.sh "$BUILD_LOG" & local pid=$!
  tail -n +1 -f --pid="$pid" "$BUILD_LOG" | sed -u -E 's/^@[0-9.]+ //' || true
  local rc=0; wait "$pid" || rc=$?
  # Belt and braces, as in Rocq's ci.yml: read the log as well as the status.
  if [ "$rc" -eq 0 ]; then
    if ! tail -1 "$BUILD_LOG" | grep -qE '^@end [0-9.]+ rc=0$'; then
      echo "::error::lake exited 0 but $BUILD_LOG does not end with '@end … rc=0'."; rc=1
    elif grep -qE '^@[0-9.]+ (✖ |error: )' "$BUILD_LOG"; then
      echo "::error::Errors in the build log despite a zero exit status."
      grep -E -B2 -A5 '^@[0-9.]+ (✖ |error: )' "$BUILD_LOG" | head -60; rc=1
    fi
  fi
  if [ "$rc" -ne 0 ]; then
    {
      echo "## Proof build"
      echo
      echo "> :x: \`lake build Xv6 MachCSL\` failed (exit $rc)."
      echo
      echo '```'
      grep -E '^@[0-9.]+ (✖ |error: )' "$BUILD_LOG" | sed -E 's/^@[0-9.]+ //' | head -80
      echo '```'
    } >> "$GITHUB_STEP_SUMMARY"
    echo "::error::The proof build failed (exit $rc); the failing modules are in the step summary."
  fi
  return "$rc"
}

step_audit() { tools/ci/audit.sh; }

step_tcb() { tools/ci/tcb.sh; }

step_reports() {
  # Source-file attribution for the coverage report: best effort, never
  # built, and the numbers do not depend on it (tools/ci/reports.sh).
  if [ ! -d xv6-riscv ]; then
    timeout 60 git clone -q --depth 1 --branch verified https://github.com/mit-pdos/xv6-riscv xv6-riscv \
      || echo "reports: no xv6-riscv checkout (no network?); functions will not be attributed to source files"
  fi
  if [ -s "$BUILD_LOG" ]; then tools/ci/reports.sh "$BUILD_LOG"; else tools/ci/reports.sh; fi
}

# = `make vtest-check-ci`.  Deletes the run proofs' build products, rebuilds
# the green set (vtest-lean/Vtest.lean) keeping going past a red proof, and
# lets the run table be the verdict; it writes the table to the summary itself.
step_vtest() { tools/ci/vtest.sh check-ci; }

step_test_tools() { make test-tools; }

step_dead_imports() {
  local out="$XV6_CI_OUT/imports"
  tools/ci/dead_imports.sh "$out" | tee "$out.txt" || return 1
  {
    echo "## Dead imports (Lean, informational)"
    echo
    grep -E '^dead-imports: [0-9]+ dead' "$out.txt" | sed 's/^dead-imports: //'
    echo
    echo "\`redundant\`: reachable through another import anyway. \`high\`: nothing in"
    echo "the import or its closure is needed. \`manual\`: as \`high\`, but the file's text"
    echo "names something from it -- read before removing. Apply with"
    echo "\`tools/ci/dead_imports.sh --apply\`, then rebuild the whole tree."
    echo
    echo "<details><summary>The dead imports of <code>Xv6/</code> and <code>MachCSL/</code></summary>"
    echo
    echo '```'
    grep -E '^(## |(Xv6|MachCSL)\.)' "$out/shake/dead.txt" || true
    echo '```'
    echo
    echo "</details>"
  } >> "$GITHUB_STEP_SUMMARY"
}

# ------------------------------------------------------------- the driver

known() { local s; for s in "${SEQUENCE[@]}" "${EXTRA[@]}"; do [ "$s" = "$1" ] && return 0; done; return 1; }

# Append this step's summary to the real one, cut to the size GitHub accepts.
flush_summary() {
  local tmp=$1 size
  size=$(wc -c < "$tmp")
  [ "$size" -gt 0 ] || { rm -f "$tmp"; return 0; }
  if [ "$size" -gt "$SUMMARY_MAX" ]; then
    # Cut at a line boundary; close any <details> the cut left open.
    head -c "$SUMMARY_MAX" "$tmp" | sed '$d' > "$tmp.cut"
    {
      cat "$tmp.cut"
      printf '\n\n</details>\n\n> :warning: This summary was %d bytes; GitHub accepts 1 MiB per step, so it was cut at %d. The full reports are in `%s/` of the workspace.\n' \
        "$size" "$SUMMARY_MAX" "$XV6_CI_OUT"
    } >> "$REAL_SUMMARY"
    rm -f "$tmp.cut"
    echo "::warning::step summary cut from $size to $SUMMARY_MAX bytes (GitHub's limit is 1 MiB per step)"
  else
    cat "$tmp" >> "$REAL_SUMMARY"
  fi
  rm -f "$tmp"
}

run_step() {
  local step=$1 rc=0 t0=$SECONDS tmp
  tmp=$(mktemp)
  say "[$step]"
  GITHUB_STEP_SUMMARY="$tmp" "step_${step//-/_}" || rc=$?
  flush_summary "$tmp"
  TIMES+=("$step $((SECONDS - t0)) $rc")
  return "$rc"
}

keep_going=0; from=""; steps=()
while [ $# -gt 0 ]; do
  case "$1" in
    -k|--keep-going) keep_going=1 ;;
    --from) shift; from=${1:?--from needs a step} ;;
    --list) printf '%s\n' "${SEQUENCE[@]}"; exit 0 ;;
    -h|--help) sed -n '2,/^set -uo/p' "${BASH_SOURCE[0]}" | sed '$d' | sed -E 's/^# ?//'; exit 0 ;;
    -*) echo "run_all.sh: unknown option $1 (see --help)" >&2; exit 2 ;;
    *) known "$1" || { echo "run_all.sh: unknown step '$1'; steps: ${SEQUENCE[*]} ${EXTRA[*]}" >&2; exit 2; }
       steps+=("$1") ;;
  esac
  shift
done
whole=0
if [ ${#steps[@]} -eq 0 ]; then
  whole=1
  if [ -n "$from" ]; then
    known "$from" || { echo "run_all.sh: unknown step '$from'" >&2; exit 2; }
    seen=0
    for s in "${SEQUENCE[@]}"; do
      [ "$s" = "$from" ] && seen=1
      [ "$seen" -eq 1 ] && steps+=("$s")
    done
  else
    steps=("${SEQUENCE[@]}")
  fi
fi

mkdir -p "$XV6_CI_OUT"
if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  REAL_SUMMARY=$GITHUB_STEP_SUMMARY
else
  REAL_SUMMARY="$XV6_CI_OUT/summary.md"
  [ "$whole" -eq 1 ] && [ -z "$from" ] && : > "$REAL_SUMMARY"
fi

TIMES=(); failed=()
for s in "${steps[@]}"; do
  if run_step "$s"; then :; else
    failed+=("$s")
    [ "$keep_going" -eq 1 ] || break
  fi
done

if [ ${#steps[@]} -gt 1 ]; then
  echo
  echo "== run_all.sh: step times"
  for t in "${TIMES[@]}"; do
    read -r name secs rc <<< "$t"
    printf '  %-16s %5ds  %s\n' "$name" "$secs" "$([ "$rc" -eq 0 ] && echo ok || echo "FAILED ($rc)")"
  done
  for s in "${steps[@]:${#TIMES[@]}}"; do printf '  %-16s %6s  not run\n' "$s" "-"; done
  [ -n "${GITHUB_STEP_SUMMARY:-}" ] || echo "== the job summary is $REAL_SUMMARY"
fi
if [ ${#failed[@]} -gt 0 ]; then
  echo "run_all.sh: FAILED: ${failed[*]}" >&2
  exit 1
fi
[ ${#steps[@]} -gt 1 ] && echo "run_all.sh: all ${#steps[@]} steps passed"
exit 0
