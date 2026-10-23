#!/usr/bin/env bash
# tools/ci/tcb.sh [--build] [--update] [--self-test] -- THE TRUSTED BASE OF THE STATEMENTS
# (Rocq: tools/tcb/tcb-report.sh + tcb_report.py, CI step "Adequacy trusted base").
#
# Runs tools/tcb/Tcb.lean against an ALREADY-BUILT tree: for each top theorem,
# the definitions its STATEMENT transitively depends on (what one must read to
# trust it), per file, with declaration and line counts; and checks two things
# against tools/tcb/expected.json -- per theorem, the SET of this tree's modules
# the statement reaches and the axioms / `opaque` constants it reaches; and,
# shared by all theorems, the CONTENT of every trusted constant of MachCSL/,
# Xv6/ and model/Xv6Extras.lean, a hash of its elaborated type and value,
# grouped by source declaration (Tcb.lean's header, "THE CHECK").  ~2 s (a
# native executable, built here if CI's build step has not), ~3 GB.
#
#   --build      `lake build Xv6 MachCSL` first.
#   --update     rewrite tools/tcb/expected.json from this run instead of
#                checking against it.  Commit the result in the same commit
#                and READ THE DIFF (notes/model-policy.md section 6, "The
#                trusted base's content").
#   --self-test  instead of the check, run tools/tcb/selftest.py: the tool
#                against a doctored copy of the baseline must FAIL, naming
#                exactly the three doctored constants.  CI runs it right
#                after the check (tools/ci/run_all.sh, step tcb).
#
# EXIT STATUS: non-zero iff a set moved, or a pinned constant's content moved,
# entered or left (every problem names the declaration and its file:lines),
# or Lean cannot load the tree; with --self-test, iff the doctored run did NOT
# fail as required.
#
# Output in $XV6_CI_OUT (default .lake/ci): tcb.json, tcb.md, tcb.txt, tcb.log;
# the self-test's in $XV6_CI_OUT/tcb-selftest/ (its log tcb-selftest.log beside
# them).  The tables are also appended to $GITHUB_STEP_SUMMARY when that is
# set, and the plain tables (`=== TCB <theorem> ===`) go to stdout, so they are
# in the run log.
#
# Needs a machine sized for a Lean build (README: "Build"): run it on
# a build server or in CI, e.g.
#   tools/ci/tcb.sh && tools/ci/tcb.sh --self-test
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
command -v lake >/dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"
export XV6_CI_OUT="${XV6_CI_OUT:-.lake/ci}"
mkdir -p "$XV6_CI_OUT"

unset XV6_TCB_UPDATE
mode=check
for arg in "$@"; do
  case "$arg" in
    --build) lake build Xv6 MachCSL ;;
    --update) export XV6_TCB_UPDATE=1 ;;
    --self-test) mode=selftest ;;
    *) echo "usage: tools/ci/tcb.sh [--build] [--update] [--self-test]" >&2; exit 2 ;;
  esac
done
if [ "$mode" = selftest ] && [ -n "${XV6_TCB_UPDATE:-}" ]; then
  echo "tools/ci/tcb.sh: --self-test and --update exclude each other" >&2; exit 2
fi

log="$XV6_CI_OUT/tcb.log"
if [ "$mode" = check ]; then
  rm -f "$XV6_CI_OUT/tcb.json" "$XV6_CI_OUT/tcb.md" "$XV6_CI_OUT/tcb.txt"
else
  log="$XV6_CI_OUT/tcb-selftest.log"
fi

rc=0
# tools/tcb/Tcb.lean is a native executable in its own lake package (its
# header): build it (nothing to do when up to date; CI builds it alongside
# the proofs), then run it on the built tree through `lake env` -- or, with
# --self-test, let tools/tcb/selftest.py run it against a doctored baseline.
lake -d tools/tcb build tcb -q > "$log" 2>&1 || rc=$?
if [ "$rc" -eq 0 ]; then
  if [ "$mode" = check ]; then
    lake env tools/tcb/.lake/build/bin/tcb >> "$log" 2>&1 || rc=$?
  else
    python3 tools/tcb/selftest.py >> "$log" 2>&1 || rc=$?
  fi
fi
cat "$log"

if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  if [ "$mode" = selftest ]; then
    if [ "$rc" -eq 0 ]; then
      echo "Self-test of the trusted-base check (\`tools/tcb/selftest.py\`): the tool fails on a doctored baseline, naming exactly the three doctored constants." >> "$GITHUB_STEP_SUMMARY"
    else
      {
        echo "> :x: **The trusted-base check's self-test failed** (exit $rc): the tool did not fail on a doctored baseline as it must."
        echo
        echo '```'
        tail -40 "$log"
        echo '```'
      } >> "$GITHUB_STEP_SUMMARY"
    fi
  elif [ -f "$XV6_CI_OUT/tcb.md" ]; then
    cat "$XV6_CI_OUT/tcb.md" >> "$GITHUB_STEP_SUMMARY"
  else
    {
      echo "## Trusted base of the top theorems"
      echo
      echo "> :x: \`tools/tcb/Tcb.lean\` did not run (exit $rc)."
      echo
      echo '```'
      tail -40 "$log"
      echo '```'
    } >> "$GITHUB_STEP_SUMMARY"
  fi
fi

if [ "$rc" -ne 0 ]; then
  if [ "$mode" = selftest ]; then
    echo "::error::The trusted-base check's self-test failed (exit $rc); see $log." >&2
  else
    echo "::error::The trusted-base check failed (exit $rc); see $XV6_CI_OUT/tcb.md." >&2
  fi
fi
exit "$rc"
