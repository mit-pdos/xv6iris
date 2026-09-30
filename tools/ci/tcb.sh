#!/usr/bin/env bash
# tools/ci/tcb.sh [--build] [--update] -- THE TRUSTED BASE OF THE STATEMENTS
# (Rocq: tools/tcb/tcb-report.sh + tcb_report.py, CI step "Adequacy trusted base").
#
# Runs tools/tcb/Tcb.lean against an ALREADY-BUILT tree: for each top theorem,
# the definitions its STATEMENT transitively depends on (what one must read to
# trust it), per file, with declaration and line counts.  ~15 s, ~3 GB.
#
#   --build    `lake build Xv6 MachCSL` first.
#   --update   rewrite tools/tcb/expected.json from this run instead of
#              checking against it.  Commit the result and READ THE DIFF.
#
# EXIT STATUS: non-zero iff, for some theorem, the set of this tree's modules
# its statement reaches, or the axioms / `opaque` constants it reaches, differ
# from tools/tcb/expected.json -- or Lean cannot load the tree.
#
# Output in $XV6_CI_OUT (default .lake/ci): tcb.json, tcb.md, tcb.txt, tcb.log.
# The tables are also appended to $GITHUB_STEP_SUMMARY when that is set, and
# the plain tables (`=== TCB <theorem> ===`) go to stdout, so they are in the
# run log.
#
# Needs a machine sized for a Lean build (README: "Build"): run it on
# a build server or in CI, e.g.
#   tools/ci/tcb.sh
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
command -v lake >/dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"
export XV6_CI_OUT="${XV6_CI_OUT:-.lake/ci}"
mkdir -p "$XV6_CI_OUT"
rm -f "$XV6_CI_OUT/tcb.json" "$XV6_CI_OUT/tcb.md" "$XV6_CI_OUT/tcb.txt"

unset XV6_TCB_UPDATE
for arg in "$@"; do
  case "$arg" in
    --build) lake build Xv6 MachCSL ;;
    --update) export XV6_TCB_UPDATE=1 ;;
    *) echo "usage: tools/ci/tcb.sh [--build] [--update]" >&2; exit 2 ;;
  esac
done

rc=0
lake env lean tools/tcb/Tcb.lean > "$XV6_CI_OUT/tcb.log" 2>&1 || rc=$?
cat "$XV6_CI_OUT/tcb.log"

if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  if [ -f "$XV6_CI_OUT/tcb.md" ]; then
    cat "$XV6_CI_OUT/tcb.md" >> "$GITHUB_STEP_SUMMARY"
  else
    {
      echo "## Trusted base of the top theorems"
      echo
      echo "> :x: \`tools/tcb/Tcb.lean\` did not run (exit $rc)."
      echo
      echo '```'
      tail -40 "$XV6_CI_OUT/tcb.log"
      echo '```'
    } >> "$GITHUB_STEP_SUMMARY"
  fi
fi

if [ "$rc" -ne 0 ]; then
  echo "::error::The trusted-base check failed (exit $rc); see $XV6_CI_OUT/tcb.md." >&2
fi
exit "$rc"
