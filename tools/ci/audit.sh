#!/usr/bin/env bash
# tools/ci/audit.sh [--build] -- THE ASSUMPTION AUDIT (Rocq: `make audit-all-only`,
# CI step "Assumption audits").
#
# Runs tools/audit/Audit.lean against an ALREADY-BUILT tree: the axioms of each
# top theorem, the `opaque` constants in its cone and the Sail platform hooks,
# checked against tools/audit/baseline.json.  That file's header says what a
# reader must trust.  ~35 s, ~5 GB.
#
#   --build   `lake build Xv6 MachCSL` first (Rocq's `make audit` vs `audit-only`).
#             Without it a stale .lake/build is audited as it stands.
#
# EXIT STATUS: non-zero iff the audit fails (an axiom or opaque outside the
# baseline, a stale baseline entry, a `sorryAx` anywhere in MachCSL/Xv6) or
# Lean cannot load the tree.  No pipe masks it.
#
# Output in $XV6_CI_OUT (default .lake/ci): audit.json, audit.md, audit.log.
# The summary is also appended to $GITHUB_STEP_SUMMARY when that is set.
#
# Needs a machine sized for a Lean build (README: "Build"): run it on
# a build server or in CI, e.g.
#   tools/ci/audit.sh
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
command -v lake >/dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"
export XV6_CI_OUT="${XV6_CI_OUT:-.lake/ci}"
mkdir -p "$XV6_CI_OUT"
rm -f "$XV6_CI_OUT/audit.json" "$XV6_CI_OUT/audit.md"

if [ "${1:-}" = "--build" ]; then
  lake build Xv6 MachCSL
fi

rc=0
lake env lean tools/audit/Audit.lean > "$XV6_CI_OUT/audit.log" 2>&1 || rc=$?
cat "$XV6_CI_OUT/audit.log"

if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  if [ -f "$XV6_CI_OUT/audit.md" ]; then
    cat "$XV6_CI_OUT/audit.md" >> "$GITHUB_STEP_SUMMARY"
  else
    {
      echo "## Assumption audit"
      echo
      echo "> :x: \`tools/audit/Audit.lean\` did not run (exit $rc)."
      echo
      echo '```'
      tail -40 "$XV6_CI_OUT/audit.log"
      echo '```'
    } >> "$GITHUB_STEP_SUMMARY"
  fi
fi

if [ "$rc" -ne 0 ]; then
  echo "::error::The assumption audit failed (exit $rc); see $XV6_CI_OUT/audit.md." >&2
fi
exit "$rc"
