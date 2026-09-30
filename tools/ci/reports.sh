#!/usr/bin/env bash
# tools/ci/reports.sh [BUILD_LOG]
#
# The post-build reports, in the order Rocq's ci.yml runs them, against the
# tree `lake build Xv6 MachCSL` just built:
#
#   1. environment facts  tools/ci/envfacts.sh          -> .lake/ci/envfacts.tsv
#   2. build profile      tools/proof_profile.py         -> .lake/ci/profile/report.md   (informational)
#   3. proof coverage     tools/proof_coverage.py --check -> .lake/ci/coverage.md        (BLOCKING)
#   4. dead code          tools/find_dead.py              -> .lake/ci/dead.md            (informational)
#
# BUILD_LOG is the timed log of tools/ci/timed_build.sh; without it the
# profile is skipped.  Each report is printed and, when $GITHUB_STEP_SUMMARY
# is set, appended to the job summary.
#
# EXIT STATUS: non-zero iff the environment facts could not be produced (a
# top theorem of tools/ci/roots.txt is gone, a stale allowlist row) or the
# coverage check failed (a kernel function that is not proven, linked and
# reached and has no row in tools/ci/coverage_allow.txt; a user function of
# the baseline that regressed; a stale manifest/allow row).  The coverage
# report is written before the status is decided -- a failing run is exactly
# when you want to read it.  The profile and the dead-code report never fail
# the step.
#
# For source-file attribution in the coverage report, check out xv6-riscv/
# first (best effort, as Rocq's CI does; the numbers do not depend on it):
#     test -d xv6-riscv || timeout 60 git clone --depth 1 \
#         https://github.com/mit-pdos/xv6-riscv xv6-riscv || true
#
# Runs lean: on the build machine only (README: "Build").
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
LOG=${1:-}
OUT=.lake/ci
SUMMARY=${GITHUB_STEP_SUMMARY:-/dev/null}
mkdir -p "$OUT"

tools/ci/envfacts.sh "$OUT/envfacts.tsv" || { echo "reports: envfacts failed" >&2; exit 1; }

if [ -n "$LOG" ]; then
  python3 tools/proof_profile.py --build-log "$LOG" --out-dir "$OUT/profile" --top 30 > /dev/null || true
  [ -f "$OUT/profile/report.md" ] && cat "$OUT/profile/report.md" | tee -a "$SUMMARY"
else
  echo "reports: no build log given, profile skipped"
fi

rc=0
python3 tools/proof_coverage.py --facts "$OUT/envfacts.tsv" --format md \
  --out "$OUT/coverage.md" --check || rc=$?
cat "$OUT/coverage.md" >> "$SUMMARY"
python3 tools/proof_coverage.py --facts "$OUT/envfacts.tsv" | sed -n '1,/^legend/p'

python3 tools/find_dead.py --facts "$OUT/envfacts.tsv" --triage --top 40 || true
python3 tools/find_dead.py --facts "$OUT/envfacts.tsv" --format md --out "$OUT/dead.md" > /dev/null || true
[ -f "$OUT/dead.md" ] && cat "$OUT/dead.md" >> "$SUMMARY"

if [ "$rc" -ne 0 ]; then
  echo "::error::proof coverage check failed; see the step summary ($OUT/coverage.md)."
fi
exit "$rc"
