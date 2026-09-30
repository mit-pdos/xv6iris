#!/usr/bin/env bash
# tools/ci/timed_build.sh LOG [--clean] [LAKE BUILD TARGETS...]
#
# `lake build` with a TIMED log: the input of tools/proof_profile.py.  Every
# line lake prints is prefixed with the wall-clock instant it arrived,
#
#     @1759200000.123456 ✔ [324/2657] Built MachCSL.Dev.DevIds (260ms)
#
# and the log is framed by `@start <epoch> nproc=<n>`, `@cpu user=<s> sys=<s>`
# (CPU of lake and every lean it ran) and `@end <epoch> rc=<status>`.  Lake's
# own `(260ms)` is the module's wall; the instant is when it FINISHED, so
# start = finish - wall, which is what the parallelism chart is drawn from
# (the role of the .vo mtimes in Rocq's profile).
#
# Targets default to `Xv6 MachCSL`.  `--clean` removes the build outputs of
# this package and of the two path dependencies first (the model and
# lean-sail), so the log is a FULL build: a profile of an incremental build
# only describes what happened to be stale.  The fetched packages
# (.lake/packages) are kept.
#
# Exit status is lake's (the pipe does not mask it).  CI:
#     tools/ci/timed_build.sh "$RUNNER_TEMP/lake-build.log" --clean
# By hand, detached, then follow the log until `@end`:
#     setsid nohup tools/ci/timed_build.sh build.log --clean >/dev/null 2>&1 < /dev/null &
#     tail -3 build.log
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
command -v lake >/dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"
[ $# -ge 1 ] || { echo "usage: $0 LOG [--clean] [targets...]" >&2; exit 2; }
LOG=$1; shift
if [ "${1:-}" = "--clean" ]; then
  shift
  rm -rf .lake/build model/Lean_RV64D/.lake/build vendor/lean-sail/.lake/build
fi
[ $# -gt 0 ] || set -- Xv6 MachCSL
echo "@start $EPOCHREALTIME nproc=$(nproc)" > "$LOG"
lake build "$@" 2>&1 | while IFS= read -r line; do
  printf '@%s %s\n' "$EPOCHREALTIME" "$line"
done >> "$LOG"
rc=${PIPESTATUS[0]}
# `times`: second line is the children's user and system time (lake + leans).
# (`times` must run in THIS shell -- in a subshell it reports the subshell's.)
tf=$(mktemp); times > "$tf"; read -r cu cs < <(tail -1 "$tf"); rm -f "$tf"
tosec() { local m=${1%%m*} s=${1#*m}; s=${s%s}; awk -v m="$m" -v s="$s" 'BEGIN{printf "%.1f", m*60+s}'; }
echo "@cpu user=$(tosec "$cu") sys=$(tosec "$cs")" >> "$LOG"
echo "@end $EPOCHREALTIME rc=$rc" >> "$LOG"
exit "$rc"
