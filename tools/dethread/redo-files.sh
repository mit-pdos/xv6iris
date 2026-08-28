#!/bin/bash
# Re-apply the whole rank-1c de-threading to the CURRENT upstream version of
# the .v files named on the command line.  Use it when a lane that restructures
# those files (the continuation-fold lane) lands ahead of you and the rebase
# conflicts: take the other lane's version whole, then run this.
#
#   BASE=<upstream commit> tools/dethread/redo-files.sh ProofIput.v ...
#
# BASE is the upstream commit the conflicted files come from -- i.e. the commit
# this branch is being rebased ONTO, whose tree is the pre-de-threading one.
# The sweep is deterministic, so what comes out is what it would have produced
# had the other lane landed first.  Only the named files are copied back; the
# scratch tree is left behind so the run can be inspected.
set -e
D=$(cd "$(dirname "$0")" && pwd)
cd "$D/../.."
BASE=${BASE:?set BASE to the upstream commit the conflicted files come from}
W=$(mktemp -d)
mkdir -p "$W/iris"
git archive "$BASE" iris | tar -x -C "$W"
for f in "$@"; do git show "origin/main:iris/$f" > "$W/iris/$f"; done
export R1C_IRIS="$W/iris" R1C_USED="$W/used.txt"
python3 "$D/rewrite.py" apply 2> "$W/p1.log" >/dev/null || true
grep 'stats:' "$W/p1.log"
python3 "$D/cleanup.py" >/dev/null 2>&1 || true
python3 "$D/phase2.py" apply 2> "$W/p2.log" >/dev/null || true
grep 'stats:' "$W/p2.log"
grep 'still used' "$W/p2.log" | sed 's/^ *//' > "$W/used.txt" || true
python3 "$D/fixuse.py" apply 2>&1 | head -1
for f in "$@"; do cp "$W/iris/$f" "iris/$f"; done
echo "copied back: $*   (scratch tree $W)"
