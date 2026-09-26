#!/usr/bin/env bash
# Import-graph / critical-path / unused-import analysis (see notes/import_graph_report.md).
#
#   tools/import_analysis.sh BUILD_LOG OUT_DIR [REV]
#
# BUILD_LOG: a clean `lake build` log with per-module times (`✔ [i/N] Built M (12s)`).
# Run from a tree whose .lake/build matches REV (default HEAD) -- e.g. a worktree at REV
# after `lake build Xv6 MachCSL`; the Lean dumpers read the .olean files.
set -euo pipefail
LOG=$(readlink -f "$1"); OUT=$(readlink -f "$2"); REV=${3:-HEAD}
T=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$OUT"
REVH=$(git rev-parse "$REV")
# sources at REV for the text checks (open/namespace scan, name mentions)
rm -rf "$OUT/src" && mkdir -p "$OUT/src"
git archive "$REVH" MachCSL Xv6 model/Lean_RV64D/LeanRV64D vendor/lean-sail/Sail | tar -x -C "$OUT/src"

lake env lean --run "$T/ImportNeeds.lean" Xv6 MachCSL > "$OUT/needs.tsv" 2> "$OUT/needs.err"
lake env lean --run "$T/ConstDeps.lean"   Xv6 MachCSL > "$OUT/constdeps.tsv"
python3 "$T/import_shake.py" "$OUT/needs.tsv" --src "$OUT/src" --out "$OUT/shake" 2> "$OUT/shake.err"
python3 "$T/import_graph.py" --log "$LOG" --git-rev "$REVH" > "$OUT/graph.txt"
for m in dead exact; do
  python3 "$T/import_graph.py" --log "$LOG" --git-rev "$REVH" --move "$OUT/shake/edits_$m.txt" > "$OUT/graph_$m.txt"
done
for mode in move spec; do
  python3 "$T/split_whatif.py" --needs "$OUT/needs.tsv" --consts "$OUT/constdeps.tsv" \
    --log "$LOG" --rev "$REVH" --mode $mode --no-model --steps 30 > "$OUT/whatif_$mode.txt"
done
grep -h "critical path:" "$OUT"/graph*.txt | grep modules
grep -h "^final" "$OUT"/whatif_*.txt
echo "dead imports: $OUT/shake/dead.txt; edit lists: $OUT/shake/edits_{dead,exact}.txt"
echo "apply with: tools/apply_import_edits.py $OUT/shake/edits_dead.txt <tree>"
