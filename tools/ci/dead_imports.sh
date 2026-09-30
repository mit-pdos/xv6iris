#!/usr/bin/env bash
# tools/ci/dead_imports.sh [--apply] [OUT_DIR]
#
# The dead-import sweep (Rocq: iris/detect_unused_imports.py, run nightly by
# .github/workflows/dead-imports.yml).  Finds `import` lines of Xv6/ and
# MachCSL/ that can go, and with --apply removes them.
#
# HOW.  Lean 4.32's own `lake shake` refuses this tree ("`lake shake` only
# works with `module`s currently": the files are not in the new module
# system), so the needs computation is
# tools/ImportNeeds.lean -- a port of shake's -- run as a metaprogram over the
# BUILT environment: module `i` needs module `j` when a constant of `i`
# mentions one of `j`, or the elaborator recorded `j` as used by `i` (macros,
# tactics, syntax, simp sets, attributes, instances: `getExtraModUses`).
# tools/import_shake.py turns the needs into
#
#     OUT_DIR/shake/dead.txt         every dead import, classified
#         redundant  the module is reachable through another import anyway
#                    (dropping it changes nothing in the DAG)
#         high       nothing in the import or its closure is needed
#         manual     as `high`, but the file's TEXT names something from it
#                    (an `open`, an unused simp argument, a notation): read it
#     OUT_DIR/shake/edits_dead.txt   `Mod -Imp` / `Mod +Imp`: remove every dead
#                    import and re-add what a module loses because an upstream
#                    module stopped importing it
#
# Unlike Rocq's checker there is no per-candidate recompile: the needs come
# from the elaborator's own record rather than from a name-reference
# shortlist, so instances, notations and tactics are already accounted for.
#
# --apply edits the sources (tools/apply_import_edits.py).  THE CALLER MUST
# THEN REBUILD THE WHOLE TREE (`lake build Xv6 MachCSL`) before committing:
# that build is the only gate on what lands, exactly as in Rocq's workflow.
#
# INFORMATIONAL: without --apply the exit status is 0 whatever is found
# (non-zero only if the analysis itself could not run).  Needs a built tree;
# run on a machine sized for a Lean build (README: "Build").
# ~2 min.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
command -v lake >/dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"
apply=0
if [ "${1:-}" = "--apply" ]; then apply=1; shift; fi
OUT=${1:-.lake/ci/imports}
mkdir -p "$OUT"
lake env lean --run tools/ImportNeeds.lean Xv6 MachCSL > "$OUT/needs.tsv" 2> "$OUT/needs.err"
python3 tools/import_shake.py "$OUT/needs.tsv" --src . --out "$OUT/shake" 2> "$OUT/shake.err" \
  > "$OUT/summary.txt"
# The analysis also covers the generated model and lean-sail; only Xv6/ and
# MachCSL/ are ours to edit, so only those are counted and applied.
awk -F'\t' '/^## /{split($0, h, /[ :]/); c = h[2]; next}
            /^(Xv6|MachCSL)\./{n[c]++; t++}
            END{printf "dead-imports: %d dead import line(s) in Xv6/ and MachCSL/", t;
                for (k in n) printf "  %s=%d", k, n[k]; printf "\n"}' "$OUT/shake/dead.txt"
echo "dead-imports: the list is $OUT/shake/dead.txt (redundant / high / manual: see the header of this script)"
grep -E '^(Xv6|MachCSL)\.' "$OUT/shake/edits_dead.txt" > "$OUT/shake/edits_local.txt" || true
if [ -s "$OUT/shake.err" ]; then
  echo "dead-imports: import_shake.py warnings:"; head -20 "$OUT/shake.err"
fi
if [ "$apply" -eq 1 ]; then
  if [ -s "$OUT/shake/edits_local.txt" ]; then
    python3 tools/apply_import_edits.py "$OUT/shake/edits_local.txt" .
    echo "dead-imports: applied $OUT/shake/edits_local.txt -- now REBUILD before committing"
  else
    echo "dead-imports: nothing to apply"
  fi
fi
