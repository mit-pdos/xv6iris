#!/usr/bin/env bash
# tools/ci/dead_imports.sh [--apply] [OUT_DIR]
#
# The dead-import sweep, run nightly with --apply by
# .github/workflows/lean-dead-imports.yml (Rocq's was
# iris/detect_unused_imports.py, run by dead-imports.yml on the `rocq`
# branch).  Finds `import` lines of Xv6/ and MachCSL/ that can go, and with
# --apply removes them.
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
# Instances, notations, tactics and simp sets are in the elaborator's record,
# so unlike Rocq's name-reference shortlist they are already accounted for.
#
# --apply edits the sources, BUILD-CONFIRMED (tools/ci/dead_imports_verify.py):
# the needs come from the elaborated terms, so a name a file mentions only in
# tactic text (an unused `simp` argument, say) is invisible to them, and its
# import can look dead and not be.  The edits are applied and the tree rebuilt,
# and whatever the build refutes is backed off, until `lake build Xv6 MachCSL`
# is green; that script's header has the rules.  Other consumers of the two
# libraries (vtest-lean/, tools/ci/envfacts/) are not in that build: before
# committing, run the whole CI sequence, as the nightly job does.  A failure
# leaves the sources as they were and exits non-zero.
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
# MachCSL/ are ours to edit, so only those are counted and applied (and of
# those, not the generated files: see below).
awk -F'\t' '/^## /{split($0, h, /[ :]/); c = h[2]; next}
            /^(Xv6|MachCSL)\./{n[c]++; t++}
            END{printf "dead-imports: %d dead import line(s) in Xv6/ and MachCSL/", t;
                for (k in n) printf "  %s=%d", k, n[k]; printf "\n"}' "$OUT/shake/dead.txt"
echo "dead-imports: the list is $OUT/shake/dead.txt (redundant / high / manual: see the header of this script)"
# Generated files (first line `-- AUTO-GENERATED ...`; tools/check_gen.py
# regenerates them) are not ours to edit either: their imports are whatever
# the generator writes.  Leaving a removal out only keeps an import, so the
# remaining edits stay sound.  A RE-ADD to one cannot be left out (the module
# would lose what an upstream removal took away), so that is an error.
: > "$OUT/shake/edits_local.txt"; : > "$OUT/shake/edits_generated.txt"
grep -E '^(Xv6|MachCSL)\.' "$OUT/shake/edits_dead.txt" | while read -r mod op; do
  if head -1 "${mod//.//}.lean" | grep -q '^-- AUTO-GENERATED'; then
    echo "$mod $op" >> "$OUT/shake/edits_generated.txt"
  else
    echo "$mod $op" >> "$OUT/shake/edits_local.txt"
  fi
done
if grep -q ' +' "$OUT/shake/edits_generated.txt"; then
  echo "dead-imports: a generated file would need an import re-added, so the edits cannot be applied:" >&2
  grep ' +' "$OUT/shake/edits_generated.txt" >&2
  [ "$apply" -eq 0 ] || exit 1
fi
if [ -s "$OUT/shake.err" ]; then
  echo "dead-imports: import_shake.py warnings:"; head -20 "$OUT/shake.err"
fi
if [ "$apply" -eq 1 ]; then
  if [ -s "$OUT/shake/edits_local.txt" ]; then
    python3 tools/ci/dead_imports_verify.py "$OUT/shake/edits_local.txt" "$OUT/needs.tsv" "$OUT"
    echo "dead-imports: applied $OUT/edits_verified.txt (build-confirmed)"
  else
    echo "dead-imports: nothing to apply"
  fi
fi
