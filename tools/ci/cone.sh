#!/usr/bin/env bash
# tools/ci/cone.sh — THE VETTING-CONE GATE (mini plan rev 4 §4 K5): for every line `<Module> <Decl> <limit>` of
# tools/ci/cone-targets.txt, compute the statement cone (tools/cone/Cone.lean), write its manifest to
# notes/mini/cone/<Decl>.txt, and FAIL if the Weak.Mini line count exceeds <limit> or any declaration lies outside
# the allowlist (ALIEN).  Run after the modules are built.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
command -v lake >/dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"
mkdir -p notes/mini/cone
fail=0
while read -r mod decl limit; do
  [[ -z "${mod:-}" || "$mod" == \#* ]] && continue
  out="notes/mini/cone/${decl}.txt"
  lake env lean --run tools/cone/Cone.lean "$mod" "$decl" > "$out"
  head -1 "$out"
  if grep -q '^MISSING' "$out"; then echo "cone: $decl missing"; fail=1; continue; fi
  mini=$(head -1 "$out" | sed -n 's/.* mini=\([0-9]*\).*/\1/p')
  if [ "$mini" -gt "$limit" ]; then echo "cone: $decl Weak.Mini lines $mini > $limit"; fail=1; fi
  if grep -q '^ALIEN' "$out"; then echo "cone: $decl has declarations outside the allowlist:"; grep '^ALIEN' "$out" | head; fail=1; fi
done < tools/ci/cone-targets.txt
[ "$fail" -eq 0 ] && echo "cone.sh: all cones within limits" || { echo "::error::cone gate failed"; exit 1; }
