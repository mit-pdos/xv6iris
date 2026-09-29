#!/usr/bin/env bash
# toolchain_check.sh [SWITCH] -- is this opam switch exactly the toolchain opam/xv6rocq.export
# describes?  Re-exports the switch (full, frozen) and diffs it against the file: an empty diff
# means every package, version and source pin is identical, i.e. .vo files built here are
# interchangeable with CI's and the container's.  Exit 0 when identical, 1 with the diff otherwise.
# Default SWITCH: the Makefile's (/shared/xv6rocq), or the current one if that does not exist.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
switch=${1:-${SWITCH:-/shared/xv6rocq}}
[ -d "$switch" ] || [ -d "$switch/_opam" ] || switch=$(opam switch show 2>/dev/null || echo "$switch")
tmp=$(mktemp); trap 'rm -f "$tmp"' EXIT
if ! opam switch export --full --freeze --switch="$switch" "$tmp" 2>/dev/null; then
  echo "toolchain-check: cannot export switch '$switch' (does it exist? try SWITCH=<path>)"; exit 2
fi
if diff -q "$tmp" "$here/opam/xv6rocq.export" >/dev/null; then
  echo "toolchain-check: switch $switch is IDENTICAL to opam/xv6rocq.export"
  exit 0
fi
echo "toolchain-check: switch $switch DIFFERS from opam/xv6rocq.export:"
# the readable part first: the roots/installed lists; then the full diff, capped
diff <(sed -n '1,/^pinned:/p;/^pinned:/q' "$tmp") <(sed -n '1,/^pinned:/p;/^pinned:/q' "$here/opam/xv6rocq.export") | head -40
echo "(full diff: opam switch export --full --freeze --switch=$switch - | diff - opam/xv6rocq.export)"
exit 1
