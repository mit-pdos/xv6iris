#!/usr/bin/env bash
# migrate.sh FILE.v...  -- rewrite Rocq sources written for Iris 4.4 / stdpp 1.12 / coq-sail 0.20.1
# for the toolchain in opam/xv6rocq.export (Iris master, stdpp master, coq-sail 0.20.3), in place.
# Deterministic and idempotent-enough for one pass over a file that has not been migrated; do NOT
# run it twice on the same file (the *_frac renames would be re-applied). See README.md here.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
[ $# -gt 0 ] || { echo "usage: $0 FILE.v..." >&2; exit 2; }
sed -E -i -f "$here/migrate-master.sed" "$@"
perl -0pi "$here/unwrap.pl" "$@"
for f in "$@"; do python3 "$here/migrate_imports.py" "$f"; done
echo "migrated: $#"
