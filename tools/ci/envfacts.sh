#!/usr/bin/env bash
# tools/ci/envfacts.sh [OUT]       -- dump the environment facts the report tools read.
# tools/ci/envfacts.sh --build-only -- only build the executable (CI does this
#                                     alongside the proof build: tools/ci/run_all.sh)
#
# Builds tools/ci/envfacts/EnvFacts.lean as a native executable (its own lake
# package: it imports only `Lean`; ~10 s, and nothing when it is up to date),
# then runs it against the BUILT tree under `lake env`, whose LEAN_PATH is how
# it finds Xv6 and MachCSL -- so `lake build Xv6 MachCSL` must have succeeded;
# nothing of the proofs is rebuilt here.  OUT defaults to
# .lake/ci/envfacts.tsv.  Consumers: tools/proof_coverage.py (coverage) and
# tools/find_dead.py (dead code).  ~3 s on all cores, ~5 GB.
#
# Exit status: non-zero when the metaprogram fails -- a top theorem of
# tools/ci/roots.txt that no longer exists, a stale allowlist row, or a pc
# predicate that was renamed.  Each of those would silently empty a report.
#
# Needs a machine sized for a Lean build (README: "Build"); from the
# repository root:
#   bash tools/ci/envfacts.sh
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
command -v lake >/dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"
EXE=tools/ci/envfacts/.lake/build/bin/envfacts
# (run from the repository root, so elan picks the repository's lean-toolchain)
lake -d tools/ci/envfacts build envfacts -q || { echo "envfacts: building $EXE failed" >&2; exit 1; }
[ "${1:-}" = "--build-only" ] && exit 0
OUT=${1:-.lake/ci/envfacts.tsv}
mkdir -p "$(dirname "$OUT")"
rm -f "$OUT"
XV6_ENVFACTS_OUT="$OUT" lake env "$EXE"
test -s "$OUT" || { echo "envfacts: $OUT was not written" >&2; exit 1; }
echo "envfacts: wrote $OUT ($(wc -l < "$OUT") facts)" >&2
