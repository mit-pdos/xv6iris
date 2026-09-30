#!/usr/bin/env bash
# tools/ci/envfacts.sh [OUT]   -- dump the environment facts the report tools read.
#
# Runs tools/ci/EnvFacts.lean against the BUILT tree (it imports Xv6 and
# MachCSL, so `lake build Xv6 MachCSL` must have succeeded; nothing is
# rebuilt here beyond what lake finds stale).  OUT defaults to
# .lake/ci/envfacts.tsv.  Consumers: tools/proof_coverage.py (coverage) and
# tools/find_dead.py (dead code).  ~1-2 min, one core, ~20 GB.
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
OUT=${1:-.lake/ci/envfacts.tsv}
mkdir -p "$(dirname "$OUT")"
rm -f "$OUT"
XV6_ENVFACTS_OUT="$OUT" lake env lean tools/ci/EnvFacts.lean
test -s "$OUT" || { echo "envfacts: $OUT was not written" >&2; exit 1; }
echo "envfacts: wrote $OUT ($(wc -l < "$OUT") facts)" >&2
