#!/usr/bin/env bash
# Regenerate model-xv6iris/{rv64d.v,rv64d_types.v} from a sail-riscv checkout,
# using this repo's SIG-disabled config (model-xv6iris/sail-config-rv64d.json).
# See root README.md "Regenerating the Sail model" for background.
#
# Usage:
#   tools/regen_sail_model.sh [SAIL_RISCV_DIR]
#
# SAIL_RISCV_DIR defaults to ../sail-riscv (sibling of this repo, matching the
# layout documented in README.md). Requires: sail 0.20.1 + sail_coq_backend
# (opam), cmake, coqc (only used for the compile-check at the end).
#
# What this does NOT do: touch sail-riscv's own config/config.json.in or its
# cmake cache. It configures/builds sail-riscv's cmake project as usual (so
# `generated_rocq_rv64d` and its dependencies exist), then invokes `sail`
# directly with our own --config so the SIG-disabled JSON overrides the
# upstream default, mirroring exactly what model/CMakeLists.txt's Rocq
# target does but for our config file instead of the auto-generated one.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SAIL_RISCV_DIR="${1:-$REPO_ROOT/../sail-riscv}"
CONFIG_JSON="$REPO_ROOT/model-xv6iris/sail-config-rv64d.json"
OUT_DIR="$REPO_ROOT/model-xv6iris"

if [ ! -d "$SAIL_RISCV_DIR" ]; then
  echo "error: sail-riscv checkout not found at $SAIL_RISCV_DIR" >&2
  echo "usage: $0 [SAIL_RISCV_DIR]" >&2
  exit 1
fi
if ! command -v sail >/dev/null 2>&1; then
  echo "error: 'sail' (0.20.1, with sail_coq_backend) not on PATH -- eval \$(opam env) first" >&2
  exit 1
fi

echo "== Configuring/building sail-riscv's cmake project (for its own module list + deps) =="
cmake -S "$SAIL_RISCV_DIR" -B "$SAIL_RISCV_DIR/build" \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo -DDOWNLOAD_GMP=FALSE

# SAIL_MODULES is the exact set of Sail modules this project's model is built
# from (a curated subset, not --all-modules -- see the cmake cache). Reuse it
# so our manual invocation matches what `generated_rocq_rv64d` would produce,
# module-for-module, with only the --config swapped out.
SAIL_MODULES="$(grep '^SAIL_MODULES:STRING=' "$SAIL_RISCV_DIR/build/CMakeCache.txt" | cut -d= -f2 | tr ';' ' ')"
if [ -z "$SAIL_MODULES" ]; then
  echo "error: could not read SAIL_MODULES from $SAIL_RISCV_DIR/build/CMakeCache.txt" >&2
  exit 1
fi
SAIL_REQUIRED_VER="$(grep -m1 'set(SAIL_REQUIRED_VER' "$SAIL_RISCV_DIR/CMakeLists.txt" | sed -E 's/.*SAIL_REQUIRED_VER ([0-9.]+).*/\1/')"

echo "== Running sail (--coq) with the SIG-disabled config =="
echo "   modules: $SAIL_MODULES"
TMP_OUT="$(mktemp -d)"
trap 'rm -rf "$TMP_OUT"' EXIT
(
  cd "$SAIL_RISCV_DIR/model"
  sail --strict-var --strict-bitvector --strict-exponentials \
    --require-version "$SAIL_REQUIRED_VER" \
    --memo-z3-path "$SAIL_RISCV_DIR/build/model/sail_smt_cache" \
    --dcoq-undef-axioms --coq --coq-lib riscv_extras \
    --coq-output-dir "$TMP_OUT" \
    -o rv64d \
    --config "$CONFIG_JSON" \
    $SAIL_MODULES \
    riscv.sail_project
)

echo "== Compile-checking the regenerated model =="
if command -v coqc >/dev/null 2>&1; then
  CHECK_DIR="$(mktemp -d)"
  trap 'rm -rf "$TMP_OUT" "$CHECK_DIR"' EXIT
  cp "$TMP_OUT/rv64d.v" "$TMP_OUT/rv64d_types.v" "$SAIL_RISCV_DIR/handwritten_support/riscv_extras.v" "$CHECK_DIR/"
  ( cd "$CHECK_DIR" && coqc -R . Riscv riscv_extras.v && coqc -R . Riscv rv64d_types.v && coqc -R . Riscv rv64d.v )
  echo "   OK: compiles clean under coqc"
else
  echo "   warning: coqc not found, skipping compile-check" >&2
fi

echo "== Installing into $OUT_DIR =="
cp "$TMP_OUT/rv64d.v" "$TMP_OUT/rv64d_types.v" "$OUT_DIR/"
cp "$SAIL_RISCV_DIR/handwritten_support/riscv_extras.v" "$OUT_DIR/"
echo "Done. Review the diff (rv64d.v is the only file expected to change vs."
echo "an upstream-default regen) and run 'make model' to rebuild."
