#!/usr/bin/env bash
# ======================================================================
# Regenerate model/Lean_RV64D/ (the Sail RISC-V model compiled to Lean)
# from a sail-riscv checkout, using this repo's own config and module list:
#
#   model/sail-config-rv64d.json   the resolved rv64d_v256_e64 config with
#                                  the xv6 deviations (same file as the Rocq
#                                  MachCSL prototype's model-xv6iris/)
#   model/sail-modules.txt         the module subset to compile
#
# The generated Lean project `require`s the vendored lean-sail fork
# (vendor/lean-sail), whose `PreSailM` is a free monad -- see its README.
#
# Usage:
#   tools/regen_sail_model.sh [SAIL_RISCV_DIR]
#
# SAIL_RISCV_DIR defaults to $SAIL_RISCV_DIR in the environment, else
# ./sail-riscv (gitignored; cloned here on demand).  The model is taken from
# the MachCSL fork zeldovich/sail-riscv (branch `xv6`) pinned at
# $SAIL_RISCV_REV; its deltas against riscv/sail-riscv upstream are the atomic
# PTE A/D-bit update and the AK_ifetch/AK_ttw tagging of fetches and
# page-table walks at the concurrency interface.
#
# Requires: `sail` with `sail_lean_backend` on PATH.  The opam switch that
# has them is `lean-xv6`: run as
#   opam exec --switch=lean-xv6 -- tools/regen_sail_model.sh
# ======================================================================
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

SAIL_RISCV_URL="${SAIL_RISCV_URL:-https://github.com/zeldovich/sail-riscv}"
SAIL_RISCV_REV="${SAIL_RISCV_REV:-070832a1e4b086f0c6f7635de54cc2b4cfd66993}"
SAIL_RISCV_DIR="${1:-${SAIL_RISCV_DIR:-$REPO_ROOT/sail-riscv}}"
case "$SAIL_RISCV_DIR" in /*) ;; *) SAIL_RISCV_DIR="$PWD/$SAIL_RISCV_DIR" ;; esac

CONFIG_JSON="$REPO_ROOT/model/sail-config-rv64d.json"
MODULES_FILE="$REPO_ROOT/model/sail-modules.txt"
OUT_DIR="$REPO_ROOT/model"
LEAN_SAIL_DIR="$REPO_ROOT/vendor/lean-sail"

if ! command -v sail >/dev/null 2>&1; then
  echo "error: 'sail' not on PATH -- run under 'opam exec --switch=lean-xv6 --'" >&2
  exit 1
fi

if [ ! -d "$SAIL_RISCV_DIR" ]; then
  echo "== Cloning $SAIL_RISCV_URL into $SAIL_RISCV_DIR =="
  git clone "$SAIL_RISCV_URL" "$SAIL_RISCV_DIR"
  git -C "$SAIL_RISCV_DIR" checkout --detach "$SAIL_RISCV_REV"
fi

have="$(git -C "$SAIL_RISCV_DIR" rev-parse HEAD 2>/dev/null || true)"
if [ "$have" != "$SAIL_RISCV_REV" ]; then
  echo "WARNING: $SAIL_RISCV_DIR is at $have, not the pinned $SAIL_RISCV_REV" >&2
fi

SAIL_MODULES="$(sed -e 's/#.*//' "$MODULES_FILE" | tr -s '[:space:]' ' ')"
if [ -f "$SAIL_RISCV_DIR/cmake/sail_required_version.txt" ]; then
  SAIL_REQUIRED_VER="$(tr -d '[:space:]' < "$SAIL_RISCV_DIR/cmake/sail_required_version.txt")"
else
  SAIL_REQUIRED_VER="0.20.2"
fi
SAIL_HAVE_VER="$(sail --version | sed -E 's/^Sail ([0-9.]+).*/\1/')"
if [ "$SAIL_REQUIRED_VER" != "$SAIL_HAVE_VER" ]; then
  echo "note: model asks for sail $SAIL_REQUIRED_VER, this is sail $SAIL_HAVE_VER;"
  echo "      generating with --require-version $SAIL_HAVE_VER."
  SAIL_REQUIRED_VER="$SAIL_HAVE_VER"
fi

echo "== Running sail (--lean) with $(basename "$CONFIG_JSON") =="
echo "   modules: $SAIL_MODULES"
TMP_OUT="$(mktemp -d)"
trap 'rm -rf "$TMP_OUT"' EXIT
mkdir -p "$SAIL_RISCV_DIR/build/model"
(
  cd "$SAIL_RISCV_DIR/model"
  # Flags mirror sail-riscv's model/CMakeLists.txt (`sail_common`,
  # `lean_sail_common`, `lean_sail_default`), plus --lean-lib-path so the
  # generated lakefile requires our vendored lean-sail.
  sail --strict-var --strict-bitvector --strict-exponentials \
    --require-version "$SAIL_REQUIRED_VER" \
    --memo-z3 --memo-z3-path "$SAIL_RISCV_DIR/build/model/sail_smt_cache" \
    --config "$CONFIG_JSON" \
    --lean \
    --lean-output-dir "$TMP_OUT" \
    --lean-force-output \
    --lean-non-beq-type instruction \
    --lean-non-beq-type ExecutionResult \
    --lean-non-beq-type Step \
    --lean-noncomputable \
    --lean-noncomputable-function encdec_forwards \
    --lean-noncomputable-function encdec_backwards \
    --lean-noncomputable-function encdec_forwards_matches \
    --lean-noncomputable-function encdec_backwards_matches \
    --lean-noncomputable-function encdec_compressed_forwards \
    --lean-noncomputable-function encdec_compressed_backwards \
    --lean-noncomputable-function encdec_compressed_forwards_matches \
    --lean-noncomputable-function encdec_compressed_backwards_matches \
    --lean-import-file ../handwritten_support/RiscvExtras.lean \
    --lean-lib-path "$LEAN_SAIL_DIR" \
    -o Lean_RV64D \
    $SAIL_MODULES \
    riscv.sail_project
)

echo "== Installing into $OUT_DIR/Lean_RV64D =="
rm -rf "$OUT_DIR/Lean_RV64D"
cp -r "$TMP_OUT/Lean_RV64D" "$OUT_DIR/Lean_RV64D"
# pin the generated project to this repo's toolchain and lean-sail (relative path)
cp "$REPO_ROOT/lean-toolchain" "$OUT_DIR/Lean_RV64D/lean-toolchain"
sed -i "s|path = \"$LEAN_SAIL_DIR\"|path = \"../../vendor/lean-sail\"|" "$OUT_DIR/Lean_RV64D/lakefile.toml"
rm -f "$OUT_DIR/Lean_RV64D/lake-manifest.json"
# Two source-compat patches on the copied-in support files:
#  1. the fork's handwritten RiscvExtras.lean predates Sail dropping the
#     `Defs` namespace from the generated model;
#  2. Sail's SpecializationV1.lean types the memory/barrier primitives
#     polymorphically (any `pa_size ts arch`), but our free-monad `Outcome`
#     fixes them at the Arch instance's types (the only ones a model can
#     instantiate them at), so the abbrevs are pinned to match.
sed -i 's/^open LeanRV64D\.Defs$/open LeanRV64D/' "$OUT_DIR/Lean_RV64D/LeanRV64D/RiscvExtras.lean"
sed -i \
  -e 's/(req : Mem_write_request n vasize (BitVec pa_size) ts arch)/(req : Mem_write_request n vasize Arch.pa Arch.translation Arch.arch_ak)/' \
  -e 's/(req : Mem_read_request n vasize (BitVec pa_size) ts arch)/(req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)/' \
  -e 's/abbrev sail_barrier (a : α) : SailM Unit/abbrev sail_barrier (a : Arch.barrier) : SailM Unit/' \
  -e 's/ \[Arch\]//g' \
  "$OUT_DIR/Lean_RV64D/LeanRV64D/SpecializationV1.lean"
#  3. WORKAROUND for a Lean 4.32 do-notation performance bug: a run of
#     non-final `(pure (f ...))` statements elaborates in time exponential in
#     the run length (18 of them in `print_rvfi_exec` never finish).  Spelling
#     them `discard <| pure (...)` is semantically identical and linear.
sed -i 's/(pure (print_/(discard <| pure (print_/g' "$OUT_DIR"/Lean_RV64D/LeanRV64D/*.lean
#  4. CONSTANT-FOLD the xlen-dependent widths: the backend prints the Sail
#     type `bits(if xlen == 32 then 34 else 64)` as `BitVec (if (64 = 32 : Bool)
#     then 34 else 64)`, an unreduced `ite` in a TYPE that makes `simp` stumble
#     over ill-typed intermediate terms.  xlen is 64 in this configuration.
sed -i -e 's/(if ( 64 = 32  : Bool) then 34 else 64)/64/g' \
       -e 's/(if ( 64 = 32  : Bool) then 9 else 16)/16/g' "$OUT_DIR"/Lean_RV64D/LeanRV64D/*.lean
#  5. `unwrapValue` (pure extraction of a config constant) ran the EStateM;
#     on the free monad a value is pure exactly when the tree is a leaf.
python3 - "$OUT_DIR/Lean_RV64D/LeanRV64D/SpecializationV1.lean" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()
old = """  match x.run default with
  | .ok x _ => x
  | _ => default"""
new = """  match x with
  | .pure x => x
  | _ => default"""
assert old in s, "unwrapValue shape changed; update tools/regen_sail_model.sh"
open(p, 'w').write(s.replace(old, new))
PY
echo "Done.  Review 'git diff model/' and rebuild with 'lake build'."
