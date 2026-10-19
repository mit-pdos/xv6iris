#!/usr/bin/env bash
# ======================================================================
# Regenerate model/Lean_RV64D/ (the Sail RISC-V model compiled to Lean)
# from a sail-riscv checkout, using this repo's own config and module list:
#
#   model/sail-config-rv64d.json   the resolved rv64d_v256_e64 config with
#                                  the xv6 deviations (its header lists them)
#   model/sail-modules.txt         the module subset to compile
#   model/Xv6Extras.lean           HAND-WRITTEN realisations of the Sail
#                                  platform hooks (LR/SC reservation,
#                                  plat_term_write, experimental extensions);
#                                  passed as a second --lean-import-file, NOT
#                                  regenerated (Rocq: xv6iris_extras.v)
#
# The generated Lean project `require`s lean-sail by git at $LEAN_SAIL_REV
# (upstream's `Sail.ArchSem.PreSailM` is the free monad over
# `InstructionEffect` that MachCSL steps; the root lakefile.toml pins the
# SAME revision -- tools/ci/toolchain_check.sh checks that they agree).
#
# Usage:
#   tools/regen_sail_model.sh [SAIL_RISCV_DIR]
#
# SAIL_RISCV_DIR defaults to $SAIL_RISCV_DIR in the environment, else
# ./sail-riscv (gitignored; cloned here on demand).  The model is taken from
# the fork dongjaelee1/sail-riscv (branch `xv6`) pinned at $SAIL_RISCV_REV:
# upstream riscv/sail-riscv release 0.16 (e5acebb0) plus six commits (each
# with its kind and reason in notes/model-diffs.md section 1) --
# the atomic PTE A/D-bit update (upstream PR #1860); the external-interrupt
# pin registers consulted without the Simple Interrupt Generator (so
# MachCSL's PLIC device can drive sig_meip/sig_seip with the SIG's MMIO
# window, which collides with the PLIC's, switched off); and two Lean-target
# repairs of code added by upstream #2018 -- a width-monomorphic Sdtrig
# `MemoryTriggerPayload` (its existential union does not elaborate in Lean;
# Sdtrig is disabled by our config, and trigger matching is unchanged) and
# the AMO's result tested by pattern instead of `==` on `ExecutionResult`
# (which the backend gives no equality); the F/D instructions kept out of
# `postlude`'s dependencies (0.16 pulls them in for H's transformed FP
# loads/stores; they were not in the model before the bump, and their
# softfloat externs must stay outside every audited cone); and `hideleg`
# ignored when H is not enabled, as `mideleg` is without S (a bug fix).
#
# Requires on PATH: `sail` with `sail_lean_backend` built from the fork
# dongjaelee1/sail, branch `xv6` (merge b49c997e), = rems-project/sail `sail2`
# (its development branch) $SAIL_REV with four Lean-backend fixes on top: the escaping of the Lean
# command keywords `prefix`, `infix`, `notation`, ... in identifiers (ours;
# sail-riscv's DeviceTree has a parameter named `prefix`), `termination_by`
# only on a definition that calls itself (ours; Lean warns about the measure
# of a non-recursive one, and the specialised copies of the two-stage page
# walk have one), and two still-unmerged fixes from github.com/zeldovich/sail:
#   3c03fced  "Lean: make boolean & and | short-circuit with effectful
#             operands" (upstream PR #1750; without it the backend hoists an
#             effectful right operand of `&`/`|` out of the condition and
#             ALWAYS runs it, e.g. `check_CSR` reaches an `assert false` on a
#             user access to mseccfg; Sail and Rocq short-circuit, and the
#             proofs assume the short-circuit form)
#   4b46310d  "Lean: parenthesise non-atomic operands in type-level
#             arithmetic" (upstream PR #1774; without it `flen` prints as
#             `if true then 8 else 4 * 8`, i.e. 8)
# and `z3` (the Sail type checker calls it).  Build sail from a clone of that
# branch with opam and dune (`opam install --deps-only .`, `dune build
# --release`, `dune install --release --prefix <dir>`).  In the agent
# container both live under /work/toolchain (user space, no root):
#   export PATH=/work/toolchain/sail-v2/bin:/work/toolchain/bin:$PATH
# `sail --version` then prints "Sail 0.20.3 (xv6 @ …)".  Once an upstream Sail
# release contains the fixes, build that release instead and drop this
# paragraph.
# ======================================================================
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

SAIL_RISCV_URL="${SAIL_RISCV_URL:-https://github.com/dongjaelee1/sail-riscv}"
SAIL_RISCV_REV="${SAIL_RISCV_REV:-f0ef9813bf93f91907a08c0f475fd2434cb42dcb}"
SAIL_RISCV_DIR="${1:-${SAIL_RISCV_DIR:-$REPO_ROOT/sail-riscv}}"
case "$SAIL_RISCV_DIR" in /*) ;; *) SAIL_RISCV_DIR="$PWD/$SAIL_RISCV_DIR" ;; esac
# the Sail compiler this model was generated with: upstream `sail2` $SAIL_REV; the built branch is
# dongjaelee1/sail `xv6` = that + the four fixes, merge $SAIL_XV6_REV, which `sail --version` names
# ("Sail 0.20.3 (xv6 @ <merge>)") and this script requires (notes/model-policy.md, section 6)
SAIL_REV="e49821011450d2c26dad90e8806fc82d9698b627"
SAIL_XV6_REV="b49c997e91215c561f928d01f5bdadc0b8f406af"
# lean-sail: the revision the generated lakefile requires (= the root lakefile.toml's)
LEAN_SAIL_GIT="https://github.com/rems-project/lean-sail"
LEAN_SAIL_REV="${LEAN_SAIL_REV:-01bb54c7c8a69e52ba11863c67e7c403a6cd198a}"   # tag v7

CONFIG_JSON="$REPO_ROOT/model/sail-config-rv64d.json"
MODULES_FILE="$REPO_ROOT/model/sail-modules.txt"
OUT_DIR="$REPO_ROOT/model"
# HAND-WRITTEN, not regenerated: the realisations of the Sail platform hooks
# (the Lean twin of Rocq's model-xv6iris/xv6iris_extras.v; see its header).
# Passed as a SECOND --lean-import-file, so sail copies it into the generated
# project as LeanRV64D/Xv6Extras.lean and every generated module imports it;
# its definitions (in LeanRV64D.Functions) take precedence over the fork's
# root-level axioms of the same names in RiscvExtras.lean.
XV6_EXTRAS="$REPO_ROOT/model/Xv6Extras.lean"

if ! command -v sail >/dev/null 2>&1; then
  echo "error: 'sail' not on PATH -- see this script's header" >&2
  exit 1
fi
if ! command -v z3 >/dev/null 2>&1; then
  echo "error: 'z3' not on PATH (the Sail type checker needs it)" >&2
  exit 1
fi

if [ ! -d "$SAIL_RISCV_DIR" ]; then
  echo "== Cloning $SAIL_RISCV_URL into $SAIL_RISCV_DIR =="
  git clone "$SAIL_RISCV_URL" "$SAIL_RISCV_DIR"
  git -C "$SAIL_RISCV_DIR" checkout --detach "$SAIL_RISCV_REV"
fi

have="$(git -C "$SAIL_RISCV_DIR" rev-parse HEAD 2>/dev/null || true)"
if [ "$have" != "$SAIL_RISCV_REV" ]; then
  echo "error: $SAIL_RISCV_DIR is at $have, not the pinned $SAIL_RISCV_REV" >&2
  echo "       (REGEN_ALLOW_UNPINNED=1 makes this a warning, for an experiment whose output is never committed)" >&2
  [ "${REGEN_ALLOW_UNPINNED:-}" = 1 ] || exit 1
fi
if ! grep -q '^\$define CONCURRENCY_INTERFACE_V2' "$SAIL_RISCV_DIR/model/core/phys_mem_interface.sail"; then
  echo "error: $SAIL_RISCV_DIR does not use concurrency interface v2; this script is for sail-riscv >= 0.15" >&2
  exit 1
fi

SAIL_MODULES="$(sed -e 's/#.*//' "$MODULES_FILE" | tr -s '[:space:]' ' ')"
if [ -f "$SAIL_RISCV_DIR/cmake/sail_required_version.txt" ]; then
  SAIL_REQUIRED_VER="$(tr -d '[:space:]' < "$SAIL_RISCV_DIR/cmake/sail_required_version.txt")"
else
  SAIL_REQUIRED_VER="0.20.3"
fi
SAIL_HAVE_VER="$(sail --version | sed -E 's/^Sail ([0-9.]+).*/\1/')"
if ! sail --version | grep -q "(xv6 @ $SAIL_XV6_REV)"; then
  echo "error: '$(sail --version)' is not the pinned compiler (xv6 @ $SAIL_XV6_REV); see this script's header" >&2
  echo "       (REGEN_ALLOW_UNPINNED=1 makes this a warning, for an experiment whose output is never committed)" >&2
  [ "${REGEN_ALLOW_UNPINNED:-}" = 1 ] || exit 1
fi
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
  # `lean_sail_common`, `lean_sail_default`), plus the lean-sail pin.
  sail --strict-var --strict-bitvector --strict-exponentials \
    --require-version "$SAIL_REQUIRED_VER" \
    --memo-z3 --memo-z3-path "$SAIL_RISCV_DIR/build/model/sail_smt_cache" \
    --config "$CONFIG_JSON" \
    --lean \
    --lean-output-dir "$TMP_OUT" \
    --lean-force-output \
    --lean-non-beq-type instruction \
    --lean-non-beq-type instr_info \
    --lean-non-beq-type HartState \
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
    --lean-import-file "$XV6_EXTRAS" \
    --lean-lib-repo "$LEAN_SAIL_GIT" \
    --lean-lib-rev "$LEAN_SAIL_REV" \
    -o Lean_RV64D \
    $SAIL_MODULES \
    riscv.sail_project
)

echo "== Installing into $OUT_DIR/Lean_RV64D =="
rm -rf "$OUT_DIR/Lean_RV64D"
cp -r "$TMP_OUT/Lean_RV64D" "$OUT_DIR/Lean_RV64D"
# pin the generated project to this repo's toolchain (the backend writes its own Lean version)
cp "$REPO_ROOT/lean-toolchain" "$OUT_DIR/Lean_RV64D/lean-toolchain"
rm -f "$OUT_DIR/Lean_RV64D/lake-manifest.json"
grep -q "rev = \"$LEAN_SAIL_REV\"" "$OUT_DIR/Lean_RV64D/lakefile.toml" || {
  echo "error: the generated lakefile does not require lean-sail at $LEAN_SAIL_REV" >&2; exit 1; }
# The interface must be v2: the backend copies in SpecializationArchSem.lean for it.
[ -f "$OUT_DIR/Lean_RV64D/LeanRV64D/SpecializationArchSem.lean" ] || {
  echo "error: no SpecializationArchSem.lean -- the backend did not generate the v2 interface" >&2; exit 1; }
if [ -f "$OUT_DIR/Lean_RV64D/LeanRV64D/SpecializationV1.lean" ]; then
  echo "error: SpecializationV1.lean generated -- the model is on the V1 interface" >&2; exit 1
fi

# Source-compat patches on the generated files.  Each is CONDITIONAL and
# reports what it did, so a patch that becomes unnecessary (or necessary
# again) after a Sail bump is visible in the regen log.  The pre-0.16 list
# had six; four of them (the `Defs` namespace, the V1 specialization
# abbrevs, `unwrapValue`, `assert`) are upstream now.
#  A. WORKAROUND for a Lean do-notation performance bug (seen with 4.32): a
#     run of non-final `(pure (f ...))` statements elaborates in time
#     exponential in the run length.  `discard <| pure (...)` is
#     semantically identical and linear.
#     (`grep -l` exits 1 when nothing matches; under `pipefail` that must not abort the script.)
n=$( (grep -l '(pure (print_' "$OUT_DIR"/Lean_RV64D/LeanRV64D/*.lean 2>/dev/null || true) | wc -l)
if [ "$n" -gt 0 ]; then
  sed -i 's/(pure (print_/(discard <| pure (print_/g' "$OUT_DIR"/Lean_RV64D/LeanRV64D/*.lean
  echo "patch A: '(pure (print_' -> 'discard <| pure' in $n file(s)"
else echo "patch A: not needed"; fi
#  B. CONSTANT-FOLD the xlen-dependent widths: the backend prints the Sail
#     type `bits(if xlen == 32 then 34 else 64)` as `BitVec (if (64 = 32 :
#     Bool) then 34 else 64)`, an unreduced `ite` in a TYPE that makes `simp`
#     stumble over ill-typed intermediate terms.  xlen is 64 here.
n=$( (grep -l 'if ( 64 = 32  : Bool) then' "$OUT_DIR"/Lean_RV64D/LeanRV64D/*.lean 2>/dev/null || true) | wc -l)
if [ "$n" -gt 0 ]; then
  sed -i -e 's/(if ( 64 = 32  : Bool) then 34 else 64)/64/g' \
         -e 's/(if ( 64 = 32  : Bool) then 9 else 16)/16/g' \
         -e 's/(if ( 64 = 32  : Bool) then 22 else 44)/44/g' \
         -e 's/(if ( 64 = 32  : Bool) then 7 else 14)/14/g' \
         -e 's/(if ( 64 = 32  : Bool) then 2 else 3)/3/g' "$OUT_DIR"/Lean_RV64D/LeanRV64D/*.lean
  left=$( (grep -c 'if ( 64 = 32  : Bool) then' "$OUT_DIR"/Lean_RV64D/LeanRV64D/*.lean || true) | awk -F: '{s+=$2} END{print s+0}')
  echo "patch B: xlen ites folded in $n file(s); $left other xlen ite(s) left (add their shapes here if a proof trips on one)"
else echo "patch B: not needed"; fi
#  C. Lean 4.34 made `assert` a do-element of the intrinsic-verification
#     syntax; Sail `sail2` emits `sail_assert`, so nothing should match.
n=$( (grep -lE '^\s*assert |(then|else|=>) assert ' "$OUT_DIR"/Lean_RV64D/LeanRV64D/*.lean 2>/dev/null || true) | wc -l)
if [ "$n" -gt 0 ]; then
  echo "WARNING: $n generated file(s) still use bare 'assert' (expected 'sail_assert' from Sail >= 7e0e53d1); re-add the parenthesising patch" >&2
else echo "patch C: not needed (sail_assert)"; fi

# The installed copy of Xv6Extras.lean must be the master copy verbatim
# (sail only substitutes THE_MODULE_NAME, which the master does not use).
cmp -s "$XV6_EXTRAS" "$OUT_DIR/Lean_RV64D/LeanRV64D/Xv6Extras.lean" || {
  echo "error: installed Xv6Extras.lean differs from $XV6_EXTRAS" >&2; exit 1; }
echo "Done.  Review 'git diff --stat model/', then: lake update Sail Lean_RV64D (once, after a pin change;"
echo "a pin change is a dependency bump, which needs the owner's approval)"
echo "and build EVERY generated module -- \`lake build LeanRV64D\` covers only the root's import closure,"
echo "which omits Step, InstsEnd, DecodeExt, DeviceTree, ...:"
echo "  lake build \$(cd model/Lean_RV64D && ls LeanRV64D/*.lean | sed -e 's/\\.lean\$//' -e 's|/|.|g')"
