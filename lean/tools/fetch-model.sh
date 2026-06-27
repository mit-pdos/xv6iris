#!/usr/bin/env bash
# ======================================================================
# Pull in the upstream generated Sail RISC-V Lean model as a build step
# (instead of vendoring 172k lines into this repo) and patch it to build
# against the xv6iris *free-monad* fork of lean-sail (lean/vendor/lean-sail).
#
# Idempotent: re-running fast-forwards to the pinned commit and re-applies
# the (tiny) patches. Run this before `lake build` once; CI/fresh checkouts
# run it via `make model`.
#
# The patches are deliberately minimal — see lean/README.md and the memory
# note `lean-sail-free-monad-fork`:
#   1. toolchain  -> v4.31.0 (match iris-lean / this project)
#   2. lakefile   -> require Sail from ../../vendor/lean-sail (our fork)
#   3. one line in Specialization.lean: pin the ChoiceSource for `Mon.run`
# ======================================================================
set -euo pipefail

LEAN_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODEL_DIR="$LEAN_DIR/.model/sail-riscv-lean"
REPO="https://github.com/opencompl/sail-riscv-lean"
COMMIT="5175d438b076fdd5d1d0ae229ccdbe917cf67a3d"

mkdir -p "$LEAN_DIR/.model"
if [ ! -d "$MODEL_DIR/.git" ]; then
  git init -q "$MODEL_DIR"
  git -C "$MODEL_DIR" remote add origin "$REPO" 2>/dev/null || true
fi
if [ "$(git -C "$MODEL_DIR" rev-parse HEAD 2>/dev/null || echo none)" != "$COMMIT" ]; then
  echo "fetch-model: fetching $COMMIT"
  git -C "$MODEL_DIR" fetch --depth 1 origin "$COMMIT"
  git -C "$MODEL_DIR" checkout -q --force "$COMMIT"
  git -C "$MODEL_DIR" clean -qfdx -e .lake
fi

# --- patch 1: toolchain ---
echo "leanprover/lean4:v4.31.0" > "$MODEL_DIR/lean-toolchain"

# --- patch 2: require our forked lean-sail instead of upstream EStateM one ---
python3 - "$MODEL_DIR/lakefile.toml" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()
old = '''[[require]]
name = "Sail"
git = "https://github.com/rems-project/lean-sail"
rev = "v4"'''
new = '''[[require]]
name = "Sail"
path = "../../vendor/lean-sail"'''
if old in s:
    s = s.replace(old, new); open(p, 'w').write(s)
PY

# --- patch 3: free-monad Mon.run needs the ChoiceSource pinned ---
sed -i 's/match x.run default with/match x.run (c := trivialChoiceSource) default with/' \
  "$MODEL_DIR/LeanRV64D/Specialization.lean"

rm -f "$MODEL_DIR/lake-manifest.json"
echo "fetch-model: model ready at lean/.model/sail-riscv-lean ($COMMIT)"
