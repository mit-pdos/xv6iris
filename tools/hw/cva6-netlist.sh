#!/bin/bash
# cva6-netlist.sh -- CVA6's RTL as a HIERARCHICAL word-level Yosys netlist.
#
# The front end of the below-Sail effort (claude-notes/projects/hw-refinement.md
# section 7): read the pinned CVA6 core with yosys-slang, lower processes, keep
# memories word-level, and write the netlist as JSON WITHOUT flattening (owner
# ruling: the semantics is hierarchical), then summarise it.
#
# Runs on the build VM, not this host:
#     ./gcp-rocq/run-on-gcp tools/hw/cva6-netlist.sh
# Needs the YosysHQ OSS CAD Suite (yosys >= 0.67 with the slang plugin); set
# OSS_CAD to its root.  Everything else is fetched into $HW_WORK.
set -euo pipefail

CVA6_REV=${CVA6_REV:-81245a47f}          # openhwgroup/cva6, 2026-09-15
TARGET_CFG=${TARGET_CFG:-cv64a6_imafdc_sv39}
OSS_CAD=${OSS_CAD:-$HOME/hw/oss-cad-suite}
HW_WORK=${HW_WORK:-$HOME/hw/work}
HERE=$(cd "$(dirname "$0")" && pwd)

export PATH=$OSS_CAD/bin:$PATH
CVA6=$HW_WORK/cva6
export HPDCACHE_DIR=$CVA6/core/cache_subsystem/hpdcache  # read by hpdcache.Flist
mkdir -p "$HW_WORK/overrides"
cd "$HW_WORK"

if [ ! -d "$CVA6/.git" ]; then
  git clone -q https://github.com/openhwgroup/cva6.git "$CVA6"
fi
git -C "$CVA6" fetch -q origin
git -C "$CVA6" checkout -q "$CVA6_REV"
git -C "$CVA6" submodule update -q --init --recursive

# The cache SRAMs.  tc_sram_wrapper hides its behavioural tc_sram behind
# `synthesis translate_off` (a real tapeout substitutes a hard macro), so a
# synthesis read leaves every cache with an EMPTY wrapper and an undriven
# rdata_o -- and still reports success.  Use a copy without the two pragma
# lines.  (Not --no-default-translate-off-format: that would also switch on
# every simulation-only region in the design.)
grep -v "synthesis translate_o" "$CVA6/common/local/util/tc_sram_wrapper.sv" \
  > overrides/tc_sram_wrapper.sv
[ "$(wc -l < "$CVA6/common/local/util/tc_sram_wrapper.sv")" -eq \
  $(( $(wc -l < overrides/tc_sram_wrapper.sv) + 2 )) ] \
  || { echo "tc_sram_wrapper.sv changed shape; re-check the override" >&2; exit 1; }

# CVA6's own file list, expanded into a slang command file.
sed -e "s#\${CVA6_REPO_DIR}#$CVA6#g" \
    -e "s#\${TARGET_CFG}#$TARGET_CFG#g" \
    -e "s#\${HPDCACHE_DIR}#$HPDCACHE_DIR#g" \
    -e "s#^$CVA6/common/local/util/tc_sram_wrapper.sv\$#$HW_WORK/overrides/tc_sram_wrapper.sv#" \
    -e "s#^+incdir+#-I #" \
    "$CVA6/core/Flist.cva6" | grep -v '^\s*//' | grep -v '^\s*$' > cva6.f
grep -q "^$HW_WORK/overrides/tc_sram_wrapper.sv\$" cva6.f \
  || { echo "tc_sram_wrapper.sv not found in Flist.cva6" >&2; exit 1; }

# --keep-hierarchy: yosys-slang flattens during import by default.
# async2sync: CVA6's async active-low resets become synchronous cells, which
# is what a clocked semantics can state.
cat > cva6.ys <<EOF
read_slang -F cva6.f --top cva6 --keep-hierarchy \
  --ignore-assertions --ignore-initial --ignore-timing
hierarchy -top cva6
proc
opt_clean
memory -nomap
async2sync
tee -q -o cva6.stat stat
write_json cva6.json
EOF
yosys -m slang -q -l cva6.log cva6.ys
grep -E "Build succeeded" cva6.log
python3 "$HERE/netlist_summary.py" cva6.json cva6
