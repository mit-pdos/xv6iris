# Device conformance (vtest-lean/): the machine model re-checked against
# behaviours captured from QEMU, the VisionFive 2 board and the CVA6 RTL.
# Included by the top-level Makefile; the targets are tools/ci/vtest.sh's
# commands under the names the Rocq tree's Makefile gives them.  See
# tools/vtest/README.md.
#
# NOT part of the proof build: a red run is a finding about the model and
# must not break `lake build Xv6 MachCSL`.  The suite needs only the cone of
# MachCSL.Lang (the model and the device language).
#
# Targets marked [lean] are for a build machine and CI (README: "Build");
# vtest-gen and vtest-table are Python only.

.PHONY: vtest vtest-check vtest-check-ci vtest-passes vtest-table vtest-explain vtest-gen vtest-runs

## vtest-check: [lean] check the model against the CHECKED-IN captures (the green set); lake's own status
vtest-check:
	tools/ci/vtest.sh check

## vtest-check-ci: [lean] the same, rebuilding every run's proof and keeping going; the run table is the verdict (what CI runs)
vtest-check-ci:
	tools/ci/vtest.sh check-ci

## vtest-passes: [lean] ATTEMPT every run's proof, classify (agree/stuck), rewrite the green set, print the table
vtest-passes:
	tools/ci/vtest.sh passes

## vtest-table: THE TABLE: every case, its run on each platform, whether that run has a passing proof
vtest-table:
	tools/ci/vtest.sh table

## vtest-explain: [lean] say why every red run is red (RUNS="QEMU/DiskRw ..." for some)
vtest-explain:
	tools/ci/vtest.sh explain $(if $(RUNS),$(RUNS),--all)

## vtest-gen: RE-RUN QEMU and rewrite the QEMU captures (needs qemu-system-riscv64 + the riscv64 toolchain; never CI)
vtest-gen:
	tools/ci/vtest.sh gen --all

## vtest-runs: re-render every checked-in capture and proof in the current shape (no QEMU)
vtest-runs:
	tools/ci/vtest.sh runs

## vtest: [lean] vtest-gen, then vtest-check
vtest: vtest-gen vtest-check
