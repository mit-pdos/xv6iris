# CI-parity targets: lints, generated-file checks and the report tools
# (included by the top-level Makefile; `make help` lists them).
#
# BLOCKING (non-zero exit on a real regression): lint, toolchain-check,
# check-gen, check-gen-kernel, coverage, test-tools.
# INFORMATIONAL (always exit 0, print a summary): profile, dead-code,
# dead-imports.
#
# Targets marked [lean] elaborate against the built tree: run them on the
# build machine / CI, never on the development machine
# (README: "Build").  The others are Python and shell only.

PYTHON    ?= python3
CI_OUT    ?= .lake/ci
FACTS     ?= $(CI_OUT)/envfacts.tsv
BUILD_LOG ?= $(CI_OUT)/lake-build.log
KERNEL    ?= xv6-riscv/kernel/kernel

.PHONY: lint toolchain-check check-gen check-gen-kernel test-tools timed-build envfacts \
        coverage coverage-baseline profile dead-code dead-imports reports

## lint: layering, no sorry/axiom/native_decide, module drift, toolchain pins (tools/ci/lint.sh)
lint:
	tools/ci/lint.sh

## toolchain-check: [lean] the lake on PATH and the fetched packages are the pinned ones
toolchain-check:
	tools/ci/toolchain_check.sh --with-lake

## check-gen: every generated file equals its generator's output (tools/check_gen.py)
check-gen:
	$(PYTHON) tools/check_gen.py

## check-gen-kernel: the same for the kernel dumps; needs the pinned ELF (KERNEL=path) and objdump
check-gen-kernel:
	$(PYTHON) tools/check_gen.py --only kernel --kernel $(KERNEL)

## test-tools: the unit tests of the Python tools (tools/tests/)
test-tools:
	$(PYTHON) -m unittest discover -s tools/tests

## timed-build: [lean] a CLEAN `lake build Xv6 MachCSL` with a timed log (BUILD_LOG=path)
timed-build:
	mkdir -p $(dir $(BUILD_LOG))
	tools/ci/timed_build.sh $(BUILD_LOG) --clean

## envfacts: [lean] dump the cone and the pc pins of the built tree to FACTS (tools/ci/envfacts.sh)
envfacts:
	tools/ci/envfacts.sh $(FACTS)

## coverage: proof coverage of the pinned images; fails below the floor (needs FACTS)
coverage:
	$(PYTHON) tools/proof_coverage.py --facts $(FACTS) --check

## coverage-baseline: rewrite the user-function floor from the current state (review the diff)
coverage-baseline:
	$(PYTHON) tools/proof_coverage.py --facts $(FACTS) --update-baseline > /dev/null

## profile: build profile from BUILD_LOG: wall, ΣCPU, critical path, slowest modules (informational)
profile:
	$(PYTHON) tools/proof_profile.py --build-log $(BUILD_LOG) --out-dir $(CI_OUT)/profile

## dead-code: declarations outside the cone of the top theorems, triaged (informational; needs FACTS)
dead-code:
	$(PYTHON) tools/find_dead.py --facts $(FACTS) --triage

## dead-imports: [lean] dead `import` lines of Xv6/ and MachCSL/ (informational; tools/ci/dead_imports.sh)
dead-imports:
	tools/ci/dead_imports.sh $(CI_OUT)/imports

## reports: [lean] envfacts + profile + coverage (blocking) + dead code, as CI runs them
reports:
	tools/ci/reports.sh $(wildcard $(BUILD_LOG))
