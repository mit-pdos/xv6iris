# The whole CI sequence as make targets (included by the top-level Makefile).
# tools/ci/run_all.sh is the entry point .github/workflows/lean-ci.yml calls, one
# step at a time; its header lists the steps.

.PHONY: ci ci-steps

## ci: [lean] every CI step in order, as .github/workflows/lean-ci.yml runs them (tools/ci/run_all.sh)
ci:
	tools/ci/run_all.sh

## ci-steps: the names of the CI steps; run one with `tools/ci/run_all.sh STEP`
ci-steps:
	@tools/ci/run_all.sh --list
