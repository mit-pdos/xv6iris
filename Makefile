# Top-level entry points for everything that is not `lake build`.
#
#   make help        list the targets
#
# The targets live in tools/ci/*.mk, one file per area, each target with a
# `## name: what it does` line above it (that line is what `make help`
# prints).  The proofs themselves are built by lake:
#
#   lake build Xv6 MachCSL
#
# Targets marked [lean] need a machine sized for a Lean build (README:
# "Build"), e.g. a build server or CI.

.DEFAULT_GOAL := help

include $(wildcard tools/ci/*.mk)

.PHONY: help
help:
	@grep -hE '^## [a-z-]+: ' $(MAKEFILE_LIST) | sed -E 's/^## ([a-z-]+): (.*)/\1\t\2/' | awk -F'\t' '{printf "  %-18s %s\n", $$1, $$2}'
