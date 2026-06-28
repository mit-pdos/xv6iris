# Build for the Lean (iris-lean) port. The upstream Sail RISC-V model is pulled
# in as a build step (tools/fetch-model.sh) rather than vendored, and patched to
# build against the free-monad fork of lean-sail in vendor/lean-sail.
#
#   make            == make build (fetch the model, then compile everything)
#   make model      fetch + patch the upstream model into .model/ (idempotent)
#   make build      make model, then `lake build`
#   make iris       build only the Iris layer (no model fetch needed)
#   make model-lib  compile the pulled-in model itself (~172k lines, slow)
#   make clean-model  remove the pulled-in model (.model/)

.PHONY: all build model iris model-lib clean-model

all: build

model:
	tools/fetch-model.sh

build: model
	lake build
	lake build Xv6Iris.Model

# The Iris development layer on its own (model resolved lazily; not compiled
# unless a file imports it).
iris:
	lake build Xv6Iris

# The real-machine layer: the Iris Language over the generated model's `try_step`
# (non-module; imports the model, so this triggers the model build).
real: model
	lake build Xv6Iris.Model

# Force-compile the pulled-in generated model (the heavy 172k-line build).
model-lib: model
	lake build Lean_RV64D

clean-model:
	rm -rf .model

# Verify the xv6 kernel's first two instructions on the real model (kernel
# reduction of try_step ×2; needs a large interpreter stack).
kernel-first-two: model
	lake env lean --tstack=16000000 Xv6Iris/KernelFirstTwo.lean

# The same result encoded as a weakest-precondition over the program logic
# (wp_kernel_first_two), built on wp_lift_step + the reg points-to bridges and the
# kernel-reduction step lemmas. Large interpreter stack as above.
kernel-wp: model
	lake build Xv6Iris.RealPtsto
	lake env lean --tstack=16000000 Xv6Iris/KernelWP.lean

# The whole _entry (_start) boot sequence (8 instructions, ending at jal start) as
# a WP over the program logic (wp_entry), via 8 per-instruction kernel-reduction
# step lemmas + the generalized wp_estep rule. Heavy (8 try_step reductions) —
# allow several minutes and a big stack.
kernel-entry: model
	lake build Xv6Iris.RealPtsto
	lake env lean --tstack=64000000 Xv6Iris/KernelEntry.lean

# The kernel's start() through mret (54 instructions incl. timerinit + the
# Machine->Supervisor transition to main): both operationally (start_to_main) and
# as a WP over the program logic (wp_start_to_main), the latter via the
# whole-machine-state engine in KernelMain (wp_run). Very heavy operational
# reduction (~55 try_steps) — several minutes, big stack.
kernel-start: model
	lake build Xv6Iris.KernelMain
	lake env lean --tstack=64000000 Xv6Iris/KernelStart.lean
