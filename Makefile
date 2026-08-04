# ======================================================================
# Top-level build for the xv6-on-Sail RISC-V Rocq/Iris development.
#
#   make            build everything needed for the proofs (== make proofs)
#   make proofs     compile the Iris proofs (iris/) + their dependencies
#   make model      compile the Sail-generated Coq model (model-xv6iris/)
#   make kernel     build the xv6 kernel ELF (xv6-riscv/kernel/kernel)
#   make user       build the xv6 user-space programs (xv6-riscv/user/_*)
#   make xv6-rev-check  warn if xv6-riscv/ is not at the pinned $(XV6_REV)
#   make dump       (re)generate kernel-rocq/*.v + user-rocq/*.v, then compile
#   make kernel-rocq  compile kernel-rocq/ (regenerating its .v if the ELF changed)
#   make user-rocq  compile user-rocq/ (the dumped user programs, e.g. _sync)
#   make dump-force force a re-dump of every image, even if the ELF is unchanged
#   make clean      remove Coq build artifacts (.vo/.glob/CoqMakefile)
#   make distclean  also `make clean` the xv6 tree
#
# Every Rocq command runs inside the project-local opam switch ($(SWITCH));
# you do NOT need to `eval $(opam env ...)` first.  Override on the command
# line if needed, e.g.  make OBJDUMP=riscv64-unknown-elf-objdump
#
# NOTE: regenerating the Coq model from the Sail sources needs the `sail`
# compiler (not required for a normal build -- the model .v are checked in).
# See README.md > "Build" > "Regenerating the Sail model".
# ======================================================================

SWITCH  ?= /shared/xv6rocq
RUN     := opam exec --switch=$(SWITCH) --
PYTHON  ?= python3
OBJDUMP ?= riscv64-linux-gnu-objdump
SAIL_RISCV_DIR ?=

# Parallel compilation: each Coq sub-make (coq_makefile) is run with -j$(JOBS).
# coq_makefile computes the dependency order, so independent files (e.g. the
# WpAdd/WpAuipc/WpLoad/WpFetch siblings) compile concurrently.  Override with
# e.g.  make JOBS=4 proofs   (JOBS=1 forces a serial build).
JOBS ?= $(shell nproc 2>/dev/null || echo 4)

MODEL := model-xv6iris
KDUMP := kernel-rocq
UDUMP := user-rocq
IRIS  := iris

DUMPER     := tools/dump_elf.py
XV6_DIR    := xv6-riscv
XV6_URL    ?= https://github.com/mit-pdos/xv6-riscv
KERNEL_ELF := $(XV6_DIR)/kernel/kernel
USER_DIR   := $(XV6_DIR)/user

# THE xv6 revision this development is proved against.  $(XV6_DIR) is
# .gitignored, so this is the only record of which upstream commit the tracked
# kernel-rocq/*.v came from -- building any other revision moves symbol
# addresses out from under every proof that names one (a few commits either
# way already move most of them).  Verified: a kernel built here reproduces
# kernel-rocq/*.v byte for byte and symbol for symbol.
XV6_REV ?= 59db7e2ea922cb1cf18e328b5b80f5264b0f755b

KDUMP_SRCS := $(KDUMP)/KernelInstrs.v $(KDUMP)/KernelData.v $(KDUMP)/KernelSyms.v

# User-space programs to dump into user-rocq/, as <xv6 program>:<Rocq module
# prefix> pairs (the ELF is $(USER_DIR)/_<program>).  Adding one here also needs
# its three .v listed in user-rocq/_CoqProject.
USER_DUMPS ?= sync:Sync

.PHONY: all proofs model kernel user dump dump-force kernel-rocq user-rocq \
        xv6-rev-check clean clean-proofs distclean model-gen

all: proofs

# ---- 1. Sail-generated Coq model (rv64d_types, riscv_extras, rv64d) ----
$(MODEL)/CoqMakefile: $(MODEL)/_CoqProject
	cd $(MODEL) && $(RUN) coq_makefile -f _CoqProject -o CoqMakefile
model: $(MODEL)/CoqMakefile
	$(RUN) $(MAKE) -C $(MODEL) -f CoqMakefile -j$(JOBS)

# ---- 2. xv6 sources, pinned at $(XV6_REV) ----
# Detached: the checkout is a build input pinned by this Makefile, not a branch
# to develop on.  An existing $(XV6_DIR) is left alone (see xv6-rev-check).
$(XV6_DIR):
	git clone $(XV6_URL) $@
	git -C $@ checkout --detach $(XV6_REV)

# Warn when the checkout is not the revision the tracked dumps came from.
xv6-rev-check: | $(XV6_DIR)
	@have=`git -C $(XV6_DIR) rev-parse HEAD 2>/dev/null`; \
	 want=`git -C $(XV6_DIR) rev-parse $(XV6_REV) 2>/dev/null`; \
	 if [ -z "$$want" ]; then \
	   echo "WARNING: $(XV6_DIR) does not have XV6_REV=$(XV6_REV); try 'git -C $(XV6_DIR) fetch'."; \
	 elif [ "$$have" != "$$want" ]; then \
	   echo "WARNING: $(XV6_DIR) is at $$have,"; \
	   echo "         not the pinned XV6_REV=$$want."; \
	   echo "         Images built here will NOT match the tracked kernel-rocq/*.v:"; \
	   echo "         symbol addresses move, and every proof naming one breaks."; \
	   echo "         Fix with: git -C $(XV6_DIR) checkout --detach $(XV6_REV)"; \
	 fi

# ---- 2a. the kernel ELF (disassembled into Rocq by the dumper) ----
kernel: $(KERNEL_ELF)
$(KERNEL_ELF): | $(XV6_DIR)
	$(MAKE) -C $(XV6_DIR) kernel/kernel

# ---- 2b. xv6 user-space programs (user/_sync & friends; built by fs.img) ----
user: $(USER_DIR)/_sh
$(USER_DIR)/_%: | $(XV6_DIR)
	$(MAKE) -C $(XV6_DIR) fs.img

# ---- 3. Dump the ELF images into Rocq and compile them ----
#
# The generated .v are checked in but the ELFs are not ($(XV6_DIR) is
# .gitignored), so what keeps a dump honest is $(XV6_REV), not the build graph:
# an image built from another revision moves every symbol address and
# invalidates the proofs that name them.  Re-dumps themselves are cheap and
# safe: the dumper leaves an output (and its mtime) untouched when the content
# is unchanged, so a dumper edit that changes no output rebuilds nothing.
$(KDUMP)/KernelInstrs.v: $(KERNEL_ELF) $(DUMPER)
	$(PYTHON) $(DUMPER) --format rocq      --elf $< --objdump $(OBJDUMP) --out $@
$(KDUMP)/KernelData.v:   $(KERNEL_ELF) $(DUMPER)
	$(PYTHON) $(DUMPER) --format rocq-data --elf $< --objdump $(OBJDUMP) --out $@
$(KDUMP)/KernelSyms.v:   $(KERNEL_ELF) $(DUMPER)
	$(PYTHON) $(DUMPER) --format rocq-syms --elf $< --objdump $(OBJDUMP) --out $@
$(KDUMP)/CoqMakefile: $(KDUMP)/_CoqProject
	cd $(KDUMP) && $(RUN) coq_makefile -f _CoqProject -o CoqMakefile
kernel-rocq: $(KDUMP_SRCS) $(KDUMP)/CoqMakefile
	$(RUN) $(MAKE) -C $(KDUMP) -f CoqMakefile -j$(JOBS)

# One dump per user program.  $(1) = xv6 program name, $(2) = Rocq module prefix
# (so `sync:Sync` gives user-rocq/Sync{Instrs,Data,Syms}.v with names sync_bytes,
# sync_data, syncEntry, ... — distinct from the kernel's, so a proof can Require
# both the kernel image and the program it runs).
define user_dump_rules
$(UDUMP)/$(2)Instrs.v: $(USER_DIR)/_$(1) $$(DUMPER)
	$$(PYTHON) $$(DUMPER) --format rocq      --elf $$< --prefix $(1) --objdump $$(OBJDUMP) --out $$@
$(UDUMP)/$(2)Data.v:   $(USER_DIR)/_$(1) $$(DUMPER)
	$$(PYTHON) $$(DUMPER) --format rocq-data --elf $$< --prefix $(1) --objdump $$(OBJDUMP) --out $$@
$(UDUMP)/$(2)Syms.v:   $(USER_DIR)/_$(1) $$(DUMPER)
	$$(PYTHON) $$(DUMPER) --format rocq-syms --elf $$< --prefix $(1) --objdump $$(OBJDUMP) --out $$@
UDUMP_SRCS += $(UDUMP)/$(2)Instrs.v $(UDUMP)/$(2)Data.v $(UDUMP)/$(2)Syms.v
endef
$(foreach d,$(USER_DUMPS),\
  $(eval $(call user_dump_rules,$(word 1,$(subst :, ,$(d))),$(word 2,$(subst :, ,$(d))))))

$(UDUMP)/CoqMakefile: $(UDUMP)/_CoqProject
	cd $(UDUMP) && $(RUN) coq_makefile -f _CoqProject -o CoqMakefile
user-rocq: $(UDUMP_SRCS) $(UDUMP)/CoqMakefile
	$(RUN) $(MAKE) -C $(UDUMP) -f CoqMakefile -j$(JOBS)

dump: kernel-rocq user-rocq

# Re-dump every image from the ELFs currently in xv6-riscv/, even if make
# thinks the .v are up to date.  Check `git diff kernel-rocq/` afterwards: a
# changed symbol address means the proofs must be replayed against the new one.
# (Removing the outputs, rather than `make -B`, because -B would also force a
# rebuild of the ELFs themselves -- exactly the drift this guards against.)
dump-force: xv6-rev-check
	rm -f $(KDUMP_SRCS) $(UDUMP_SRCS)
	$(MAKE) $(KDUMP_SRCS) $(UDUMP_SRCS)

# ---- 4. The Iris proofs (depend on the model and the kernel dump) ----
$(IRIS)/CoqMakefile: $(IRIS)/_CoqProject
	cd $(IRIS) && $(RUN) coq_makefile -f _CoqProject -o CoqMakefile
proofs: model kernel-rocq $(IRIS)/CoqMakefile
	$(RUN) $(MAKE) -C $(IRIS) -f CoqMakefile -j$(JOBS)

# ---- cleaning ----
clean-proofs:
	-$(RUN) $(MAKE) -C $(IRIS) -f CoqMakefile clean 2>/dev/null || true
	rm -f $(IRIS)/CoqMakefile* $(IRIS)/*.vo $(IRIS)/*.vos $(IRIS)/*.vok $(IRIS)/*.glob $(IRIS)/.*.aux

clean: clean-proofs
	-$(RUN) $(MAKE) -C $(MODEL) -f CoqMakefile clean 2>/dev/null || true
	-$(RUN) $(MAKE) -C $(KDUMP) -f CoqMakefile clean 2>/dev/null || true
	-$(RUN) $(MAKE) -C $(UDUMP) -f CoqMakefile clean 2>/dev/null || true
	rm -f $(MODEL)/CoqMakefile* $(KDUMP)/CoqMakefile* $(UDUMP)/CoqMakefile*

distclean: clean
	-$(MAKE) -C xv6-riscv clean 2>/dev/null || true

# ---- regenerating the Sail model (manual; needs the Sail toolchain) ----
model-gen:
	@if command -v sail >/dev/null 2>&1; then \
		tools/regen_sail_model.sh $(if $(SAIL_RISCV_DIR),"$(SAIL_RISCV_DIR)",); \
	else \
		echo "Regenerating $(MODEL)/*.v requires the 'sail' compiler (0.20.1,"; \
		echo "sail_coq_backend) on PATH -- eval \$$(opam env) into whichever switch"; \
		echo "has it installed, then run tools/regen_sail_model.sh directly, or"; \
		echo "'make model-gen SAIL_RISCV_DIR=path/to/sail-riscv'."; \
		echo "See README.md > Build > 'Regenerating the Sail model'."; \
		false; \
	fi
