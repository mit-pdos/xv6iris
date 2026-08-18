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
#   make sail-rev-check  warn if sail-riscv/ is not at the pinned $(SAIL_RISCV_REV)
#   make model-gen  regenerate model-xv6iris/*.v from sail-riscv (needs `sail`)
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
GENCODE    := tools/gen_code.py
XV6_DIR    := xv6-riscv
XV6_URL    ?= https://github.com/zeldovich/xv6-riscv
KERNEL_ELF := $(XV6_DIR)/kernel/kernel
USER_DIR   := $(XV6_DIR)/user

# THE Sail model this development is proved against.  Like $(XV6_DIR), the
# checkout is .gitignored, so these two lines are the only record of where the
# generated model-xv6iris/*.v came from.  It is a FORK of riscv/sail-riscv: its
# delta upstream is the atomic PTE A/D-bit update (an exclusive PTE read + a
# conditional PTE write, with the tablewalk checks re-run on the freshly read
# value), which is what the page-table proofs are stated against.
SAIL_RISCV_DIR ?= sail-riscv
SAIL_RISCV_URL ?= https://github.com/zeldovich/sail-riscv
SAIL_RISCV_REV ?= c32fbf4111b849061db1812355d6da9df8c2e396

# THE xv6 revision this development is proved against.  $(XV6_DIR) is
# .gitignored, so this is the only record of which upstream commit the tracked
# kernel-rocq/*.v came from -- building any other revision moves symbol
# addresses out from under every proof that names one (a few commits either
# way already move most of them).  Verified: a kernel built here reproduces
# kernel-rocq/*.v byte for byte and symbol for symbol.
#
# THE PIN IS A CLEAN TIP OF $(XV6_URL)'s `verified` BRANCH.  It was briefly a
# local cherry-pick (ae96fd0 + 9da28f5) while the fix for kernel-defects.md D2
# was ahead of the revision this tree was proved against; converging on the
# branch tip retired that apparatus, and the pin has tracked the tip since
# (…; d80e61c5: tx_lock becomes a spinlock, panic path removed; a28e94b: no
# procdump from the console; 2691300 -> 1a70c2e: unreachable() split out of
# panic(), rebased onto upstream 13602eb, which gives sleep() a prototype and
# so rewrites sys_sync's call to it; 1a70c2e -> 515391a: seventeen more
# panic() call sites become unreachable(), and gcc reorders four of fs.c's
# functions).  Nothing here is a local commit:
# `git -C xv6-riscv checkout --detach $(XV6_REV)` reproduces the image, and
# that is the whole recipe.
#
# THAT BRANCH IS REBASED, NOT APPENDED TO, so `git -C xv6-riscv fetch` on a
# tree pinned at the previous tip reports a FORCED UPDATE and the old pin
# stays reachable only from your local clone -- expect the diff between two
# consecutive pins to be an upstream commit that landed UNDER the series, not
# on top of it.
XV6_REV ?= f60ff589b461deba936a917235a1ddf778ea7262

KDUMP_SRCS := $(KDUMP)/KernelInstrs.v $(KDUMP)/KernelData.v $(KDUMP)/KernelSyms.v

# User-space programs to dump into user-rocq/, as <xv6 program>:<Rocq module
# prefix> pairs (the ELF is $(USER_DIR)/_<program>).  Adding one here also needs
# its three .v listed in user-rocq/_CoqProject.
USER_DUMPS ?= sync:Sync echo:Echo sh:Sh

.PHONY: all proofs model kernel user dump dump-force kernel-rocq user-rocq \
        xv6-rev-check sail-rev-check gen-code check-decode update-decode \
        clean clean-proofs distclean model-gen

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
	git -C $@ fetch -q origin $(XV6_REV)
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

# ---- 3a. Keep the iris/ decode layer in step with the image ----
#
# Every instr fact states an encoding word and a decoded immediate; both are
# properties of the IMAGE, and both move when the kernel is relaid out --
# including in functions whose own source did not change, via re-encoded call
# targets and linker relaxation.  (The pc's themselves are symbol-relative,
# [KernelSyms.bpin + 0x14], and survive a relayout untouched.)
#
# So the whole layer -- iris/KernelDecode*.v and every iris/Code*.v named in
# tools/code_manifest.json -- is GENERATED from kernel-rocq/, never patched.
#
#   make gen-code        regenerate the decode layer from the tracked dump
#   make check-decode    regenerate, then fail if anything moved
#
# check-decode's diff is the signal after a dump-force: a Code file that
# changed shape (a different instruction, not just a different immediate) is a
# real code change, and its proof needs a human.
gen-code:
	$(PYTHON) $(GENCODE) --iris $(IRIS) --kernel-rocq $(KDUMP)
# The diff is scoped to the files gen_code.py actually WRITES -- the manifest's
# outputs plus the shared decode catalogs -- not to the $(IRIS)/Code*.v glob:
# that glob also sweeps the HAND-WRITTEN Code<F>Aux.v files, so any uncommitted
# edit to one of those failed this target with a diff that has nothing to do
# with the dump.  (It fired twice on unrelated work before being narrowed.)
GENFILES := $(addprefix $(IRIS)/,$(shell $(PYTHON) -c "import json;print(' '.join(sorted(set(e[0] for e in json.load(open('tools/code_manifest.json'))))))"))
check-decode: gen-code
	git diff --exit-code -- $(IRIS)/KernelDecode*.v $(GENFILES)
update-decode: gen-code

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
proofs: model kernel-rocq user-rocq $(IRIS)/CoqMakefile
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

# ---- the Sail sources, pinned at $(SAIL_RISCV_REV) ----
# Same treatment as $(XV6_DIR): a build input pinned by this Makefile, cloned
# detached, .gitignored.  An existing checkout is left alone (see
# sail-rev-check).  Only `model-gen` needs it; a normal build uses the
# generated .v checked into $(MODEL).
$(SAIL_RISCV_DIR):
	git clone $(SAIL_RISCV_URL) $@
	git -C $@ checkout --detach $(SAIL_RISCV_REV)

sail-rev-check: | $(SAIL_RISCV_DIR)
	@have=`git -C $(SAIL_RISCV_DIR) rev-parse HEAD 2>/dev/null`; \
	 want=`git -C $(SAIL_RISCV_DIR) rev-parse $(SAIL_RISCV_REV) 2>/dev/null`; \
	 if [ -z "$$want" ]; then \
	   echo "WARNING: $(SAIL_RISCV_DIR) does not have SAIL_RISCV_REV=$(SAIL_RISCV_REV);"; \
	   echo "         try 'git -C $(SAIL_RISCV_DIR) fetch $(SAIL_RISCV_URL)'."; \
	 elif [ "$$have" != "$$want" ]; then \
	   echo "WARNING: $(SAIL_RISCV_DIR) is at $$have,"; \
	   echo "         not the pinned SAIL_RISCV_REV=$$want."; \
	   echo "         A model regenerated there is NOT the one the proofs are about."; \
	   echo "         Fix with: git -C $(SAIL_RISCV_DIR) checkout --detach $(SAIL_RISCV_REV)"; \
	 fi

# ---- regenerating the Sail model (manual; needs the Sail toolchain) ----
model-gen: | $(SAIL_RISCV_DIR)
	@if command -v sail >/dev/null 2>&1; then \
		SAIL_RISCV_URL="$(SAIL_RISCV_URL)" SAIL_RISCV_REV="$(SAIL_RISCV_REV)" \
		  tools/regen_sail_model.sh "$(SAIL_RISCV_DIR)"; \
	else \
		echo "Regenerating $(MODEL)/*.v requires the 'sail' compiler (0.20.1,"; \
		echo "sail_coq_backend) on PATH -- eval \$$(opam env) into whichever switch"; \
		echo "has it installed, then run tools/regen_sail_model.sh directly, or"; \
		echo "'make model-gen SAIL_RISCV_DIR=path/to/sail-riscv'."; \
		echo "See README.md > Build > 'Regenerating the Sail model'."; \
		false; \
	fi
