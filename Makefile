# ======================================================================
# Top-level build for the xv6-on-Sail RISC-V Rocq/Iris development.
#
#   make            build everything needed for the proofs (== make proofs)
#   make proofs     compile the Iris proofs (iris/) + their dependencies
#   make model      compile the Sail-generated Coq model (model-xv6iris/)
#   make kernel     build the xv6 kernel ELF (xv6-riscv/kernel/kernel)
#   make dump       (re)generate kernel-rocq/*.v from the ELF, then compile it
#   make kernel-rocq  compile kernel-rocq/ (regenerating its .v if the ELF changed)
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
IRIS  := iris

KERNEL_ELF := xv6-riscv/kernel/kernel
KDUMP_SRCS := $(KDUMP)/KernelInstrs.v $(KDUMP)/KernelData.v $(KDUMP)/KernelSyms.v

.PHONY: all proofs model kernel dump kernel-rocq \
        clean clean-proofs distclean model-gen

all: proofs

# ---- 1. Sail-generated Coq model (rv64d_types, riscv_extras, rv64d) ----
$(MODEL)/CoqMakefile: $(MODEL)/_CoqProject
	cd $(MODEL) && $(RUN) coq_makefile -f _CoqProject -o CoqMakefile
model: $(MODEL)/CoqMakefile
	$(RUN) $(MAKE) -C $(MODEL) -f CoqMakefile -j$(JOBS)

# ---- 2. xv6 kernel ELF (disassembled into Rocq by the dumper) ----
kernel: $(KERNEL_ELF)
$(KERNEL_ELF):
	$(MAKE) -C xv6-riscv kernel/kernel

# ---- 3. Dump the kernel image into Rocq and compile it ----
$(KDUMP)/KernelInstrs.v: $(KERNEL_ELF) tools/dump_kernel.py
	$(PYTHON) tools/dump_kernel.py --format rocq      --objdump $(OBJDUMP) --out $@
$(KDUMP)/KernelData.v:   $(KERNEL_ELF) tools/dump_kernel.py
	$(PYTHON) tools/dump_kernel.py --format rocq-data --objdump $(OBJDUMP) --out $@
$(KDUMP)/KernelSyms.v:   $(KERNEL_ELF) tools/dump_kernel.py
	$(PYTHON) tools/dump_kernel.py --format rocq-syms --objdump $(OBJDUMP) --out $@
$(KDUMP)/CoqMakefile: $(KDUMP)/_CoqProject
	cd $(KDUMP) && $(RUN) coq_makefile -f _CoqProject -o CoqMakefile
kernel-rocq: $(KDUMP_SRCS) $(KDUMP)/CoqMakefile
	$(RUN) $(MAKE) -C $(KDUMP) -f CoqMakefile -j$(JOBS)
dump: kernel-rocq

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
	rm -f $(MODEL)/CoqMakefile* $(KDUMP)/CoqMakefile*

distclean: clean
	-$(MAKE) -C xv6-riscv clean 2>/dev/null || true

# ---- regenerating the Sail model (manual; needs the Sail toolchain) ----
model-gen:
	@echo "Regenerating $(MODEL)/*.v requires the 'sail' compiler and the"
	@echo "sail-riscv sources.  See README.md > Build > 'Regenerating the Sail model'."
	@false
