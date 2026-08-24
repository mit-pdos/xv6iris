(* CoreRegsScsr.v -- THE S-MODE CSR FILE AT BOOT.

   Source: tools/vtest/tests/core_regs_scsr.S.  Capture: CoreRegsScsrGen.v.

   RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):
     +0   done               +4   status = 1
     +8   sstatus  0x100     +16  sie      0x104
     +24  stvec    0x105     +32  scounteren 0x106
     +40  senvcfg  0x10A     +48  sscratch 0x140
     +56  sepc     0x141     +64  scause   0x142
     +72  stval    0x143     +80  sip      0x144
     +88  satp     0x180     +96  stimecmp 0x14D

   THE RESULT: the whole S-mode file agrees under the DEFAULT boot -- no
   witness power-on file was needed, so VBoot.v's step 2 is not exercised
   here at all and this file uses [VTest.start] rather than [start_from].
   Every one of the twelve is zero on both machines except sstatus, which is
   0x2_0000_0000 (UXL = 2, and nothing else) on both.

   That is a real agreement and not an accident of everything being zero:
   sstatus is a WINDOW onto mstatus ([read_CSR 0x100] is [lower_mstatus] of
   the mstatus register), so its value here is derived from the same
   0xA_0000_0000 that ArchReset.board_regs writes, and the equality says the
   model's [lower_mstatus] narrows SXL/UXL exactly the way the hardware's
   does.  satp = 0 is the one that matters most to the kernel proofs: it is
   what makes the boot chain's `translation is off until start() turns it
   on` true of the machine as well as of the model.

   The comparison is over the WHOLE 4 KB region, untouched tail included, so
   nothing can hide past +96. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest CoreRegsScsrGen.
Local Open Scope Z_scope.

Definition scsr_run : option mstate := run_until 600 (start core_regs_scsr_text).

Lemma core_regs_scsr_result : result_of scsr_run = core_regs_scsr_qemu_result.
Proof. solve_vtest core_regs_scsr_qemu_result. Qed.

(* ...and it touched no disk, as QEMU did not. *)
Lemma core_regs_scsr_disk : core_regs_scsr_qemu_disk = [].
Proof. reflexivity. Qed.
