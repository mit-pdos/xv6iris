(* CoreRegsFcsr.v -- THE FLOATING-POINT CONTROL CSRs AT BOOT.

   Source: tools/vtest/tests/core_regs_fcsr.S.  Capture: CoreRegsFcsrGen.v.

   RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):
     +8   fcsr 0x003    +16  fflags 0x001
     +24  frm  0x002    +32  mstatus 0x300, read back AFTER the FS write

   THE RESULT: whole-region agreement under the DEFAULT boot, so no witness
   power-on file is needed and this file uses [VTest.start].

   WHY THE TEST HAS TO WRITE SOMETHING FIRST.  mstatus.FS is Off at boot on
   both machines, and with FS = Off every fp CSR read is an illegal
   instruction, so the image sets FS = Initial before reading.  That makes
   +32 the interesting entry rather than a formality: it says the model's
   [legalize_mstatus] accepted the same FS write the hardware did and
   produced the same 0xA_0000_2000 -- FS = 1, SD still 0, and no other field
   disturbed.  fcsr, fflags and frm are then 0 on both.

   THIS TEST IS SPLIT FROM core_regs_fpr ON PURPOSE.  Reading the fp CSRs
   needs only Zicsr, which the model has; reading the fp REGISTER FILE needs
   an fp store, which the model has no encoding for at all.  Putting them in
   one image would have made the model trap before it reached these three
   and this comparison would never have happened.  See CoreRegsFpr.v. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest CoreRegsFcsrGen.
Local Open Scope Z_scope.

Definition fcsr_run : option mstate := run_until 600 (start core_regs_fcsr_text).

Lemma core_regs_fcsr_result : result_of fcsr_run = core_regs_fcsr_qemu_result.
Proof. solve_vtest core_regs_fcsr_qemu_result. Qed.

Lemma core_regs_fcsr_disk : core_regs_fcsr_qemu_disk = [].
Proof. reflexivity. Qed.
