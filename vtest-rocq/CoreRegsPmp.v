(* CoreRegsPmp.v -- THE PHYSICAL-MEMORY-PROTECTION FILE AT BOOT.

   Source: tools/vtest/tests/core_regs_pmp.S.  Capture: CoreRegsPmpGen.v.

   RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):
     +0   done            +4   status = 1
     +8   pmpcfg0  0x3A0  +16  pmpcfg2  0x3A2
     +24 + 8*i           pmpaddr<i> (0x3B0 + i), i = 0..15  ->  +24 .. +144

   THE RESULT: the whole file -- both packed cfg words and all sixteen
   address registers -- agrees under the DEFAULT boot, every entry zero on
   both machines.  No witness power-on file is needed, so this file uses
   [VTest.start] rather than [VBoot.start_from].

   WHY THIS ONE IS WORTH HAVING even though the answer is all zeros.
   ArchReset.v's board list says explicitly that pmpcfg is NOT a board
   obligation: the privileged spec's own [reset_pmp] is what establishes
   [RiscvLang.reset_regs]' [pmp_all_off] over an ARBITRARY power-on vector
   ([BootReset.exec_reset_pmp]).  So the zeros the model shows here are
   produced by the model's reset CODE, not assumed of the board -- and this
   test is the check that the code's answer is the machine's answer.  The A
   field of every entry being 0 (OFF) is what makes every access unmatched
   by PMP, which is the precondition the whole M-mode memory argument runs
   under.

   Both machines have sixteen entries (the model's [sys_pmp_count] = 16,
   QEMU's default rv64 CPU likewise), so this is the complete file and not a
   sample.  The comparison is over the whole 4 KB region. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest CoreRegsPmpGen.
Local Open Scope Z_scope.

Definition pmp_run : option mstate := run_until 600 (start core_regs_pmp_text).

Lemma core_regs_pmp_result : result_of pmp_run = core_regs_pmp_qemu_result.
Proof. solve_vtest core_regs_pmp_qemu_result. Qed.

Lemma core_regs_pmp_disk : core_regs_pmp_qemu_disk = [].
Proof. reflexivity. Qed.
