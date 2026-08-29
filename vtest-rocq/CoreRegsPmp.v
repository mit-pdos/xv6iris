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
Require Import VTest CoreRegsPmpGen CoreRegsPmpHart1Gen.
Local Open Scope Z_scope.

Definition pmp_run : option mstate := run_until 600 (start core_regs_pmp_text).

Lemma core_regs_pmp_result : result_of pmp_run = core_regs_pmp_qemu_result.
Proof. solve_vtest core_regs_pmp_qemu_result. Qed.

Lemma core_regs_pmp_disk : core_regs_pmp_qemu_disk = [].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* THE SAME FILE, ON HART 1.                                              *)
(*                                                                        *)
(*    Capture: CoreRegsPmpHart1Gen.v -- the same source built with PRIMARY_HART=1
    and run under -smp 2, with the model started on the same hart by
    [VTest.start_hart].  See CoreHart.v for what the hart variant is and
    why it is a different IMAGE rather than a different schedule.

    Two claims, and the second is the interesting one: the model
    reproduces the machine on hart 1, and the whole PMP file is
    BYTE-IDENTICAL to what it was on hart 0.  So the reset chain's
    hart-id argument does not leak into this register file -- which is
    not automatic, since [ColdBoot.cold_regs] takes that id and could
    have put it anywhere.  Contrast core_regs_mcsr, where exactly one
    register moves, and it is mhartid.                                    *)
(* ---------------------------------------------------------------------- *)

Definition pmp_h1_run : option mstate :=
  run_until 600 (start_hart core_regs_pmp_hart1_primary_hart core_regs_pmp_hart1_text).

Lemma core_regs_pmp_hart1_result :
  result_of pmp_h1_run = core_regs_pmp_hart1_qemu_result.
Proof. solve_vtest core_regs_pmp_hart1_qemu_result. Qed.

Lemma core_regs_pmp_hart1_is_hart0 :
  core_regs_pmp_hart1_qemu_result = core_regs_pmp_qemu_result.
Proof. reflexivity. Qed.
