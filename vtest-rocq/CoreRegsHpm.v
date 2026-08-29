(* CoreRegsHpm.v -- THE HARDWARE PERFORMANCE-MONITOR FILE AT BOOT.

   Source: tools/vtest/tests/core_regs_hpm.S.  Capture: CoreRegsHpmGen.v.

   RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):
     +8   + 8*k   mhpmcounter<3+k>  (0xB03 + k), k = 0..15  ->  +8   .. +128
     +136 + 8*k   hpmcounter<3+k>   (0xC03 + k), k = 0..15  ->  +136 .. +256
     +264 + 8*k   mhpmevent<3+k>    (0x323 + k), k = 0..15  ->  +264 .. +384

   THE RESULT: whole-region agreement under the DEFAULT boot -- all
   forty-eight zero on both machines -- so no witness power-on file is
   needed and this file uses [VTest.start].

   THE PART THAT IS NOT `everything was zero anyway`.  Reading a counter is
   the one place where a boot-state test also exercises a PERMISSION check:
   an M-mode read of the unprivileged alias hpmcounter<n> (0xC03 + k) goes
   through the counter-enable logic, and mcounteren is 0 at boot on both
   machines (CoreRegsMcsr.v pins it).  Both machines nevertheless complete
   the read, which is correct -- mcounteren gates S and U, not M -- and it
   is a thing the model could have got wrong in the strict direction and did
   not.  The M-mode aliases mhpmcounter<n> (0xB03 + k) are read alongside so
   the two paths are compared against each other as well as against QEMU.

   THE RANGE IS THE INTERSECTION OF THE TWO MACHINES, and finding it was the
   work: QEMU's default rv64 CPU implements counters 3..18 and traps on
   19..31, so 0xB13 / 0xC13 upward would have hung the capture.  Both
   machines refuse the RV32-only high halves (mcycleh 0xB80, cycleh 0xC80),
   which is right at xlen = 64; those are not read here.  See
   CoreRegsCtr.v for mcycle/minstret/time, which do not settle and are kept
   out of this comparison on purpose. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest CoreRegsHpmGen CoreRegsHpmHart1Gen.
Local Open Scope Z_scope.

Definition hpm_run : option mstate := run_until 900 (start core_regs_hpm_text).

Lemma core_regs_hpm_result : result_of hpm_run = core_regs_hpm_qemu_result.
Proof. solve_vtest core_regs_hpm_qemu_result. Qed.

Lemma core_regs_hpm_disk : core_regs_hpm_qemu_disk = [].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* THE SAME FILE, ON HART 1.                                              *)
(*                                                                        *)
(*    Capture: CoreRegsHpmHart1Gen.v -- the same source built with PRIMARY_HART=1
    and run under -smp 2, with the model started on the same hart by
    [VTest.start_hart].  See CoreHart.v for what the hart variant is and
    why it is a different IMAGE rather than a different schedule.

    Two claims, and the second is the interesting one: the model
    reproduces the machine on hart 1, and the whole HPM file is
    BYTE-IDENTICAL to what it was on hart 0.  So the reset chain's
    hart-id argument does not leak into this register file -- which is
    not automatic, since [ColdBoot.cold_regs] takes that id and could
    have put it anywhere.  Contrast core_regs_mcsr, where exactly one
    register moves, and it is mhartid.                                    *)
(* ---------------------------------------------------------------------- *)

Definition hpm_h1_run : option mstate :=
  run_until 900 (start_hart core_regs_hpm_hart1_primary_hart core_regs_hpm_hart1_text).

Lemma core_regs_hpm_hart1_result :
  result_of hpm_h1_run = core_regs_hpm_hart1_qemu_result.
Proof. solve_vtest core_regs_hpm_hart1_qemu_result. Qed.

Lemma core_regs_hpm_hart1_is_hart0 :
  core_regs_hpm_hart1_qemu_result = core_regs_hpm_qemu_result.
Proof. reflexivity. Qed.
