(* ======================================================================= *)
(* CoreRegsCtr.v -- THE COUNTERS, AND WHY THEY ARE NOT A MODEL BUG.         *)
(*                                                                          *)
(* Source: tools/vtest/tests/core_regs_ctr.S.  Capture: CoreRegsCtrGen.v.    *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):     *)
(*   +8   mcycle  0xB00      +16  minstret 0xB02                             *)
(*   +24  cycle   0xC00      +32  time     0xC01                             *)
(*   +40  instret 0xC02      +48  mcycle 0xB00 AGAIN, six instructions later *)
(*                                                                          *)
(* THESE ARE THE ONLY ARCHITECTURALLY READABLE REGISTERS WHOSE VALUE IS NOT  *)
(* A CONSTANT OF THE BOOT, so the suite's usual equation is not available in *)
(* either direction: QEMU's mcycle/minstret/cycle/instret are the host's     *)
(* counters and are different on every run, and the vtest harness always     *)
(* steps [riscv_step false] -- the model's clock is never ticked.  So this   *)
(* file states the MODEL's values, which ARE constants and can be pinned,    *)
(* and only the SHAPE of QEMU's, which is what survives a regeneration.      *)
(*                                                                          *)
(* WHAT IT FINDS, and the classification is the point of the file:           *)
(*                                                                          *)
(*   * mcycle / cycle DO NOT MOVE in the model.  Two samples six             *)
(*     instructions apart are both 0.  This is a PROPERTY OF THE HARNESS,    *)
(*     NOT OF THE MODEL: the cycle counter advances on the platform's        *)
(*     clock tick, which [riscv_step false] deliberately does not perform,   *)
(*     so no vtest image can ever observe it move.  Reporting it as a model  *)
(*     defect would be wrong -- the model has executions in which the        *)
(*     counter advances; this harness never selects one.                     *)
(*                                                                          *)
(*   * time DOES NOT MOVE either, and for the same reason: it is the CLINT's *)
(*     mtime, which the harness's device fabric never advances.  QEMU's is   *)
(*     small but nonzero (a few tens of microseconds of boot at 10 MHz).     *)
(*                                                                          *)
(*   * minstret / instret DO MOVE, and this is the check that the previous   *)
(*     two bullets are about the CLOCK and not about counters in general.    *)
(*     The retired-instruction counter is incremented by the retire step     *)
(*     itself, not by a tick, so the model advances it exactly as the        *)
(*     hardware does: the two reads here are 13 and 19, and the six          *)
(*     instructions between them are precisely the `sd`/`csrr` pairs the .S  *)
(*     puts there.  A model that had simply frozen ALL its counters would    *)
(*     look identical on mcycle and would fail here.                         *)
(*                                                                          *)
(* CONSEQUENCE, stated once so it is not rediscovered: a vtest image cannot  *)
(* observe elapsed time, so no test in this suite can exercise the timer     *)
(* interrupt path, and mip.MTIP can only ever be present as power-on garbage *)
(* (see CoreRegsMcsr.v §2).                                                  *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest CoreRegsCtrGen.
Local Open Scope Z_scope.

Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

Definition ctr_run : option mstate := run_until 600 (start core_regs_ctr_text).

Definition ctr_offs : list nat := [8; 16; 24; 32; 40; 48]%nat.

(* ---------------------------------------------------------------------- *)
(* 1. The model's counters, pinned.  ONE evaluation for all six.           *)
(*    mcycle, cycle and time are frozen; minstret and instret are not.     *)
(* ---------------------------------------------------------------------- *)

(* The [true] is section 3's statement, carried in the same tuple so that it
   costs no second evaluation of the run: the model's two mcycle samples,
   taken six instructions apart, are EQUAL. *)
Definition ctr_model : list Z * bool := ([0; 13; 0; 0; 19; 0], true).

Lemma core_regs_ctr_model :
  ((fun o => res_dw ctr_run o) <$> ctr_offs,
   res_dw ctr_run 8%nat =? res_dw ctr_run 48%nat) = ctr_model.
Proof. solve_vtest ctr_model. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The shape of QEMU's, stated so that regenerating the capture does    *)
(*    not make this file red.  A `make vtest` run produces different       *)
(*    numbers every time and these three facts hold of all of them.        *)
(* ---------------------------------------------------------------------- *)

(* the cycle counter MOVED between the two samples *)
Lemma core_regs_ctr_qemu_cycle_moves :
  cap_dw core_regs_ctr_qemu_result 8%nat < cap_dw core_regs_ctr_qemu_result 48%nat.
Proof. vm_compute. reflexivity. Qed.

(* ...and so did the retired-instruction counter *)
Lemma core_regs_ctr_qemu_instret_moves :
  cap_dw core_regs_ctr_qemu_result 16%nat < cap_dw core_regs_ctr_qemu_result 40%nat.
Proof. vm_compute. reflexivity. Qed.

(* ...and mtime is running *)
Lemma core_regs_ctr_qemu_time_running :
  0 < cap_dw core_regs_ctr_qemu_result 32%nat.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The divergence, stated as the thing that is actually true of every   *)
(*    run rather than as a comparison of two run-dependent literals: the   *)
(*    model's two mcycle samples are EQUAL and the hardware's are not.     *)
(*    The model half is the [true] in [ctr_model] above; the hardware half  *)
(*    is [core_regs_ctr_qemu_cycle_moves].  Green today; red the day the    *)
(*    harness learns to tick the clock, which is exactly when this file     *)
(*    should be revisited.                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma core_regs_ctr_disk : core_regs_ctr_qemu_disk = [].
Proof. reflexivity. Qed.
