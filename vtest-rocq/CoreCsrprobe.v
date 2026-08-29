(* CoreCsrprobe.v -- WHICH CSRs DOES EACH MACHINE ACTUALLY IMPLEMENT?

   Source: tools/vtest/tests/core_csrprobe.S.
   Captures: CoreCsrprobeGen.v (QEMU virt) and CoreCsrprobeHwGen.v (a
   StarFive VisionFive 2 over JTAG).

   THE FIRST TEST IN THE SUITE THAT TREATS A TRAP AS DATA.  Every other test
   here either avoids faulting or reports its first fault and stops --
   mtvec is 0 by default, so a fault trap-loops at 0 and the run is over
   (README.md, "A bad FETCH is a TRAP LOOP").  This one installs the M-mode
   handler in tools/vtest/trap.S, which records the trap and RESUMES PAST
   the faulting instruction, so one run can ask thirty-seven questions
   instead of one.

   WHY THAT MATTERS HERE.  core_regs_mcsr reads these registers for their
   VALUES, so the first register a machine refuses ends the run.  On the
   VisionFive 2 that is the seventh one -- `csrr menvcfg` takes an illegal
   instruction, and everything after it was simply unmeasured.  The board
   scoreboard read that as "core_regs_mcsr fails", which is true and says
   nothing.  This test turns it into a table.

   THE RESULT, and it is a three-way comparison the suite could not make
   before:

     - the MODEL implements all 36 CSRs probed here;
     - QEMU's default rv64 virt CPU implements all 36 too;
     - the VisionFive 2's U74 refuses FOUR of them: menvcfg, mconfigptr and
       senvcfg (privileged spec 1.12 additions the core predates) and
       `time`, which SiFive cores leave to firmware to emulate.

   THE CONTROL IS LOad-BEARING.  An all-zeros instruction word is a defined
   illegal encoding, and all three trap on it.  Without that column a run in
   which the handler was never reached is indistinguishable from one in
   which nothing trapped -- every entry would be 0 either way.  It is also
   the only reason this file can claim the model's trap machinery WORKS:
   the model refuses none of the 36, so the control is the one place its
   handler runs at all. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest CoreCsrprobeGen CoreCsrprobeHwGen.
Local Open Scope Z_scope.

(* slot i is published at RES_PAYLOAD + 4*i *)
Definition cp_slot (i : nat) : nat := (8 + 4 * i)%nat.

(* the four the U74 refuses, and the control *)
Definition CP_MENVCFG    : nat := cp_slot 16.
Definition CP_MCONFIGPTR : nat := cp_slot 17.
Definition CP_SENVCFG    : nat := cp_slot 19.
Definition CP_TIME       : nat := cp_slot 33.
Definition CP_CONTROL    : nat := cp_slot 36.
Definition CP_TRAPN      : nat := 2048.   (* RES_TRAPS: trap.S's own count *)

Definition cp_run    : option mstate := run_until 4000 (start core_csrprobe_text).
Definition cp_hw_run : option mstate :=
  run_until 4000 (start_hart core_csrprobe_hw_primary_hart core_csrprobe_hw_text).

Lemma core_csrprobe_completes : run_status 4000 (start core_csrprobe_text) = VDone.
Proof. vm_cast_no_check (eq_refl VDone). Qed.
Lemma core_csrprobe_hw_completes :
  run_status 4000 (start_hart core_csrprobe_hw_primary_hart
                              core_csrprobe_hw_text) = VDone.
Proof. vm_cast_no_check (eq_refl VDone). Qed.

(* ---------------------------------------------------------------------- *)
(* 1. THE CONTROL, first, because nothing below means anything without it. *)
(*                                                                         *)
(*    An all-zeros instruction word traps on every machine and in the       *)
(*    model, which is what says the handler was REACHED and that a 0        *)
(*    elsewhere means "the machine answered" rather than "the handler       *)
(*    never ran".                                                          *)
(* ---------------------------------------------------------------------- *)

Lemma core_csrprobe_control_model : res_word cp_run    CP_CONTROL = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.
Lemma core_csrprobe_control_hw_model : res_word cp_hw_run CP_CONTROL = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.
Lemma core_csrprobe_control_qemu :
  cap_word core_csrprobe_qemu_result CP_CONTROL = 1.
Proof. reflexivity. Qed.
Lemma core_csrprobe_control_board :
  cap_word core_csrprobe_hw_result CP_CONTROL = 1.
Proof. reflexivity. Qed.

(* THE MODEL'S TRAP MACHINERY WORKS, and this is where that is established:
   it takes the illegal-instruction trap, runs trap.S's handler -- which
   reads mcause, mepc and mtval and stores them -- and RETURNS through mret
   to the instruction after the faulting one.  Exactly one trap in the whole
   run, which is the control and nothing else. *)
Lemma core_csrprobe_model_traps_once : res_word cp_run CP_TRAPN = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.
Lemma core_csrprobe_qemu_traps_once :
  cap_word core_csrprobe_qemu_result CP_TRAPN = 1.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE MODEL AND QEMU AGREE ON ALL 36, and the whole region says so.    *)
(* ---------------------------------------------------------------------- *)

Lemma core_csrprobe_result : result_of cp_run = core_csrprobe_qemu_result.
Proof. solve_vtest core_csrprobe_qemu_result. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. THE BOARD REFUSES FOUR, AND THE MODEL DOES NOT.                      *)
(*                                                                         *)
(*    Three are privileged-spec 1.12 additions (menvcfg, mconfigptr,       *)
(*    senvcfg) that the U74 predates.  The fourth is `time`, which SiFive  *)
(*    cores do not implement at all -- M-mode firmware is expected to       *)
(*    emulate rdtime, which is exactly what OpenSBI does on this board.     *)
(*                                                                         *)
(*    CLASSIFICATION: the model is WIDER than this machine, which is the    *)
(*    unsound direction -- the hardware's trap has no model execution.  It  *)
(*    is the same axis as finding 22 and it does not settle README.md's     *)
(*    open decision either; what it does is make that decision concrete,    *)
(*    because the model is now known to be wider than BOTH machines and     *)
(*    narrower than neither.                                                *)
(*                                                                         *)
(*    menvcfg is the one that is live: a pt_ program must pin menvcfg.ADUE  *)
(*    before satp (README.md's rules, finding 20), and on this board it     *)
(*    CANNOT -- the CSR does not exist.  Any port of the pt_ area to this   *)
(*    hardware has to deal with that first.                                *)
(* ---------------------------------------------------------------------- *)

Definition cp_board_refuses : Z * Z * Z * Z := (1, 1, 1, 1).
Definition cp_model_answers : Z * Z * Z * Z := (0, 0, 0, 0).

Lemma core_csrprobe_board_refuses_four :
  (cap_word core_csrprobe_hw_result CP_MENVCFG,
   cap_word core_csrprobe_hw_result CP_MCONFIGPTR,
   cap_word core_csrprobe_hw_result CP_SENVCFG,
   cap_word core_csrprobe_hw_result CP_TIME) = cp_board_refuses.
Proof. reflexivity. Qed.

Lemma core_csrprobe_model_answers_four :
  (res_word cp_hw_run CP_MENVCFG,
   res_word cp_hw_run CP_MCONFIGPTR,
   res_word cp_hw_run CP_SENVCFG,
   res_word cp_hw_run CP_TIME) = cp_model_answers.
Proof. solve_vtest cp_model_answers. Qed.

Lemma core_csrprobe_qemu_answers_four :
  (cap_word core_csrprobe_qemu_result CP_MENVCFG,
   cap_word core_csrprobe_qemu_result CP_MCONFIGPTR,
   cap_word core_csrprobe_qemu_result CP_SENVCFG,
   cap_word core_csrprobe_qemu_result CP_TIME) = cp_model_answers.
Proof. reflexivity. Qed.

Lemma core_csrprobe_really_diverges : cp_model_answers <> cp_board_refuses.
Proof. discriminate. Qed.

(* ...and the count agrees with the table: four refusals plus the control. *)
Lemma core_csrprobe_board_traps_five :
  cap_word core_csrprobe_hw_result CP_TRAPN = 5.
Proof. reflexivity. Qed.
