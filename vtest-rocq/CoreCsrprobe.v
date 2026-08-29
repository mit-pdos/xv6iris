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
(* 2. THE MODEL AND QEMU AGREE ON WHICH CSRs EXIST.                        *)
(*                                                                         *)
(*    The whole TRAP TABLE, all 37 slots: both refuse only the control.     *)
(*    There is deliberately no whole-REGION lemma -- the value table beside *)
(*    it holds misa, the counters and mtvec, which differ for reasons that  *)
(*    are not about which registers exist.  Section 4 takes those one at a  *)
(*    time.                                                                 *)
(* ---------------------------------------------------------------------- *)

Definition cp_traps (o : option mstate) : list Z := res_bytes o 8 (4 * 37).
Definition cp_traps_cap (c : list Z) : list Z := cap_bytes c 8 (4 * 37).

Lemma core_csrprobe_trap_table :
  cp_traps cp_run = cp_traps_cap core_csrprobe_qemu_result.
Proof. solve_vtest (cp_traps_cap core_csrprobe_qemu_result). Qed.

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

(* ---------------------------------------------------------------------- *)
(* 4. THE VALUES, now that a machine which refuses a register partway      *)
(*    through the list can still be asked about the rest.                  *)
(*                                                                         *)
(*    This is the thing core_regs_mcsr cannot do: it reads for values, so   *)
(*    the U74's refusal of menvcfg (the seventh register) ends its run and  *)
(*    the other thirty-odd values go unmeasured.  Under trap.S they are     *)
(*    measured, and three of the comparisons below are new because of it.   *)
(*                                                                         *)
(*    NOT COMPARED, and each for a reason that is not about the model:      *)
(*      mtvec     -- the test writes it, so it is an address in whichever   *)
(*                   image ran, and the three images differ                 *)
(*      mcycle, minstret, cycle, instret -- counters; they differ between   *)
(*                   two runs on the same machine                           *)
(*      mhartid   -- the board ran on hart 2 (CoreHart.v is where that is   *)
(*                   the subject)                                           *)
(*      mip       -- QEMU had MTIP set from its own timer                   *)
(* ---------------------------------------------------------------------- *)

Definition cp_val (i : nat) : nat := (256 + 4 * i)%nat.

(* -- misa, measured by `csrr` on all three for the first time -----------
   The board's value was previously known only from a JTAG read, and JTAG
   reads are not this question (see this file's header and the header of
   core_csrprobe.S): the debug module answers for registers the hart will
   not let an instruction touch.  core_csrprobe establishes that misa IS
   csrr-readable on the U74, so this value is the machine's own answer.

   model  0x14112D  A C D F I M S U
   QEMU   0x1411AD  ...and H          (finding 19)
   board  0x94112F  ...and B and X, but NOT H  (finding 29)              *)

Definition cp_misa_model : Z := 0x14112D.
Definition cp_misa_qemu  : Z := 0x1411AD.
Definition cp_misa_board : Z := 0x94112F.

Lemma core_csrprobe_misa_model : res_word cp_run (cp_val 1) = cp_misa_model.
Proof. vm_cast_no_check (eq_refl cp_misa_model). Qed.
Lemma core_csrprobe_misa_qemu :
  cap_word core_csrprobe_qemu_result (cp_val 1) = cp_misa_qemu.
Proof. reflexivity. Qed.
Lemma core_csrprobe_misa_board :
  cap_word core_csrprobe_hw_result (cp_val 1) = cp_misa_board.
Proof. reflexivity. Qed.

Lemma core_csrprobe_misa_all_three_differ :
  cp_misa_model <> cp_misa_qemu
  /\ cp_misa_model <> cp_misa_board
  /\ cp_misa_qemu  <> cp_misa_board.
Proof. repeat split; discriminate. Qed.

(* -- THE MACHINE'S IDENTITY: the model is anonymous ---------------------
   mvendorid / marchid / mimpid are how a kernel asks what it is running
   on.  The model answers 0 to all three, and so does QEMU; the board
   answers with real SiFive values (0x489 is SiFive's JEDEC id).  Zero is
   an architecturally legal answer -- it means "not implemented" -- so this
   is an INCOMPLETENESS and not a defect: a kernel that branches on the
   implementation id has no model execution for the branch it would take on
   this board.  Nothing in xv6 does.  FINDING 33.                        *)

Definition cp_ident_model : Z * Z * Z := (0, 0, 0).
Definition cp_ident_board : Z * Z * Z := (0x489, 0x7, 0x4210427).

Lemma core_csrprobe_ident_model :
  (res_word cp_run (cp_val 12),
   res_word cp_run (cp_val 13),
   res_word cp_run (cp_val 14)) = cp_ident_model.
Proof. solve_vtest cp_ident_model. Qed.

Lemma core_csrprobe_ident_qemu :
  (cap_word core_csrprobe_qemu_result (cp_val 12),
   cap_word core_csrprobe_qemu_result (cp_val 13),
   cap_word core_csrprobe_qemu_result (cp_val 14)) = cp_ident_model.
Proof. reflexivity. Qed.

Lemma core_csrprobe_ident_board :
  (cap_word core_csrprobe_hw_result (cp_val 12),
   cap_word core_csrprobe_hw_result (cp_val 13),
   cap_word core_csrprobe_hw_result (cp_val 14)) = cp_ident_board.
Proof. reflexivity. Qed.

Lemma core_csrprobe_ident_really_diverges : cp_ident_model <> cp_ident_board.
Proof. discriminate. Qed.

(* -- mideleg follows misa.H, and that is finding 19 seen from the board --
   QEMU has the hypervisor extension, so VSSIP/VSTIP/VSEIP/SGEIP are
   hardwired into mideleg (0x1444).  The board has no H and reads 0, which
   is what the MODEL reads too.  So on this register the model matches the
   REAL hardware and not QEMU -- the one place so far where the board
   vindicates the model against QEMU.                                    *)

Lemma core_csrprobe_mideleg_model_is_board :
  (res_word cp_run (cp_val 3), cap_word core_csrprobe_hw_result (cp_val 3))
    = (0, 0).
Proof. solve_vtest (0, 0). Qed.

Lemma core_csrprobe_mideleg_qemu : cap_word core_csrprobe_qemu_result (cp_val 3)
  = 0x1444.
Proof. reflexivity. Qed.

(* -- tselect: three answers, and the model's is the odd one -------------
   [read_CSR 0x7A0] returns [not_vec tselect] -- the architecture's "no
   trigger selectable" stub -- so on a power-on-zero register file it reads
   all-ones.  QEMU answers 0; the board answers 7, which is where OpenOCD
   left it (it reported 8 triggers).  None of the three refuses the read,
   so this is a value difference and not an existence one.

   NOTE the poison collision: core_csrprobe.S preloads 0xffffffff so that a
   TRAPPED read is visible, and the model's tselect legitimately reads
   0xffffffff.  The trap table is what tells them apart, and it says this
   slot did not trap.                                                    *)

Lemma core_csrprobe_tselect_did_not_trap :
  (res_word cp_run (cp_slot 35),
   cap_word core_csrprobe_qemu_result (cp_slot 35),
   cap_word core_csrprobe_hw_result (cp_slot 35)) = (0, 0, 0).
Proof. solve_vtest (0, 0, 0). Qed.

Lemma core_csrprobe_tselect_values :
  (res_word cp_run (cp_val 35),
   cap_word core_csrprobe_qemu_result (cp_val 35),
   cap_word core_csrprobe_hw_result (cp_val 35))
    = (0xFFFFFFFF, 0, 7).
Proof. solve_vtest (0xFFFFFFFF, 0, 7). Qed.

(* -- the frozen clock again, by a second route -------------------------
   ClintTime.v found it through the CLINT's mtime.  Here it is in the CSR
   file: the model's mcycle and cycle read 0 while minstret and instret are
   nonzero and advancing.  Same finding (27), independent evidence.      *)

Lemma core_csrprobe_model_clock_is_zero :
  (res_word cp_run (cp_val 30), res_word cp_run (cp_val 32)) = (0, 0).
Proof. solve_vtest (0, 0). Qed.

Lemma core_csrprobe_model_minstret_is_not :
  res_word cp_run (cp_val 31) = 271.
Proof. vm_cast_no_check (eq_refl 271). Qed.
