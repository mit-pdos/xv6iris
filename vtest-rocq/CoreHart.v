(* CoreHart.v -- WHICH HART AM I, on hart 0 and on hart 1.

   Source: tools/vtest/tests/core_hart.S.
   Captures: CoreHartGen.v (QEMU, -smp 1, hart 0) and CoreHartHart1Gen.v
   (QEMU, -smp 2, PRIMARY_HART=1, hart 1).

   THE FIRST TEST IN THE SUITE THAT DOES NOT RUN ON HART 0.  Every QEMU
   capture before this one was of a program on the boot hart, so nothing had
   ever checked that the hart id reaches the program at all -- and, on the
   model side, nothing had ever exercised [ColdBoot.cold_regs] at an
   argument other than 0.

   WHAT THAT ARGUMENT IS FOR.  The boot chain does exactly two things with
   the hart id: it stores it, so `csrr mhartid` reads it, and it copies it
   into a0.  Those two claims are what make `csrr mhartid` the right way for
   a program to tell harts apart -- [VConc.g0_of]'s header says so, and the
   whole multi-hart harness rests on it -- and until now they had never been
   checked against a machine on more than one hart.  A model that ignored
   the argument would pass every hart-0 test in the tree and fail §2 here.

   The hart-0 half is deliberately kept: on its own it is nearly vacuous
   (everything is 0 because the hart is 0), and its job is to be the control
   that makes the hart-1 half attributable.  The two are the same source and
   differ only in PRIMARY_HART, so any field that moves between them moved
   because of the hart. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest CoreHartGen CoreHartHart1Gen.
Local Open Scope Z_scope.

(* the offsets core_hart.S publishes at; see its header *)
Definition CH_HARTID : nat := 8.
Definition CH_A0     : nat := 12.
Definition CH_AGREE  : nat := 16.
Definition CH_SLOT   : nat := 20.
Definition CH_SP     : nat := 24.
Definition CH_S11    : nat := 28.
Definition CH_A1LO   : nat := 32.
Definition CH_MSTHI  : nat := 44.

Definition ch0_start : mstate := start core_hart_text.
Definition ch1_start : mstate :=
  start_hart core_hart_hart1_primary_hart core_hart_hart1_text.

Definition ch0_run : option mstate := run_until 300 ch0_start.
Definition ch1_run : option mstate := run_until 300 ch1_start.

Lemma core_hart_h0_completes : run_status 300 ch0_start = VDone.
Proof. vm_cast_no_check (eq_refl VDone). Qed.
Lemma core_hart_h1_completes : run_status 300 ch1_start = VDone.
Proof. vm_cast_no_check (eq_refl VDone). Qed.

(* ---------------------------------------------------------------------- *)
(* 1. HART 0 -- the control.                                               *)
(* ---------------------------------------------------------------------- *)

Lemma core_hart_h0_model_hartid : res_word ch0_run CH_HARTID = 0.
Proof. vm_cast_no_check (eq_refl 0). Qed.
Lemma core_hart_h0_qemu_hartid  : cap_word core_hart_qemu_result CH_HARTID = 0.
Proof. reflexivity. Qed.

Lemma core_hart_h0_model_a0 : res_word ch0_run CH_A0 = 0.
Proof. vm_cast_no_check (eq_refl 0). Qed.
Lemma core_hart_h0_qemu_a0  : cap_word core_hart_qemu_result CH_A0 = 0.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. HART 1 -- THE POINT.                                                 *)
(*                                                                         *)
(*    QEMU, told to run this image on hart 1, reports mhartid = 1 -- and    *)
(*    the model, started on the same hart, reports 1 too.  That is the      *)
(*    claim the whole multi-hart story rests on, and this is the first      *)
(*    evidence for it.                                                     *)
(* ---------------------------------------------------------------------- *)

Lemma core_hart_h1_qemu_hartid  : cap_word core_hart_hart1_qemu_result CH_HARTID = 1.
Proof. reflexivity. Qed.
Lemma core_hart_h1_model_hartid : res_word ch1_run CH_HARTID = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.

(* ...and it MOVED.  Same source, same everything but PRIMARY_HART, and the
   field changed on both machines -- so this is the hart id and not a
   constant that happens to be 1. *)
Lemma core_hart_hartid_moved_on_qemu :
  cap_word core_hart_qemu_result CH_HARTID
    <> cap_word core_hart_hart1_qemu_result CH_HARTID.
Proof. discriminate. Qed.

Lemma core_hart_hartid_moved_on_model :
  res_word ch0_run CH_HARTID <> res_word ch1_run CH_HARTID.
Proof.
  rewrite core_hart_h0_model_hartid, core_hart_h1_model_hartid. discriminate.
Qed.

(* THE SECOND HALF OF THE BOOT CONTRACT: a0 carries the same id.  This is
   the claim [VConc.g0_of] leans on, checked on a hart where it is not
   trivially true. *)
Lemma core_hart_h1_qemu_a0  : cap_word core_hart_hart1_qemu_result CH_A0 = 1.
Proof. reflexivity. Qed.
Lemma core_hart_h1_model_a0 : res_word ch1_run CH_A0 = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.

(* ...stated as the program itself computed it, so it does not depend on
   this file reading the two fields correctly: the image compared a0 against
   `csrr mhartid` and published the answer. *)
Lemma core_hart_h1_qemu_a0_is_mhartid :
  cap_word core_hart_hart1_qemu_result CH_AGREE = 1.
Proof. reflexivity. Qed.
Lemma core_hart_h1_model_a0_is_mhartid : res_word ch1_run CH_AGREE = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.

(* ---------------------------------------------------------------------- *)
(* 3. WHAT DID NOT MOVE, and it is what makes §2 a HART result rather than  *)
(*    an artefact of building a different image.                           *)
(*                                                                         *)
(*    The prologue biases every hart's stack slot by PRIMARY_HART, so the   *)
(*    primary is slot 0 whichever hart it is (tools/vtest/vtest.S).  If     *)
(*    that arithmetic were wrong, sp on hart 1 would be a page off and the  *)
(*    first push would leave the declared region -- so these three fields   *)
(*    agreeing across the two harts is the check that the hart variant      *)
(*    changed the HART and nothing else.                                    *)
(* ---------------------------------------------------------------------- *)

Definition ch_unmoved : Z * Z * Z :=
  (0,            (* the slot: the primary is slot 0 on either hart       *)
   0x80091000,   (* sp: STACK_BASE + STACK_SIZE, the top of the region   *)
   0x80100000).  (* s11: RESULT_BASE                                     *)

Lemma core_hart_h0_qemu_unmoved :
  (cap_word core_hart_qemu_result CH_SLOT,
   cap_word core_hart_qemu_result CH_SP,
   cap_word core_hart_qemu_result CH_S11) = ch_unmoved.
Proof. reflexivity. Qed.

Lemma core_hart_h1_qemu_unmoved :
  (cap_word core_hart_hart1_qemu_result CH_SLOT,
   cap_word core_hart_hart1_qemu_result CH_SP,
   cap_word core_hart_hart1_qemu_result CH_S11) = ch_unmoved.
Proof. reflexivity. Qed.

Lemma core_hart_h1_model_unmoved :
  (res_word ch1_run CH_SLOT,
   res_word ch1_run CH_SP,
   res_word ch1_run CH_S11) = ch_unmoved.
Proof. solve_vtest ch_unmoved. Qed.

(* mstatus is the same on both harts and on both sides: SXL = UXL = 2 and
   everything else clear, which is ArchReset.board_regs' power-on
   obligation.  core_regs_mcsr established it of hart 0; this says the reset
   chain does the same for a hart that is not 0, which is not automatic --
   [cold_regs] takes the hart id as an argument and could have leaked it. *)
Lemma core_hart_h1_qemu_mstatus  : cap_word core_hart_hart1_qemu_result CH_MSTHI = 0xa.
Proof. reflexivity. Qed.
Lemma core_hart_h1_model_mstatus : res_word ch1_run CH_MSTHI = 0xa.
Proof. vm_cast_no_check (eq_refl 0xa). Qed.

(* ---------------------------------------------------------------------- *)
(* 4. FINDING 18 IS HART-INDEPENDENT.                                      *)
(*                                                                         *)
(*    a1 is the device-tree pointer.  The model writes a hardcoded 0x1000   *)
(*    ([init_boot_requirements] in rv64d.v); QEMU passes the real DTB       *)
(*    address, which moves with -m and with the image.  That is finding 18, *)
(*    recorded on hart 0 by core_regs_gpr.                                  *)
(*                                                                         *)
(*    What is new here: it is the SAME on hart 1 on both sides.  QEMU hands *)
(*    every hart the same pointer, and the model hands every hart the same  *)
(*    constant -- so the defect is in the VALUE and not in the per-hart     *)
(*    plumbing, which is worth knowing before anyone fixes it.              *)
(* ---------------------------------------------------------------------- *)

Definition ch_a1_model : Z := 0x1000.
Definition ch_a1_qemu  : Z := 0x87e00000.

Lemma core_hart_h1_model_a1 : res_word ch1_run CH_A1LO = ch_a1_model.
Proof. vm_cast_no_check (eq_refl ch_a1_model). Qed.
Lemma core_hart_h1_qemu_a1  :
  cap_word core_hart_hart1_qemu_result CH_A1LO = ch_a1_qemu.
Proof. reflexivity. Qed.
Lemma core_hart_a1_really_diverges : ch_a1_model <> ch_a1_qemu.
Proof. discriminate. Qed.

(* the same on hart 0, on both sides -- so neither machine varies it by hart *)
Lemma core_hart_h0_qemu_a1  : cap_word core_hart_qemu_result CH_A1LO = ch_a1_qemu.
Proof. reflexivity. Qed.
Lemma core_hart_h0_model_a1 : res_word ch0_run CH_A1LO = ch_a1_model.
Proof. vm_cast_no_check (eq_refl ch_a1_model). Qed.
