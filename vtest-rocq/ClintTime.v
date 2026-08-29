(* ClintTime.v -- THE CLOCK, against both machines.

   Source: tools/vtest/tests/clint_time.S.
   Captures: ClintTimeGen.v (QEMU virt) and ClintTimeHwGen.v (a StarFive
   VisionFive 2, over JTAG).

   THIS IS THE FIRST TEST IN THE SUITE TO TOUCH THE CLINT.  The UART, the
   PLIC and the disk live in DevModel.v, a device fabric beside the byte
   memory that VSched steps; the CLINT does not.  The Sail model dispatches
   that window itself -- [plat_clint_base] = 0x0200_0000, [plat_clint_size]
   = 0xC_0000, with clint_load / clint_store in rv64d.v -- so an access here
   never reaches the interpreter's device fabric, and until this file
   nothing had ever asked whether it behaves.

   WHAT IT FINDS is not a decode bug.  It is that THE MODEL'S CLOCK DOES NOT
   RUN, so two reads of [mtime] a thousand instructions apart return the
   same value, and BOTH machines say they must not.  That is a hardware
   behaviour with no model execution -- the unsound direction -- and it sits
   beside finding 24 (the sequentially-consistent memory model) as a place
   where the model is not merely narrower than the machine but wrong about
   it.

   The test is written so that this is VISIBLE rather than merely raw.  The
   [mtime] words themselves can never be compared: they differ between two
   QEMU runs as much as between QEMU and the board, so they are recorded and
   pinned, not equated.  What IS compared is the DERIVED question -- did the
   clock advance? -- which both machines answer 1 and the model answers 0. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest ClintTimeGen ClintTimeHwGen.
Local Open Scope Z_scope.

(* the offsets clint_time.S publishes at; see its header *)
Definition CT_T0LO     : nat := 8.
Definition CT_T1LO     : nat := 16.
Definition CT_ADV      : nat := 24.
Definition CT_NOBACK   : nat := 28.
Definition CT_BRACKET  : nat := 40.
Definition CT_INSTRADV : nat := 48.
Definition CT_CYCLEADV : nat := 56.

Definition ct_run    : option mstate := run_until 8000 (start clint_time_text).
Definition ct_hw_run : option mstate :=
  run_until 8000 (start_hart clint_time_hw_primary_hart clint_time_hw_text).

(* The program finishes on the model on both images -- so everything below
   is a statement about a machine that ran to completion, not about one that
   got stuck in the CLINT window.  THE MODEL DECODES [mtime] AT BOTH WIDTHS;
   that is the first positive result here and it is worth having. *)
Lemma ct_model_completes    : run_status 8000 (start clint_time_text) = VDone.
Proof. vm_cast_no_check (eq_refl VDone). Qed.
Lemma ct_hw_model_completes :
  run_status 8000 (start_hart clint_time_hw_primary_hart clint_time_hw_text) = VDone.
Proof. vm_cast_no_check (eq_refl VDone). Qed.

(* ---------------------------------------------------------------------- *)
(* 1. THE FINDING: the clock does not advance in the model, and does on    *)
(*    both machines.                                                       *)
(*                                                                         *)
(*    [VTest.run_until] steps [riscv_step false] -- the argument is the     *)
(*    CLOCK TICK, and the harness never passes true.  So [mtime] holds its  *)
(*    reset value for the whole run however many instructions retire.       *)
(*                                                                         *)
(*    Recorded in the shape tools/vtest/README.md prescribes: pinned on     *)
(*    BOTH sides and proved unequal, so it is green today and goes RED the  *)
(*    day the harness or the model starts ticking -- which is exactly when  *)
(*    this file should be revisited.                                       *)
(* ---------------------------------------------------------------------- *)

Definition ct_model_advanced : Z := 0.   (* the model: the clock is frozen *)
Definition ct_qemu_advanced  : Z := 1.   (* QEMU virt                      *)
Definition ct_board_advanced : Z := 1.   (* VisionFive 2                   *)

Lemma ct_model_clock_frozen : res_word ct_run CT_ADV = ct_model_advanced.
Proof. vm_cast_no_check (eq_refl ct_model_advanced). Qed.

(* ...and on the BOARD's own image too, so the freeze is a property of the
   model and not of the particular program QEMU ran. *)
Lemma ct_hw_model_clock_frozen : res_word ct_hw_run CT_ADV = ct_model_advanced.
Proof. vm_cast_no_check (eq_refl ct_model_advanced). Qed.

Lemma ct_qemu_clock_ran : cap_word clint_time_qemu_result CT_ADV = ct_qemu_advanced.
Proof. reflexivity. Qed.

Lemma ct_board_clock_ran : cap_word clint_time_hw_result CT_ADV = ct_board_advanced.
Proof. reflexivity. Qed.

(* TWO INDEPENDENT MACHINES SAY THE SAME THING, which is what makes this a
   fact about the model rather than about a timebase. *)
Lemma ct_clock_really_diverges : ct_model_advanced <> ct_qemu_advanced.
Proof. discriminate. Qed.

Lemma ct_board_clock_really_diverges : ct_model_advanced <> ct_board_advanced.
Proof. discriminate. Qed.

(* The freeze stated so it cannot be read as an artefact of a short run.
   The model's [mtime] is not merely equal at the two samples, it is ZERO at
   both: the reset chain leaves it there and nothing ever moves it. *)
Lemma ct_model_mtime_starts_at_zero : res_word ct_run CT_T0LO = 0.
Proof. vm_cast_no_check (eq_refl 0). Qed.
Lemma ct_model_mtime_stays_at_zero  : res_word ct_run CT_T1LO = 0.
Proof. vm_cast_no_check (eq_refl 0). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE CONTROL, and it is what makes §1 attributable to the CLOCK.      *)
(*                                                                         *)
(*    [minstret] advances in the model exactly as it does on both machines, *)
(*    so the frozen [mtime] is not "counters are unimplemented" and not     *)
(*    "the program did not run"; it is the clock alone.  [mcycle] is driven *)
(*    by that same clock and freezes WITH it, which is the other half: the  *)
(*    model freezes exactly the clock-derived counters, not a random        *)
(*    subset.                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma ct_model_minstret_advances    : res_word ct_run    CT_INSTRADV = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.
Lemma ct_hw_model_minstret_advances : res_word ct_hw_run CT_INSTRADV = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.
Lemma ct_qemu_minstret_advances  : cap_word clint_time_qemu_result CT_INSTRADV = 1.
Proof. reflexivity. Qed.
Lemma ct_board_minstret_advances : cap_word clint_time_hw_result   CT_INSTRADV = 1.
Proof. reflexivity. Qed.

Lemma ct_model_mcycle_frozen    : res_word ct_run    CT_CYCLEADV = 0.
Proof. vm_cast_no_check (eq_refl 0). Qed.
Lemma ct_hw_model_mcycle_frozen : res_word ct_hw_run CT_CYCLEADV = 0.
Proof. vm_cast_no_check (eq_refl 0). Qed.
Lemma ct_qemu_mcycle_ran  : cap_word clint_time_qemu_result CT_CYCLEADV = 1.
Proof. reflexivity. Qed.
Lemma ct_board_mcycle_ran : cap_word clint_time_hw_result   CT_CYCLEADV = 1.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. WHAT AGREES.  Positive results are worth as much, and each of these  *)
(*    is a way the CLINT model could have been wrong and is not.           *)
(* ---------------------------------------------------------------------- *)

(* The counter never runs BACKWARDS -- true of the model vacuously and of
   both machines substantively.  This is the check that would catch a
   64-bit counter assembled from two 32-bit halves in the wrong order. *)
Lemma ct_model_no_backwards    : res_word ct_run    CT_NOBACK = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.
Lemma ct_hw_model_no_backwards : res_word ct_hw_run CT_NOBACK = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.
Lemma ct_qemu_no_backwards  : cap_word clint_time_qemu_result CT_NOBACK = 1.
Proof. reflexivity. Qed.
Lemma ct_board_no_backwards : cap_word clint_time_hw_result   CT_NOBACK = 1.
Proof. reflexivity. Qed.

(* THE ACCESS WIDTHS AGREE.  [mtime] read as two 4-byte halves (MTIME_BASE
   / MTIME_BASE_HI) reassembles to a value between an 8-byte read taken
   before it and one taken after -- on the model and on both machines.
   This is the one property of a MOVING counter that survives being
   compared across access widths, and on the model it is not vacuous: the
   model answers all three reads, so the widths really are exercised.  It
   is also the reason §1 can be trusted -- a model that simply refused the
   4-byte halves would have failed here instead. *)
Lemma ct_model_widths_agree    : res_word ct_run    CT_BRACKET = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.
Lemma ct_hw_model_widths_agree : res_word ct_hw_run CT_BRACKET = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.
Lemma ct_qemu_widths_agree  : cap_word clint_time_qemu_result CT_BRACKET = 1.
Proof. reflexivity. Qed.
Lemma ct_board_widths_agree : cap_word clint_time_hw_result   CT_BRACKET = 1.
Proof. reflexivity. Qed.
