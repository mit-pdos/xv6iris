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

   WHAT IT FINDS, in the end, is that the model tracks both machines: the
   clock advances, mcycle advances with it, minstret advances independently,
   and the access widths agree.  Section 4 has those witnesses.

   IT DID NOT LOOK THAT WAY AT FIRST, and the mistake is the most useful
   thing in this file.  Read on the default runner -- [run_until], which
   steps [riscv_step false] -- the model's clock is frozen, and that was
   recorded as finding 27, "the model's clock never runs", classified as an
   UNSOUNDNESS.  It is nothing of the kind.  [RiscvLang.mnode_step]'s
   instruction-boundary rule is [exists tick : bool], so an execution with a
   moving clock is one the model ALLOWS; the harness had been resolving that
   choice the same way every time.  AN ABSENT WITNESS WAS READ AS AN ABSENT
   EXECUTION, in a suite whose entire question is whether the model allows
   what the hardware did.  Finding 27 is withdrawn.

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
(* 1. THE TWO BRANCHES OF THE BOUNDARY'S [exists tick].                    *)
(*                                                                         *)
(*    [VTest.run_until] steps [riscv_step false], so on THAT branch [mtime] *)
(*    holds its reset value however many instructions retire.  Section 4    *)
(*    runs the other branch, where it advances.  Both are executions of the *)
(*    model; neither is a finding about it.                                 *)
(*                                                                         *)
(*    These lemmas are kept because they say precisely what the DEFAULT     *)
(*    runner does, which a reader of any other test in this suite needs to  *)
(*    know -- every one of them is exhibited on the non-ticking branch, so  *)
(*    none of them observes elapsed time.  That is a default, not a limit:  *)
(*    a test that wants elapsed time asks for [run_until_tick].             *)
(* ---------------------------------------------------------------------- *)

Definition ct_model_advanced : Z := 0.   (* on the NON-TICKING branch      *)
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

(* The two branches answer differently, which is what a nondeterministic
   choice MEANS and is not a divergence from anything.  Named so that nobody
   reads it as one: the machines' column is [ct_qemu_advanced] /
   [ct_board_advanced] and section 4 shows the model matching it. *)
Lemma ct_branches_differ : ct_model_advanced <> ct_qemu_advanced.
Proof. discriminate. Qed.

(* The freeze on this branch stated so it cannot be read as an artefact of a
   short run: [mtime] is ZERO at both samples, because nothing on the
   non-ticking branch ever moves it. *)
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

(* ...and mcycle freezes WITH mtime on this branch rather than with
   minstret, which is the clock-derived set exactly. *)
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

(* ---------------------------------------------------------------------- *)
(* 4. CORRECTION TO §1: THE MODEL'S CLOCK CAN RUN.                         *)
(*                                                                         *)
(*    §1 above says the model's clock is frozen, and as a statement about   *)
(*    the MODEL that is WRONG.  It is a statement about [run_until], which  *)
(*    steps [riscv_step false].  [RiscvLang.mnode_step]'s boundary rule is  *)
(*                                                                         *)
(*      | Interface.Ret _ => exists tick : bool, m' = riscv_step tick /\ ...*)
(*                                                                         *)
(*    so the language quantifies EXISTENTIALLY over the tick at every       *)
(*    instruction boundary -- the sound weakening of the model [loop]'s     *)
(*    deterministic every-[plat_insns_per_tick] tick.  An execution with a  *)
(*    moving clock is one the model ALLOWS.  The harness had been resolving *)
(*    that choice the same way every time and never exhibiting the other    *)
(*    branch, and I read the absence of a witness as the absence of an      *)
(*    execution.                                                           *)
(*                                                                         *)
(*    [VTest.run_until_tick] takes the other branch, and the witnesses      *)
(*    below are what §1 should have asked for: the model DOES have a run in *)
(*    which mtime advances, mcycle advances with it, and the program        *)
(*    reports exactly what both machines reported.                          *)
(*                                                                         *)
(*    AND IT IS NOT A LIMITATION OF THE HARNESS EITHER.  A test that wants  *)
(*    to reason about elapsed time simply asks for the ticking branch, as   *)
(*    this section does; the capability was always there and nothing had    *)
(*    needed it.  [run_until] steps [riscv_step false] because that is a    *)
(*    convenient DEFAULT for tests whose subject is not time, not because   *)
(*    the other branch is unavailable.                                      *)
(*                                                                          *)
(*    So there is nothing left of §1 as a FINDING: finding 27 is withdrawn  *)
(*    outright.  What is worth writing down is the reasoning error -- an    *)
(*    absent witness was read as an absent execution, in a suite whose      *)
(*    entire question is whether the model ALLOWS what the hardware did.    *)
(* ---------------------------------------------------------------------- *)

Definition ct_tick_run : option mstate := run_until_tick 8000 (start clint_time_text).

Lemma ct_tick_completes : run_status_tick 8000 (start clint_time_text) = VDone.
Proof. vm_cast_no_check (eq_refl VDone). Qed.

(* THE CORRECTION: on the ticking branch the model advances the clock, which
   is what both machines do and what §1 reported it could not. *)
Lemma ct_tick_model_clock_ran : res_word ct_tick_run CT_ADV = ct_qemu_advanced.
Proof. vm_cast_no_check (eq_refl ct_qemu_advanced). Qed.

Lemma ct_tick_model_mcycle_ran : res_word ct_tick_run CT_CYCLEADV = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.

(* ...and it still never runs backwards, and the access widths still agree,
   so the ticking branch is not a different machine -- it is the same one
   with the clock allowed to move. *)
Lemma ct_tick_no_backwards : res_word ct_tick_run CT_NOBACK = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.
Lemma ct_tick_widths_agree : res_word ct_tick_run CT_BRACKET = 1.
Proof. vm_cast_no_check (eq_refl 1). Qed.
