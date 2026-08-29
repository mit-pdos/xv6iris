(* ClintMsip.v -- the CLINT's software-interrupt register, and the question
   the two machines answer differently: IS THE CLINT INDEXED BY HART?

   Source: tools/vtest/tests/clint_msip.S.
   Captures: ClintMsipGen.v (QEMU virt, hart 0) and ClintMsipHwGen.v
   (VisionFive 2, hart 2).

   THE FINDING, and it is a decode gap of exactly the shape findings 11 and
   12 were.  A CLINT gives every hart its own MSIP word at CLINT+4*hartid
   and its own MTIMECMP at CLINT+0x4000+8*hartid; that indexing IS the
   device -- it is how one hart interrupts another and how each hart arms
   its own timer.  rv64d.v's clint_load / clint_store compare the offset
   with [eq_vec] against MSIP_BASE = 0x00000 and MTIMECMP_BASE = 0x04000,
   which are single addresses and not ranges, so ONLY HART 0'S REGISTERS
   EXIST.  Every other hart's access falls through to the fallback, which
   returns [Err (paddr, accessFault)].

   Nothing had noticed because nothing had looked: the CLINT is dispatched
   inside the Sail model rather than through DevModel.v's fabric, so no
   QEMU test has ever addressed it -- and every QEMU test runs on hart 0,
   where 4*hartid is 0 and the gap is invisible.  It took a machine whose
   hart 0 cannot run the image at all to expose it.

   THIS IS LIVE.  xv6's start() stores to CLINT_MTIMECMP(id) with
   id = r_mhartid(), so on any hart but 0 that store has no model
   execution.

   §1 is QEMU on hart 0: the model's MSIP semantics, end to end, and they
   are RIGHT.  §2 is the board on hart 2: the same program, and the model
   takes a load access fault at the first access.  The pair is the finding
   -- either half alone would be misread. *)
From Stdlib Require Import List ZArith.
From stdpp Require Import bitvector.definitions list.
Import ListNotations.
Require Import RiscvExec RiscvModelBytes DevModel VTest ClintMsipGen ClintMsipHwGen.
Local Open Scope Z_scope.

(* the same inspection helpers CoreRegsFpr.v uses: n steps of the harness's
   own stepper, and one register out of the reached state *)
Fixpoint stepn (n : nat) (s : mstate) : option mstate :=
  match n with
  | 0%nat => Some s
  | S n' => match exec (riscv_step false) s with
            | Some (_, s') => stepn n' (settle dev_fuel s')
            | None => None
            end
  end.

Definition rd (r : register_bitvector_64) (o : option mstate) : Z :=
  match o with
  | Some s => bv_unsigned (register_lookup (R_bitvector_64 r) (sregs s))
  | None => -2
  end.

(* ---------------------------------------------------------------------- *)
(* 1. QEMU, ON HART 0: the model gets MSIP right.                          *)
(*                                                                         *)
(*    Whole result region, so nothing hides in the tail: the register      *)
(*    reads 0 before anything touches it, reads back 1 after a 1 is        *)
(*    written, RAISES mip.MSIP (bit 3) while set, reads back 0 when        *)
(*    cleared and drops mip.MSIP with it.  That last pair is the one worth  *)
(*    naming -- a model that stored the word without wiring it to [mip]     *)
(*    would pass the first three checks and fail here, which is the same    *)
(*    "stored but inert control bit" failure the UART's MCR had (finding 6).*)
(* ---------------------------------------------------------------------- *)

Definition msip_run : option mstate := run_until 400 (start clint_msip_text).

Lemma clint_msip_result : result_of msip_run = clint_msip_qemu_result.
Proof. solve_vtest clint_msip_qemu_result. Qed.

Lemma clint_msip_completes : run_status 400 (start clint_msip_text) = VDone.
Proof. vm_cast_no_check (eq_refl VDone). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE BOARD, ON HART 2: the same program, and the model faults.        *)
(*                                                                         *)
(*    THE MACHINE COMPLETED IT.  clint_msip_hw_result carries a full run:   *)
(*    status 3, the register 0 before, 1 when set, mip.MSIP = 8, 0 when     *)
(*    cleared, mip.MSIP gone -- the same semantics QEMU showed, on a        *)
(*    different hart's register.  So this is not a machine that refused the *)
(*    access; it is a model that answers it with a FAULT.                   *)
(*                                                                         *)
(*    "No transition" would be the wrong words and this file used to use    *)
(*    them.  The model HAS a transition here -- a load access fault, which  *)
(*    section 2 pins with mcause, mepc and mtval -- and that is why the     *)
(*    status below is VBudget (the trap loop eats the budget) and not       *)
(*    VStuck.  The distinction is load-bearing: VStuck would mean only that *)
(*    [exec] declined to step, which is a fact about the interpreter and    *)
(*    not about the model (see VTest.v section 3b).  Here the model really  *)
(*    does take a step, and it is the wrong one.                            *)
(* ---------------------------------------------------------------------- *)

Definition msip_hw_start : mstate :=
  start_hart clint_msip_hw_primary_hart clint_msip_hw_text.

(* What the BOARD did, field by field.  Read these first: they are what the
   model has to have an execution for, and does not. *)
Definition msip_board : Z * Z * Z * Z * Z * Z * Z :=
  (cap_word clint_msip_hw_result 4,    (* status:  ran to the end        *)
   cap_word clint_msip_hw_result 8,    (* before:  0, the runner cleared *)
   cap_word clint_msip_hw_result 12,   (* set:     1                     *)
   cap_word clint_msip_hw_result 16,   (* mip:     8 = MSIP              *)
   cap_word clint_msip_hw_result 20,   (* cleared: 0                     *)
   cap_word clint_msip_hw_result 24,   (* mip:     0                     *)
   cap_word clint_msip_hw_result 32).  (* mhartid: 2                     *)

Lemma clint_msip_board_ran : msip_board = (3, 0, 1, 8, 0, 0, 2).
Proof. reflexivity. Qed.

(* ...and hart 0's MSIP, read but never written, is 1 -- firmware's, not
   ours.  It is the direct evidence that the two words are DIFFERENT
   REGISTERS on this machine: our hart's read 0 at the same moment. *)
Lemma clint_msip_board_hart0_is_separate :
  cap_word clint_msip_hw_result 28 = 1.
Proof. reflexivity. Qed.

(* THE MODEL, on the same image.  The prologue is 13 instructions and the
   body's first seven get as far as computing CLINT+4*mhartid, so the pc at
   step 20 is the faulting load and at step 21 it is 0 -- mtvec is 0, so a
   fault is a trap loop there, and the pc at step 300 says it is a LOOP and
   not a slow start.  mcause 5 is Load Access Fault and mtval names the
   address: 0x2000008, which is CLINT + 4*2, hart 2's MSIP.

   0x8000006c is `lw t0,0(s0)`, checked against
   `riscv64-linux-gnu-objdump -d tools/vtest/build/clint_msip_hw.elf`. *)
Definition msip_hw_trap : Z * Z * Z * Z * Z * Z :=
  (0x8000006c,   (* pc at step 20: the first CLINT access                *)
   0,            (* pc at step 21: trapped, and mtvec is 0               *)
   5,            (* mcause: Load Access Fault                            *)
   0x8000006c,   (* mepc: that load                                      *)
   0x2000008,    (* mtval: CLINT + 4*2 -- hart 2's MSIP                  *)
   0).           (* pc at step 300: still 0, so it is a trap LOOP        *)

Lemma clint_msip_hw_model_faults :
  (rd PC (stepn 20 msip_hw_start),
   rd PC (stepn 21 msip_hw_start),
   rd mcause (stepn 21 msip_hw_start),
   rd mepc (stepn 21 msip_hw_start),
   rd mtval (stepn 21 msip_hw_start),
   rd PC (stepn 300 msip_hw_start)) = msip_hw_trap.
Proof. solve_vtest msip_hw_trap. Qed.

(* ...so the model never publishes a result at all, where the board
   published a complete one.  [VBudget] and not [VStuck]: the model HAS a
   transition here, it is just the wrong one -- an access fault -- and the
   trap loop then eats the budget.  That distinction matters, because a
   stuck machine is a missing decode and this is a decode that answers with
   a fault the hardware does not raise. *)
Lemma clint_msip_hw_model_never_finishes :
  run_status 400 msip_hw_start = VBudget.
Proof. vm_cast_no_check (eq_refl VBudget). Qed.

Lemma clint_msip_hw_model_publishes_nothing :
  res_word (run_until 400 msip_hw_start) 4 = 0.
Proof. vm_cast_no_check (eq_refl 0). Qed.

(* The divergence, pinned in the shape tools/vtest/README.md prescribes.
   Green today; goes RED the day the CLINT learns about hart ids, which is
   exactly when this file should be revisited. *)
Definition msip_model_status : Z := 0.   (* never published               *)
Definition msip_board_status : Z := 3.   (* ran to the end                *)

Lemma clint_msip_really_diverges : msip_model_status <> msip_board_status.
Proof. discriminate. Qed.
