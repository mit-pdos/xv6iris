(* CoreCsrwide.v -- FINDING 22's SEVEN, where the MODEL IS WIDER than the
   hardware.  QEMU only, and deliberately so.

   Source: tools/vtest/tests/core_csrwide.S (`machines=qemu`).
   Capture: CoreCsrwideGen.v.

   THE SPLIT.  core_csrprobe asks the question every machine can be asked;
   this asks the half only QEMU can.  On the VisionFive 2 all seven trap,
   which adds nothing -- QEMU already refuses them and the interesting
   column is the MODEL's -- so the board profile skips this test rather than
   reporting it as a failure.

   WHY THEY CANNOT SHARE A TEST WITH ANYTHING ELSE: [exec] cannot step
   `csrr mseccfg`.  It answers None, the harness reports VStuck, and the run
   stops at the first of the seven so every later probe in the same image
   goes unasked.

   AND IT REALLY IS THE MODEL, WHICH TOOK A NEW THEOREM TO ESTABLISH.  A
   bare [VStuck] means only that [exec] would not step, and [exec] declines
   on [Interface.Choose] -- the Sail monad's nondeterminism -- exactly as it
   declines where the relation is genuinely stuck.  [RiscvExec.exec_run_det]
   runs one way only, so [exec m s = None] on its own proves nothing.  This
   file used to assert "no transition" off exactly that, which was not
   justified at the time.

   [VExecStuck.v] closes it: [exec_r] is [exec] with its failure clause
   split into [ENoStep] and [EChoice], and

     exec_r_no_step : exec_r m s = inr ENoStep -> forall x s', ~ run m s x s'

   is the converse the tree did not have.  MEASURED HERE: [stuck_why]
   answers [Some ENoStep], so by that theorem the RELATION has no
   transition at the state this run reaches.  The original claim was right;
   what was missing was any way to know it.

   SO FINDING 32 STANDS, and it now says something checkable.  Finding 22
   records the model as "implemented, read successfully" on these seven
   CSRs; the model does not read [mseccfg] at all.  Compare finding 25,
   where `sc.w` does not EVALUATE because [execute_STORECON] goes through
   opaque platform axioms -- that one is still an [exec] limit and has not
   been given this treatment. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest CoreCsrwideGen.
Local Open Scope Z_scope.

Definition cw_slot (i : nat) : nat := (8 + 4 * i)%nat.
Definition CW_CONTROL : nat := cw_slot 7.
Definition CW_TRAPN   : nat := 2048.

Definition cw_start : mstate := start core_csrwide_text.

(* ---------------------------------------------------------------------- *)
(* 1. QEMU REFUSES ALL SEVEN, and the control says the handler ran.        *)
(* ---------------------------------------------------------------------- *)

Definition cw_qemu : Z * Z * Z * Z * Z * Z * Z * Z :=
  (1, 1, 1, 1, 1, 1, 1,    (* mseccfg mstateen0 sstateen0 scountovf
                              mcyclecfg minstretcfg ssp -- all trap *)
   1).                     (* the control: an all-zeros instruction word *)

Lemma core_csrwide_qemu :
  (cap_word core_csrwide_qemu_result (cw_slot 0),
   cap_word core_csrwide_qemu_result (cw_slot 1),
   cap_word core_csrwide_qemu_result (cw_slot 2),
   cap_word core_csrwide_qemu_result (cw_slot 3),
   cap_word core_csrwide_qemu_result (cw_slot 4),
   cap_word core_csrwide_qemu_result (cw_slot 5),
   cap_word core_csrwide_qemu_result (cw_slot 6),
   cap_word core_csrwide_qemu_result CW_CONTROL) = cw_qemu.
Proof. reflexivity. Qed.

(* eight traps: the seven CSRs and the control.  This is what says QEMU
   really refused each one rather than the run ending early. *)
Lemma core_csrwide_qemu_traps_eight :
  cap_word core_csrwide_qemu_result CW_TRAPN = 8.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. [exec] CANNOT STEP THE FIRST OF THEM.                                *)
(*                                                                         *)
(*    Not VBudget (a trap loop eating the budget, which is what an          *)
(*    illegal-instruction refusal would look like -- see ClintMsip.v) and   *)
(*    not VDone.  VStuck: [exec] returned None -- see the header for what   *)
(*    that does and does not establish.                                     *)
(*                                                                         *)
(*    0x80000078 is `csrr t2,0x747`, checked against                        *)
(*    `riscv64-linux-gnu-objdump -d tools/vtest/build/core_csrwide.elf`,    *)
(*    which is what makes this a refused CSR and not an address-            *)
(*    materialising load that left a declared region.                       *)
(* ---------------------------------------------------------------------- *)

Lemma core_csrwide_exec_stuck : run_status 4000 cw_start = VStuck.
Proof. vm_cast_no_check (eq_refl VStuck). Qed.

(* ...and it is REAL stuckness, not a [Choose] the interpreter declined. *)
Lemma core_csrwide_stuck_why : stuck_why 4000 cw_start = Some ENoStep.
Proof. vm_cast_no_check (eq_refl (Some ENoStep)). Qed.

(* THE STATEMENT ABOUT THE MODEL, which [VStuck] alone could not support:
   the run reaches a state at which the RELATION has no transition. *)
Corollary core_csrwide_model_really_stuck :
  exists s0, forall x s', ~ run (riscv_step false) s0 x s'.
Proof. exact (stuck_why_no_step _ _ core_csrwide_stuck_why). Qed.

Lemma core_csrwide_exec_stuck_at : stuck_pc 4000 cw_start = 0x80000078.
Proof. vm_cast_no_check (eq_refl 0x80000078). Qed.

(* ...so the model publishes nothing at all, where QEMU published a full
   table.  [result_of] of a stuck run is the empty list, which is a
   different thing from a run that finished with zeros. *)
Lemma core_csrwide_model_publishes_nothing :
  result_of (run_until 4000 cw_start) = [].
Proof. vm_cast_no_check (eq_refl (@nil Z)). Qed.

(* The divergence, pinned in the shape README.md prescribes.  Green today;
   goes RED the day the model gains a transition here, which is exactly when
   this file and finding 22 should be revisited together. *)
Definition cw_model_status : Z := 0.   (* nothing published *)
Definition cw_qemu_status  : Z := 2.   (* ran to the end    *)

Lemma core_csrwide_qemu_finished :
  cap_word core_csrwide_qemu_result 4 = cw_qemu_status.
Proof. reflexivity. Qed.

Lemma core_csrwide_really_diverges : cw_model_status <> cw_qemu_status.
Proof. discriminate. Qed.
