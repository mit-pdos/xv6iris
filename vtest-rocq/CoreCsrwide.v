(* CoreCsrwide.v -- FINDING 22's SEVEN, where the MODEL IS WIDER than the
   hardware.  QEMU only, and deliberately so.

   Source: tools/vtest/tests/core_csrwide.S (`machines=qemu`).
   Capture: CoreCsrwideGen.v.

   THE SPLIT.  core_csrprobe asks the question every machine can be asked;
   this asks the half only QEMU can.  On the VisionFive 2 all seven trap,
   which adds nothing -- QEMU already refuses them and the interesting
   column is the MODEL's -- so the board profile skips this test rather than
   reporting it as a failure.

   WHY THEY CANNOT SHARE A TEST WITH ANYTHING ELSE, and this is the finding:
   in the model `csrr mseccfg` has NO TRANSITION.  [exec] answers None and
   the harness reports VStuck, so the run stops at the first of the seven
   and every later probe in the same image goes unasked.  Finding 22 records
   the model as IMPLEMENTING these CSRs -- "implemented, read successfully"
   -- and for the interpreter this suite runs, that is not what happens: it
   neither answers nor refuses.

   That is a THIRD outcome, and the suite's vocabulary already has a name
   for each: a machine that answers, a machine that traps, and a model with
   no transition.  Compare finding 25, where `sc.w` does not evaluate
   because [execute_STORECON] goes through opaque platform axioms; this is
   the same class of limit, in the CSR file.  Whether finding 22's "read
   successfully" was measured some other way, or has rotted, is worth
   settling before README.md's open decision is answered -- because the
   decision was framed on the belief that the model ANSWERS here. *)
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
(* 2. THE MODEL HAS NO TRANSITION FOR THE FIRST OF THEM.                   *)
(*                                                                         *)
(*    Not VBudget (a trap loop eating the budget, which is what an          *)
(*    illegal-instruction refusal would look like -- see ClintMsip.v) and   *)
(*    not VDone.  VStuck: [exec] returned None.                             *)
(*                                                                         *)
(*    0x80000078 is `csrr t2,0x747`, checked against                        *)
(*    `riscv64-linux-gnu-objdump -d tools/vtest/build/core_csrwide.elf`,    *)
(*    which is what makes this a refused CSR and not an address-            *)
(*    materialising load that left a declared region.                       *)
(* ---------------------------------------------------------------------- *)

Lemma core_csrwide_model_stuck : run_status 4000 cw_start = VStuck.
Proof. vm_cast_no_check (eq_refl VStuck). Qed.

Lemma core_csrwide_model_stuck_at : stuck_pc 4000 cw_start = 0x80000078.
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
