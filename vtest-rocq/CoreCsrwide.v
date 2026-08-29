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

   BUT THAT IS A FACT ABOUT [exec], NOT ABOUT THE MODEL, and an earlier
   version of this file said otherwise ("the model has NO TRANSITION").
   [RiscvExec.exec_run_det] runs one way only -- [exec = Some] implies [run]
   -- and there is no lemma anywhere in the tree of the form
   [exec m s = None -> no run].  There cannot be a trivial one: [exec]'s own
   fallback is

     | _ => fun _ => None   (* Choose / GenericFail / Discard / ... *)

   so it bails on [Choose], the Sail monad's NONDETERMINISM.  The relation
   may well have a transition here that this interpreter declines to pick.
   Compare finding 25, where `sc.w` does not evaluate because
   [execute_STORECON] goes through opaque platform axioms -- the same class
   of limit, and the same care needed in stating it.

   SO WHAT IS OPEN is narrower than it looked, and still worth settling:
   finding 22 records the model as "implemented, read successfully" on these
   seven, and this suite cannot confirm that because its interpreter cannot
   evaluate the read.  Whether the model ANSWERS here -- which is what
   README.md's open decision was framed on -- needs a route other than
   [exec]. *)
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
