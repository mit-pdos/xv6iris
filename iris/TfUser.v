(* ===================================================================== *)
(* TfUser.v -- THE USER-VISIBLE HALF OF A TRAPFRAME, as an equivalence on *)
(* the word list.                                                          *)
(*                                                                         *)
(* The RESUME state a trapframe determines reads exactly two things out of *)
(* the 36-word list: the epc word (index [tf_epc_idx] = 3) and the 31      *)
(* restorable registers (indices 5..35, ProcGeom.v's layout -- word 4+k is *)
(* x_k).  The four KERNEL words (0 kernel_satp, 1 kernel_sp, 2             *)
(* kernel_trap, 4 kernel_hartid) are [prepare_return]'s to re-arm on the   *)
(* way out, so ANY equation the trap round states about the resume         *)
(* trapframe is an equation UP TO THOSE FOUR.  [tf_ueq] is that relation,  *)
(* and [prepare_return_tf_ueq] (SpecPrepareReturn.v) is the one fact that  *)
(* makes it the right one.                                                 *)
(*                                                                         *)
(* PURE, and deliberately at the bottom of the user tier: only ProcGeom.v  *)
(* (for the index names) and the stdpp/mword vocabulary.  The projection   *)
(* congruences live where their projections do -- [tf_ueq_resume_pc] in    *)
(* UexecSlot.v, [tf_ueq_resume_gpr0] in UexecRet.v, [tf_ueq_num] in        *)
(* UsysMemOk.v.                                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvLang.
Require Import ProcGeom.     (* [tf_epc_idx] / [TFWORDS] *)
Local Open Scope Z_scope.

(* the words the RESUME state reads: epc (3) and the 31 restorable registers
   (5..35).  The four KERNEL words (0,1,2,4) are prepare_return's to re-arm,
   so any resume-trapframe equation the trap round states is up to this. *)
Definition tf_ueq (tf tf' : list (mword 64)) : Prop :=
  tf !!! tf_epc_idx = tf' !!! tf_epc_idx
  /\ forall i : nat, (5 <= i <= 35)%nat -> tf !!! i = tf' !!! i.

Lemma tf_ueq_refl (tf : list (mword 64)) : tf_ueq tf tf.
Proof. split; [ reflexivity | intros i _; reflexivity ]. Qed.

Lemma tf_ueq_sym (tf tf' : list (mword 64)) : tf_ueq tf tf' -> tf_ueq tf' tf.
Proof.
  intros [He Hg]. split; [ symmetry; exact He | ].
  intros i Hi. symmetry. exact (Hg i Hi).
Qed.

Lemma tf_ueq_trans (tf tf' tf'' : list (mword 64)) :
  tf_ueq tf tf' -> tf_ueq tf' tf'' -> tf_ueq tf tf''.
Proof.
  intros [He Hg] [He' Hg']. split; [ exact (eq_trans He He') | ].
  intros i Hi. exact (eq_trans (Hg i Hi) (Hg' i Hi)).
Qed.

(* the epc component, as a reader *)
Lemma tf_ueq_epc (tf tf' : list (mword 64)) :
  tf_ueq tf tf' -> tf !!! tf_epc_idx = tf' !!! tf_epc_idx.
Proof. intros [He _]. exact He. Qed.

(* ------------------------------------------------------------------- *)
(* An insert at an index OUTSIDE {3} u [5,35] -- i.e. at one of the four *)
(* kernel words -- is invisible to [tf_ueq], on either side.             *)
(* ------------------------------------------------------------------- *)
Lemma tf_ueq_insert_r (tf tf' : list (mword 64)) (i : nat) (v : mword 64) :
  i <> tf_epc_idx -> (i < 5 \/ 35 < i)%nat ->
  tf_ueq tf tf' -> tf_ueq tf (<[i := v]> tf').
Proof.
  intros Hne Hout [He Hg]. split.
  - rewrite list_lookup_total_insert_ne; [ exact He | exact Hne ].
  - intros j Hj. rewrite list_lookup_total_insert_ne; [ exact (Hg j Hj) | lia ].
Qed.

Lemma tf_ueq_insert_l (tf tf' : list (mword 64)) (i : nat) (v : mword 64) :
  i <> tf_epc_idx -> (i < 5 \/ 35 < i)%nat ->
  tf_ueq tf tf' -> tf_ueq (<[i := v]> tf) tf'.
Proof.
  intros Hne Hout H.
  apply tf_ueq_sym. apply tf_ueq_insert_r; [ exact Hne | exact Hout | ].
  apply tf_ueq_sym. exact H.
Qed.
