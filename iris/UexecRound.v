(* ===================================================================== *)
(* UexecRound.v -- THE TRAP ROUND, as a relation on the user-visible      *)
(* state.                                                                 *)
(*                                                                        *)
(* One round of the kernel's trap loop takes the process from the state   *)
(* it trapped in to the state the sret resumes it at.  [uround_ok] is     *)
(* WHAT THAT ROUND MAY HAVE DONE, keyed -- like the dispatch itself --    *)
(* on whether the cause is an ecall:                                      *)
(*                                                                        *)
(*   ecall     -- either the entry was [exec] (which never returns to     *)
(*                this process's WP at all: the new program's slot is     *)
(*                MINTED, so this row says nothing), or the round bumped  *)
(*                the trapframe (a0 := some return value, epc += 4) and   *)
(*                moved the user image/permission map by exactly what     *)
(*                [UsysMemOk.usys_mem_ok] allows for the entry's number.  *)
(*   anything  -- an interrupt, a page fault, an unexpected scause: the   *)
(*   else        resume state is the trapped state, on the nose.          *)
(*                                                                        *)
(* WHY THE BUMP IS STATED ON THE RESUME PROJECTIONS and not as            *)
(* [tf' = bump_tf tf r]: the list the sret actually resumes from is       *)
(* [prepare_return_tf] of the bumped one, which differs in the four       *)
(* KERNEL words.  [tf_resume_gpr0] / [tf_resume_pc] do not read those, so *)
(* the projection form is both what is provable and what the slot's key   *)
(* needs.  [TfUser.tf_ueq] is the corresponding equivalence, and          *)
(* [uround_ok_ueq_l] / [uround_ok_ueq_r] are its congruences here -- so a *)
(* kernel proof may state the round at whichever of the two lists it      *)
(* happens to hold.                                                       *)
(*                                                                        *)
(* PURE.  See claude-notes/projects/user-wp-slot.md SS4a (J1a).           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExtras.
Require Import RegFile.
Require Import ProcGeom.     (* [tf_epc_idx] *)
Require Import TfUser.       (* [tf_ueq] *)
Require Import UserPerm.     (* [uperm] *)
Require Import UsysMemOk.    (* [usys_num] / [usys_mem_ok] / [uecall_scause] *)
Require Import UexecSlot.    (* [tf_w] / [tf_resume_pc] / [tf_ueq_resume_pc] *)
Require Import UexecRet.     (* [tf_resume_gpr0] / [tf_ueq_resume_gpr0] *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(* SS1 The two shapes a round can leave the trapframe in.                  *)
(* ===================================================================== *)

(* TRANSPARENT: the resume state IS the trapped state. *)
Definition uround_id_ok (tf tf' : list (mword 64)) : Prop :=
  tf_resume_gpr0 tf' = tf_resume_gpr0 tf /\ tf_resume_pc tf' = tf_resume_pc tf.

(* BUMPED: a0 := the return value, pc past the ecall.  The right-hand sides
   are [UexecRet.tf_resume_gpr_bump] / [tf_resume_pc_bump]'s verbatim -- those
   two lemmas are the one-step dischargers. *)
Definition uround_bump_ok (tf tf' : list (mword 64)) (r : mword 64) : Prop :=
  tf_resume_gpr0 tf' = <[Regidx (mword_of_int 10) := r]> (tf_resume_gpr0 tf)
  /\ tf_resume_pc tf' = ret_pc (add_vec_int (tf_w tf tf_epc_idx) 4).

(* ===================================================================== *)
(* SS2 THE ROUND.                                                          *)
(* ===================================================================== *)
Definition uround_ok (sc : mword 64)
    (tf : list (mword 64)) (M : gmap Z (bv 8)) (pi : gmap (mword 27) uperm)
    (tf' : list (mword 64)) (M' : gmap Z (bv 8)) (pi' : gmap (mword 27) uperm) : Prop :=
  if decide (sc = uecall_scause) then
    usys_num tf = USYS_exec
    \/ exists r : mword 64,
         uround_bump_ok tf tf' r
         /\ usys_mem_ok (usys_num tf) tf r M pi M' pi'
  else uround_id_ok tf tf' /\ M' = M /\ pi' = pi.

(* ===================================================================== *)
(* SS3 The readers -- unpack the [decide].                                 *)
(* ===================================================================== *)
Lemma uround_ok_ecall (tf : list (mword 64)) (M M' : gmap Z (bv 8))
    (pi pi' : gmap (mword 27) uperm) (tf' : list (mword 64)) :
  uround_ok uecall_scause tf M pi tf' M' pi' ->
  usys_num tf = USYS_exec
  \/ exists r : mword 64,
       uround_bump_ok tf tf' r
       /\ usys_mem_ok (usys_num tf) tf r M pi M' pi'.
Proof.
  unfold uround_ok.
  destruct (decide (uecall_scause = uecall_scause)) as [_ | Hne];
    [ intros H; exact H | contradiction (Hne eq_refl) ].
Qed.

Lemma uround_ok_transparent (sc : mword 64) (tf : list (mword 64))
    (M M' : gmap Z (bv 8)) (pi pi' : gmap (mword 27) uperm)
    (tf' : list (mword 64)) :
  sc <> uecall_scause ->
  uround_ok sc tf M pi tf' M' pi' ->
  uround_id_ok tf tf' /\ M' = M /\ pi' = pi.
Proof.
  intros Hne. unfold uround_ok.
  destruct (decide (sc = uecall_scause)) as [Heq | _];
    [ contradiction (Hne Heq) | intros H; exact H ].
Qed.

(* ===================================================================== *)
(* SS4 THE CONGRUENCES.  Every reader of [tf] in the relation -- the       *)
(* number (word 21), [usys_mem_ok]'s window bases (words 14/15,            *)
(* [UsysMemOk.usys_mem_ok_ueq]), the epc word (3) and the restored file    *)
(* (words 5..35) -- is inside [tf_ueq]'s reach, and so is every reader of  *)
(* [tf'].                                                                  *)
(* ===================================================================== *)
Lemma uround_ok_ueq_l (sc : mword 64) (tf tfa : list (mword 64))
    (M M' : gmap Z (bv 8)) (pi pi' : gmap (mword 27) uperm)
    (tf' : list (mword 64)) :
  tf_ueq tf tfa ->
  uround_ok sc tf M pi tf' M' pi' -> uround_ok sc tfa M pi tf' M' pi'.
Proof.
  intros Hu H.
  pose proof (tf_ueq_num tf tfa Hu) as Hn.
  pose proof (tf_ueq_resume_gpr0 tf tfa Hu) as Hg.
  pose proof (tf_ueq_resume_pc tf tfa Hu) as Hp.
  pose proof (tf_ueq_epc tf tfa Hu) as He.
  unfold uround_ok in H |- *.
  destruct (decide (sc = uecall_scause)).
  - destruct H as [Hx | [r [[Hb1 Hb2] Hm]]].
    + left. rewrite <- Hn. exact Hx.
    + right. exists r. split; [ split | ].
      * rewrite <- Hg. exact Hb1.
      * unfold tf_w in Hb2 |- *. rewrite <- He. exact Hb2.
      * rewrite <- Hn. exact (usys_mem_ok_ueq (usys_num tf) tf tfa r M M' pi pi' Hu Hm).
  - destruct H as [[Hi1 Hi2] Hrest].
    split; [ split | exact Hrest ].
    + rewrite <- Hg. exact Hi1.
    + rewrite <- Hp. exact Hi2.
Qed.

Lemma uround_ok_ueq_r (sc : mword 64) (tf : list (mword 64))
    (M M' : gmap Z (bv 8)) (pi pi' : gmap (mword 27) uperm)
    (tf' tfa' : list (mword 64)) :
  tf_ueq tf' tfa' ->
  uround_ok sc tf M pi tf' M' pi' -> uround_ok sc tf M pi tfa' M' pi'.
Proof.
  intros Hu H.
  pose proof (tf_ueq_resume_gpr0 tf' tfa' Hu) as Hg.
  pose proof (tf_ueq_resume_pc tf' tfa' Hu) as Hp.
  unfold uround_ok in H |- *.
  destruct (decide (sc = uecall_scause)).
  - destruct H as [Hx | [r [[Hb1 Hb2] Hm]]].
    + left. exact Hx.
    + right. exists r. split; [ split | exact Hm ].
      * rewrite <- Hg. exact Hb1.
      * rewrite <- Hp. exact Hb2.
  - destruct H as [[Hi1 Hi2] Hrest].
    split; [ split | exact Hrest ].
    + rewrite <- Hg. exact Hi1.
    + rewrite <- Hp. exact Hi2.
Qed.

(* ===================================================================== *)
(* SS5 THE ROUND WITHOUT THE IMAGE.                                        *)
(*                                                                         *)
(* A boundary can only state a relation about data its own residue PINS.   *)
(* [SpecUsertrap.usertrap_post] hands back [UsertrapRes.ut_res], whose     *)
(* [ut_own] owns [ProcPtOwn.proc_ptm … (us_M U')] -- so the image half of  *)
(* [uround_ok] has content there.  [SpecUservec.uservec_post] hands back   *)
(* the BARE residue ([ut_res_bare]), whose body never mentions [us_M] at   *)
(* all: [ut_res_bare pt ksp U] and [ut_res_bare pt ksp (upd_usM U M')] are *)
(* literally the same proposition, because across user execution the       *)
(* kernel does not own the user bytes.  An image equation stated at that   *)
(* index would be a GAP PREMISE -- true of the witness the prover picked   *)
(* and about nothing at all.                                              *)
(*                                                                         *)
(* [uround_vis_ok] is [uround_ok] with the image existentially weakened    *)
(* away.  What survives is exactly what the bare residue does pin: the     *)
(* TRAPFRAME (its [tf_page]) and the PERMISSION MAP (a function of         *)
(* [pv_upt] and [pv_sz], both owned).  Milestone J proper re-states the    *)
(* image half at [UexecRet.uvb], which names it by construction.          *)
(* ===================================================================== *)
Definition uround_vis_ok (sc : mword 64) (tf : list (mword 64))
    (pi : gmap (mword 27) uperm) (tf' : list (mword 64))
    (pi' : gmap (mword 27) uperm) : Prop :=
  if decide (sc = uecall_scause) then
    usys_num tf = USYS_exec
    \/ exists (r : mword 64) (M M' : gmap Z (bv 8)),
         uround_bump_ok tf tf' r
         /\ usys_mem_ok (usys_num tf) tf r M pi M' pi'
  else uround_id_ok tf tf' /\ pi' = pi.

Lemma uround_vis_of_ok (sc : mword 64) (tf tf' : list (mword 64))
    (M M' : gmap Z (bv 8)) (pi pi' : gmap (mword 27) uperm) :
  uround_ok sc tf M pi tf' M' pi' -> uround_vis_ok sc tf pi tf' pi'.
Proof.
  unfold uround_ok, uround_vis_ok.
  destruct (decide (sc = uecall_scause)).
  - intros [Hx | [r [Hb Hm]]]; [ left; exact Hx | ].
    right. exists r, M, M'. split; [ exact Hb | exact Hm ].
  - intros [Hi [_ Hp]]. split; [ exact Hi | exact Hp ].
Qed.
