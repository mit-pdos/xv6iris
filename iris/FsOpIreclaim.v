(* FsOpIreclaim.v -- durable-disk stage G2 (batch 3): ireclaim, the boot
   orphan sweep.

     void ireclaim(int dev) {                          (kernel/fs.c)
       for (int inum = 1; inum < sb.ninodes; inum++) {
         struct inode *ip = 0;
         struct buf *bp = bread(dev, IBLOCK(inum, sb));
         dip = the dinode of bp->data at slot [inum % IPB];
         if (dip->type != 0 && dip->nlink == 0)     // an orphan, on disk
           ip = iget(dev, inum);
         brelse(bp);
         if (ip) { begin_op(); ilock(ip); iunlock(ip); iput(ip); end_op(); }
       }
     }

   ONE TRANSACTION PER ORPHAN -- begin_op/end_op are inside the loop, so
   the sweep is not one big effect but a SEQUENCE of them, and every
   prefix of that sequence is a committed view that must be well-formed.
   Each step is [FsOpIputFree.eff_iput_free] (the iput whose [last] test
   the scan has just decided for it on disk), so this file is the ITERATED
   corollary of that family and nothing else.

   THE PRECONDITION IS THE SCAN'S OWN TEST.  [op_iput_free_wfv] asks for
   exactly [type <> 0] and [nlink = 0] AT THE COMMITTED VIEW, which is
   what [dip] is read from -- the scan needs no reachability argument and
   this file states none; the orphan characterisation inside
   [FsOpIputFree] does that work once.

   THE TRANSPORT ACROSS STEPS is one fact: freeing [i] rewrites record [i]
   and the bitmap, so a DISTINCT orphan [j]'s record -- hence its type and
   its nlink -- is untouched, and the superblock is untouched, so [sb]
   re-parses.  Hence the list is required [NoDup]; the scan's own list is
   the strictly increasing [inum] sequence, so that is free at the call
   site.

   Pure Rocq, no Iris: worklist item G2, batch (3).                       *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import DinodeEnc.
Require Import FsImg.
Require Import FsWf.
Require Import FsEffBase.
Require Import FsOpIputFree.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE SWEEP                                                          *)
(* ====================================================================== *)

(* the committed view after the orphans of [l] have been reclaimed, one
   transaction each, in order *)
Fixpoint eff_reclaim (P : Z -> list (bv 8)) (sb : fs_sb) (l : list Z)
  : Z -> list (bv 8) :=
  match l with
  | [] => P
  | i :: l' => eff_reclaim (eff_iput_free P sb i) sb l'
  end.

(* "is a committed orphan at [P]", in the scan's own vocabulary *)
Definition fs_orphan_at (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
  : Prop :=
  0 <= i < sb_ninodes sb
  /\ bv_unsigned (di_type (fs_dinode P sb i)) <> 0
  /\ bv_unsigned (di_nlink (fs_dinode P sb i)) = 0.

(* ONE step: the scan's guard IS [op_iput_free_wfv]'s precondition *)
Lemma op_ireclaim_step_wfv (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  fs_orphan_at P sb i ->
  fs_durable_wf_view (eff_iput_free P sb i).
Proof.
  intros Hv Hp (Hi & Hlive & Hnl).
  exact (op_iput_free_wfv P sb i Hv Hp Hi Hlive Hnl).
Qed.

(* the step's transport: a DISTINCT orphan survives it unchanged *)
Lemma op_ireclaim_step_keep (P : Z -> list (bv 8)) (sb : fs_sb) (i j : Z) :
  fs_sb_ok sb -> 0 <= i < sb_ninodes sb ->
  fs_orphan_at P sb j -> j <> i ->
  fs_orphan_at (eff_iput_free P sb i) sb j.
Proof.
  intros Hok Hi (Hj & Hlive & Hnl) Hji.
  unfold fs_orphan_at.
  rewrite (eff_iput_free_fuse P sb i Hok (iblk_z_range sb i Hi)).
  rewrite (eff_free_inode_dinode P sb i j Hok (iblk_z_range sb i Hi)
             (iblk_z_range sb j Hj)).
  rewrite decide_False by exact Hji.
  split; [exact Hj | split; [exact Hlive | exact Hnl]].
Qed.

Lemma op_ireclaim_step_parse (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_sb_ok sb -> 0 <= i < sb_ninodes sb ->
  fs_parse_sb P = Some sb ->
  fs_parse_sb (eff_iput_free P sb i) = Some sb.
Proof.
  intros Hok Hi Hp.
  rewrite (eff_iput_free_fuse P sb i Hok (iblk_z_range sb i Hi)).
  exact (eff_free_inode_parse P sb i Hok (iblk_z_range sb i Hi) Hp).
Qed.

(* ====================================================================== *)
(*  2.  THE ITERATED COROLLARY                                             *)
(* ====================================================================== *)

Lemma op_ireclaim_wfv (P : Z -> list (bv 8)) (sb : fs_sb) (l : list Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  NoDup l ->
  (forall i : Z, i ∈ l -> fs_orphan_at P sb i) ->
  fs_durable_wf_view (eff_reclaim P sb l).
Proof.
  revert P. induction l as [| i l IH]; intros P Hv Hp Hnd Horph;
    [exact Hv |].
  pose proof (fs_wf_view_sb_ok P sb Hv Hp) as Hok.
  pose proof (NoDup_cons_1_1 i l Hnd) as Hni.
  pose proof (NoDup_cons_1_2 i l Hnd) as Hnd'.
  destruct (Horph i ltac:(apply elem_of_cons; left; reflexivity))
    as (Hi & Hlive & Hnl).
  cbn [eff_reclaim].
  apply IH.
  - exact (op_iput_free_wfv P sb i Hv Hp Hi Hlive Hnl).
  - exact (op_ireclaim_step_parse P sb i Hok Hi Hp).
  - exact Hnd'.
  - intros j Hj.
    apply (op_ireclaim_step_keep P sb i j Hok Hi).
    + apply Horph, elem_of_cons. right. exact Hj.
    + intros ->. exact (Hni Hj).
Qed.

(* EVERY COMMIT of the sweep, not just its last: the view after any
   PREFIX is well-formed, which is what one-transaction-per-orphan
   actually owes. *)
Corollary op_ireclaim_prefix_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (l l1 l2 : list Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  NoDup l ->
  (forall i : Z, i ∈ l -> fs_orphan_at P sb i) ->
  l = (l1 ++ l2)%list ->
  fs_durable_wf_view (eff_reclaim P sb l1).
Proof.
  intros Hv Hp Hnd Horph ->.
  apply list_relations.NoDup_app in Hnd as (Hnd1 & _ & _).
  apply (op_ireclaim_wfv P sb l1 Hv Hp Hnd1).
  intros i Hi. apply Horph, elem_of_app. left. exact Hi.
Qed.
