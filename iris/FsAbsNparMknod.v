(* FsAbsNparMknod.v -- THE LANE'S ACCEPTANCE TEST, DISCHARGED: lane W's two
   walk predicates ([FsAbsEraMknod.mknod_walk_pre_era] /
   [mknod_walk_dead_era]) are exactly what the nameiparent era walk's
   contract ([SpecNparEra]) consumes and produces.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii),
   REMAINING item.  A leaf and not an append, for the mirror's reason (see
   [FsAbsNpar]'s header).

   THREE FACTS, and two of them are [reflexivity].

   (1) THE FAMILIES ARE THE SAME FAMILY.  [FsAbsNpar.np_elems pl] and
       [SpecSysMknodAU.mknod_parent_elems pl] are both
       [removelast (path_elems pl)] -- so [ep_hops_from] and the
       [ax_hops_from] inside [mknod_walk_pre_era] are the same big-op, and
       the walk's trace premise IS what the syscall's one-shot hands out.
       This is not a coincidence to be maintained: it is why the npar
       contract ranges over the parent prefix at all (FsAbsNpar's header).

   (2) THE PRE.  [np_pre_of_mknod] fires lane W's one-shot at the string
       the walk fetched and at [ROOTINO], which is what the absolute-path
       scope of this contract pins the start to.  The two [ROOTINO]s --
       [InodeInv.ROOTINO : mword 32], read off namex's [li a1,1], and
       [FsImg.ROOTINO : Z], the image's -- agree by computation.

   (3) THE DEAD.  This one is NOT an identity, and the mismatch is worth
       recording rather than papering over.  [mknod_walk_dead_era] bounds
       its death index STRICTLY ([k < length ps]) in BOTH disjuncts; the
       walk can die at [k = length ps], because namex runs the level's
       type test and nlink guard at the PARENT's own level too
       ([FsAbsNpar]'s header, case (1)), and at [k = 0 = length ps] when
       the path has no elements at all (case (2)).  So the honest
       statement is a DISJUNCTION: either lane W's predicate, or the
       cursor at the parent index -- and the second alternative is exactly
       [SpecSysMknodAU.mknod_post_fail]'s THIRD fold arm
       ([exists d, P (length (mknod_parent_elems pl)) d * acre_commit *
       (... \/ dlookup_commit)]), which a create that never got to
       dirlink refunds anyway.  So mknod's post is dischargeable as it
       stands; what is NOT true is that [mknod_walk_dead_era] alone covers
       the walk's failures. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import InodeInv.        (* [ROOTINO] : mword 32, namex's own *)
Require Import FsImg.           (* [ROOTINO] : Z -- REQUIRED, NOT IMPORTED *)
Require Import FsBlocks.
Require Import FsBytesGamma.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import SpecSysMknodAU.  (* [mknod_parent_elems] *)
Require Import FsAbsEra.
Require Import FsAbsNpar.       (* [np_elems], [ep_hops_from], [np_dead] *)
Require Import FsAbsStart.      (* [ep_start]: the DEFERRED start        *)
Require Import FsAbsEraMknod.   (* [mknod_walk_pre_era], [mknod_walk_dead_era] *)
Require Import FsAbs.           (* LAST (FsAbs's own rule) *)

Local Open Scope Z_scope.

Section NparMknod.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  (1) the families                                                   *)
  (* ------------------------------------------------------------------ *)

  Lemma np_elems_is_mknod_parent_elems (pl : list (bv 8)) :
    np_elems pl = mknod_parent_elems pl.
  Proof. reflexivity. Qed.

  Lemma ep_hops_is_mknod_hops (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) (n : nat) :
    ep_hops_from γfs P Pmiss pl n
    = ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss (mknod_parent_elems pl) n.
  Proof. reflexivity. Qed.

  (* the roots agree *)
  Lemma np_rootino_agree :
    bv_unsigned InodeInv.ROOTINO = FsImg.ROOTINO.
  Proof. vm_compute. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (*  (2) lane W's one-shot supplies the walk's two trace premises       *)
  (* ------------------------------------------------------------------ *)

  (* THE FORM THE WALK ACTUALLY TAKES SINCE LANE A-iii: no firing at all,
     because the START INUM is the walk's to choose ([FsAbsStart]'s
     header).  [ep_start] at a fixed [pl] IS [mknod_walk_pre_era]
     specialized to that [pl] -- same quantifier, same tie, same family --
     so this is a rename plus the two ROOTINOs agreeing. *)
  Lemma np_start_of_mknod (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    mknod_walk_pre_era γfs P Pmiss -∗ ep_start γfs P Pmiss pl.
  Proof.
    iIntros "Hpre". rewrite /ep_start. iIntros (r Hr).
    rewrite /mknod_walk_pre_era.
    iMod ("Hpre" $! pl r with "[%]") as "[$ $]"; [| done].
    intros Hsl. rewrite -np_rootino_agree. exact (Hr Hsl).
  Qed.

  Lemma np_pre_of_mknod (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    mknod_walk_pre_era γfs P Pmiss ={⊤}=∗
      P 0%nat (bv_unsigned InodeInv.ROOTINO)
      ∗ ep_hops_from γfs P Pmiss pl 0%nat.
  Proof.
    iIntros "Hpre". rewrite /mknod_walk_pre_era.
    iMod ("Hpre" $! pl (bv_unsigned InodeInv.ROOTINO) with "[%]") as "[$ $]".
    { intros _. exact np_rootino_agree. }
    done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  (3) the walk's death arm, folded into lane W's two shapes          *)
  (* ------------------------------------------------------------------ *)

  Lemma np_dead_to_mknod (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    np_dead γfs P Pmiss pl -∗
      mknod_walk_dead_era γfs P Pmiss pl
      ∨ (∃ d : Z, P (length (mknod_parent_elems pl)) d).
  Proof.
    rewrite /np_dead /mknod_walk_dead_era.
    iIntros "[Hl | Hr]".
    - iDestruct "Hl" as (k d) "(%Hk & HP & Hh)".
      destruct (decide (k < length (np_elems pl))%nat) as [Hlt | Hge].
      + iLeft. iExists k, d. iSplitR; [by iPureIntro |]. iLeft. iFrame.
      + (* [k = length ps]: the parent's OWN level died.  The family from
           there is empty, and the cursor at the parent index is the whole
           refund -- mknod's third fold arm. *)
        assert (Hkeq : k = length (np_elems pl)) by lia.
        iRight. iExists d. rewrite -Hkeq. iClear "Hh". iExact "HP".
    - iDestruct "Hr" as (k d) "(%Hk & HP & Hh)".
      iLeft. iExists k, d. iSplitR; [by iPureIntro |]. iRight. iFrame.
  Qed.

  (* ...and the SUCCESS side needs no lemma at all: the walk returns
     [P (length (np_elems pl)) iL], which IS
     [P (length (mknod_parent_elems pl)) iL]. *)
  Lemma np_ok_is_mknod_ok (P : nat -> Z -> iProp Σ) (pl : list (bv 8))
      (iL : Z) :
    P (length (np_elems pl)) iL = P (length (mknod_parent_elems pl)) iL.
  Proof. reflexivity. Qed.

End NparMknod.
