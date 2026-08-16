(* ======================================================================= *)
(*  IregDirBit.v -- "AN OUTSTANDING [ilinkd] MEANS A DIRECTORY", stated at   *)
(*  a record the caller NAMES.  (T1)'s accessor, and the bridge between the  *)
(*  region's own spelling of [T_DIR] and [DirView]'s.                        *)
(* ======================================================================= *)

(*  WHY THIS FILE EXISTS.

    [InodeRegion.ireg_dir_ok] is (T1) -- [0 < wd -> di_type d = T_DIR] --
    and it is the clause the widened ledger's [wd] component buys
    (S7-unlink FINDING 3, V1; [IcacheRef.ilinkd]).  A caller that holds an
    [ilinkd] wants the fact read off the record IT names, i.e. off its own
    [dinode_at γi inum dn], which is exactly [IregLinkNz.ireg_link_nz]'s
    position one clause across.  This file is that lemma with (L1) replaced
    by (T1), and it is deliberately its structural copy: same premises, same
    opening, same re-park, one different pure step.

    WHAT IT IS FOR, AND WHAT IT IS NOT.  It is the READ half of the
    count-fact carrier.  It does NOT give a count: [ilinkd] bounds [wd]
    BELOW, and the model still bounds the ledger only below (that is
    FINDING 3's wall, and V1 does not move it).  What it gives is the TYPE
    of the record a paid, d-flavoured fragment names -- the fact
    [DirLinks]/[DirView]'s V2 clause will be keyed on, and the fact
    sys_unlink's T_DIR arm needs before it can say anything about which
    records can exist at all.

    MASK-PRESERVING, AND EVERYTHING GOES BACK.  The fragment is BORROWED,
    exactly as [ireg_link_nz] and [InodeRegion.ireg_link_alloc] borrow
    theirs: a holder still has to spend it at the flush the fact licences,
    and a payload that owns a licence has to return it at its holder's
    iunlock.

    HOME.  It belongs in [InodeRegion.v]; it is here for
    [IregLinkNz.ireg_link_nz]'s reason -- that file sits under ~350
    dependents and an additive lemma inside it costs that cone on every
    iteration (durable-notes, "the rebuild cone is the dev-loop cost").
    Fold both leaves back at a milestone. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl.
From iris.base_logic.lib Require Import invariants ghost_map.
Require Import SailStdpp.Values.
Require Import RiscvPtsto.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import LogInv.
Require Import DinodeEnc.
Require Import DirView.
Require Import IcacheRef.
Require Import DirLinks.
Require Import InodeInv.
Require Import InodeRegion.

Local Open Scope Z_scope.

Section IregDirBit.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ,
            !logG Σ}.
  Context `{ICFG : icfg}.

  (* ------------------------------------------------------------------ *)
  (*  THE TYPE, ACROSS THE TWO SPELLINGS                                  *)
  (* ------------------------------------------------------------------ *)

  (* [InodeRegion.ireg_dir_ty] is (T1)'s type at the REGION's own key type --
     a [Z] literal, stated there rather than imported so that a file ~350
     dependents deep does not acquire [DirView]'s directory geometry for one
     constant (the comment at [ireg_dir_ty] says so).  This is the bridge,
     and it is [IregLinkNz.ireg_root_ROOTINO]'s twin: the two sides are
     convertible, so it costs one [reflexivity].  Every consumer outside the
     region rewrites with this and speaks [T_DIR_z]. *)
  Lemma ireg_dir_ty_T_DIR_z : ireg_dir_ty = T_DIR_z.
  Proof. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (*  (T1) AT A RECORD THE CALLER NAMES                                   *)
  (* ------------------------------------------------------------------ *)

  (* [ilinkd z] ==> [1 <= wd] ([IcacheRef.link_wd_ge]) ==> (T1)
     [di_type = T_DIR].  Mask-preserving, and everything goes back. *)
  Lemma ireg_dirbit_ty (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    ilinkd (bv_unsigned inum) ={E}=∗
    ⌜bv_unsigned (di_type dn) = T_DIR_z⌝ ∗
    dinode_at γi inum dn ∗ ilinkd (bv_unsigned inum).
  Proof.
    iIntros (HE Hin) "#Hinv Hdn Hfrag".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wd & %gl & %rl & %cl & Hla & %Hlok & %Hrt & %Hdir) [Hep Harm]]".
    iDestruct (link_wd_ge with "Hla Hfrag") as %Hw1.
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    (* (T1), read at the caller's own record, and translated into
       [DirView]'s spelling in the same step *)
    assert (Hty : bv_unsigned (di_type dn) = T_DIR_z).
    { rewrite -ireg_dir_ty_T_DIR_z -Hdeq.
      exact (ireg_dir_ok_ty (ds !!! islot inum) wd Hdir ltac:(lia)). }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hfsb Harm Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m. iFrame "Ha".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wd gl cl rl Hlok Hrt Hdir with "Hla Hep"). iExact "Harm". }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hty.
  Qed.

End IregDirBit.
