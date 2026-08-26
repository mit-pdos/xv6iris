(* ======================================================================= *)
(*  IregDirBit.v -- OFF [_CoqProject] SINCE durable-disk LANE G6.           *)
(*  SUPERSEDED BY THE TYPE REGISTER: design/fs-state.md §6½.                *)
(*                                                                          *)
(*  Historic: "AN OUTSTANDING [ilinkd] MEANS A DIRECTORY", stated at a       *)
(*  record the caller NAMES -- (T1)'s accessor, and the bridge between the   *)
(*  region's own spelling of [T_DIR] and [DirView]'s.                        *)
(* ======================================================================= *)

(*  WHY IT IS RETIRED.  (T1) and (T1') were readings of the old ledger's
    flavour columns: which column a paid record's ticket sat in told its
    holder whether the target was a directory.  A type-register fragment
    carries the target's TYPE outright ([FsStateInode.ent_ty_ok],
    [IregLinkNz.ireg_tok_nz]), so [ProofSysUnlink]'s rmdir arm -- this
    file's last live reader -- reads the fact off the entry unit it already
    holds and the two clauses are deleted with the columns.  Nothing
    imports this file; it does not compile against the narrowed
    [InodeRegion].                                                          *)

(*  WHY THIS FILE EXISTS.

    [InodeRegion.ireg_dir_ok] is (T1) -- [0 < wd -> di_type d = T_DIR] --
    and it is the clause the widened ledger's [wd] component buys
    (S7-unlink FINDING 3, V1; [IcacheRef.ilinkd]).  A caller that holds an
    [ilinkd] wants the fact read off the record IT names, i.e. off its own
    [dinode_at γi inum dn], which is exactly [IregLinkNz.ireg_tok_nz]'s
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
    exactly as [IregLinkNz.ireg_tok_nz] borrows
    theirs: a holder still has to spend it at the flush the fact licences,
    and a payload that owns a licence has to return it at its holder's
    iunlock.

    HOME.  It belongs in [InodeRegion.v]; it is here for
    [IregLinkNz.ireg_tok_nz]'s reason -- that file sits under ~350
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
Require Import FsBlocks.
Require Import LogInv.
Require Import DinodeEnc.
Require Import DirView.
Require Import IcacheRef.
Require Import DirLinks.
Require Import InodeRegion.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Local Open Scope Z_scope.

Section IregDirBit.
  Context `{!riscvGS Σ, !xv6G Σ}.
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
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iDestruct (ireg_rcol_wd_ge with "Hla Hfrag") as %Hw1.
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    (* (T1), read at the caller's own record, and translated into
       [DirView]'s spelling in the same step *)
    assert (Hty : bv_unsigned (di_type dn) = T_DIR_z).
    { rewrite -ireg_dir_ty_T_DIR_z -Hdeq.
      exact (ireg_dir_ok_ty (ds !!! islot inum) (wdu + wdt) Hdir
               ltac:(lia)). }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hlnk Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hlnk Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hlnk Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hty.
  Qed.

  (* ...AND THE SAME READING OFF THE **TAGGED** UNIT (V5' increment P).
     (T1) is stated at [wdu + wdt], so the parent-record unit forces it just
     as the [".."]-unit does; what changes is only which component the bound
     comes off ([IcacheRef.link_wdt_ge] rather than [link_wd_ge]).  It is
     needed because since V5' a payload's NAME records (index >= 2) carry
     the tagged unit, so sys_unlink's FILE arm -- which refutes [b = true]
     against the non-directory it is deleting -- meets an [ilinkdp] where it
     used to meet an [ilinkd].  Structural copy, one line different. *)
  Lemma ireg_dirbit_ty_dp (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) (pv : Z) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    ilinkdp (bv_unsigned inum) pv ={E}=∗
    ⌜bv_unsigned (di_type dn) = T_DIR_z⌝ ∗
    dinode_at γi inum dn ∗ ilinkdp (bv_unsigned inum) pv.
  Proof.
    iIntros (HE Hin) "#Hinv Hdn Hfrag".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iDestruct (ireg_rcol_wdt_ge with "Hla Hfrag") as %[Hw1 _].
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    (* (T1), read at the caller's own record, and translated into
       [DirView]'s spelling in the same step *)
    assert (Hty : bv_unsigned (di_type dn) = T_DIR_z).
    { rewrite -ireg_dir_ty_T_DIR_z -Hdeq.
      exact (ireg_dir_ok_ty (ds !!! islot inum) (wdu + wdt) Hdir
               ltac:(lia)). }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hlnk Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hlnk Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hlnk Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hty.
  Qed.


  (* ------------------------------------------------------------------ *)
  (*  (T1') AT A RECORD THE CALLER NAMES -- THE MIRROR (V4)               *)
  (* ------------------------------------------------------------------ *)

  (* [ilink z] ==> [1 <= wl] ([IcacheRef.link_w_ge]) ==> (T1')
     [di_type <> T_DIR].  The exact mirror of [ireg_dirbit_ty], and the
     missing half of S7-unlink's T_DIR arm: the file arm refutes a
     d-flavoured ticket through (T1); this refutes a PLAIN one at a
     record the walk KNOWS is a directory.  Mask-preserving, everything
     goes back. *)
  Lemma ireg_link_not_dir (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    ilink (bv_unsigned inum) ={E}=∗
    ⌜bv_unsigned (di_type dn) <> T_DIR_z⌝ ∗
    dinode_at γi inum dn ∗ ilink (bv_unsigned inum).
  Proof.
    iIntros (HE Hin) "#Hinv Hdn Hfrag".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iDestruct (ireg_rcol_w_ge with "Hla Hfrag") as %Hw1.
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    (* (T1'), read at the caller's own record: a directory would force
       [wl = 0] against the held unit's [1 <= wl] *)
    assert (Hty : bv_unsigned (di_type dn) <> T_DIR_z).
    { intro Hc.
      assert (Hc' : bv_unsigned (di_type (ds !!! islot inum)) = ireg_dir_ty)
        by (rewrite Hdeq ireg_dir_ty_T_DIR_z; exact Hc).
      pose proof (Hwl0 Hc'). lia. }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hlnk Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hlnk Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hlnk Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hty.
  Qed.

  (* (D2) USED TO BE DERIVED HERE (durable-disk G3).  "A directory holding
     a live SUBDIRECTORY entry has at least two links" was V4's payoff and
     S7-unlink W5-DIR's premise, and its carrier was [DirView.dlc_lower]
     inside [DirLinks.dir_links] -- one of the two things blocking the 6d
     column deletion.  It comes off the PARENT REGISTER now
     ([InodeRegion]'s (U1)/(U2), read by [IregLinkNz.ireg_par_up_min2]):
     the child's [".."] stands as an up-pointing unit in the parent's own
     register, and (U2) says a live inum's count exceeds its up-pointing
     namers.  No ledger, no data, no root exception.  [dlc_lower] is still
     MAINTAINED inside [dir_links] and has no reader left; it goes with the
     columns. *)


End IregDirBit.
