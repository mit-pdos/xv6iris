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
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar) [Hep Harm]]".
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
      exact (ireg_dir_ok_ty (ds !!! islot inum) (wdu + wdt) Hdir
               ltac:(lia)). }
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
                wl wdu wdt gl cl rl pl Hlok Hrt Hdir Hwl0 Hpar
                with "Hla Hep"). iExact "Harm". }
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
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar) [Hep Harm]]".
    iDestruct (link_wdt_ge with "Hla Hfrag") as %[Hw1 _].
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
    iMod ("Hclose" with "[Ha Hfsb Harm Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m. iFrame "Ha".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl Hlok Hrt Hdir Hwl0 Hpar
                with "Hla Hep"). iExact "Harm". }
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
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar) [Hep Harm]]".
    iDestruct (link_w_ge with "Hla Hfrag") as %Hw1.
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
    iMod ("Hclose" with "[Ha Hfsb Harm Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m. iFrame "Ha".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl Hlok Hrt Hdir Hwl0 Hpar
                with "Hla Hep"). iExact "Harm". }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hty.
  Qed.

  (* ==================================================================== *)
  (*  (D2), DERIVED: A DIRECTORY HOLDING A LIVE SUBDIRECTORY ENTRY HAS    *)
  (*  AT LEAST TWO LINKS (V4's payoff, S7-unlink W5-DIR's premise)        *)
  (* ==================================================================== *)

  (* The three-step consumption bridge, packaged so the seal applies ONE
     lemma at the +0x8a seam's T_DIR arm:

       1. borrow the found record's ticket out of [dp]'s payload -- it is
          live, non-dot, non-self, and the home is live;
       2. REFUTE the plain flavour: the walk holds the CHILD's own
          [dinode_at] and its type test said T_DIR, so a plain ticket
          dies against (T1') ([ireg_link_not_dir] above);
       3. the ticket is therefore d-flavoured -- COUNTED, since the index
          is past the dots -- and [dlc_lower] reads
          [2 <= 1 + count <= nlink] off the same [F].

     Everything is borrowed and everything goes back; the conclusion is
     pure.  [su_w5_dir]'s (D2) premise [2 <= bv_unsigned (di_nlink dnd)]
     is exactly this lemma's conclusion -- the seal derives it here and
     feeds the premise; (D1) remains V5''s. *)
  Lemma dir_links_subdir_nlink2 (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (self : Z) (dnd : dinode)
      (datd : nat -> list (bv 8)) (kk : nat) (inum : bv 32)
      (dni : dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    bv_unsigned (di_type dnd) = T_DIR_z ->
    bv_unsigned (di_nlink dnd) <> 0 ->
    (2 <= kk)%nat ->
    (kk < dir_nrec (bv_unsigned (di_size dnd)))%nat ->
    dir_live datd kk ->
    bv_unsigned (dir_inum datd kk) <> self ->
    bv_unsigned inum = bv_unsigned (dir_inum datd kk) ->
    bv_unsigned (di_type dni) = T_DIR_z ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dni -∗
    dir_links self dnd datd ={E}=∗
    ⌜2 <= bv_unsigned (di_nlink dnd)⌝ ∗
    dinode_at γi inum dni ∗ dir_links self dnd datd.
  Proof.
    iIntros (HE Hin Htyd Hnzd Hk2 Hklt Hlv Hnself Hieq Htyi)
      "#Hinv Hdni Hdlnk".
    rewrite /dir_links decide_True; [| exact Htyd].
    iDestruct "Hdlnk" as (F) "(%Hbnd & %Hlow & Htie & H)".
    iDestruct (big_sepL_lookup_acc _
                 (seq 0 (dir_nrec (bv_unsigned (di_size dnd)))) kk kk
                 with "H") as "[Hk Hback]".
    { apply lookup_seq. lia. }
    (* the ticket, naked: the record is live and not the self record *)
    iEval (rewrite /dir_link_at_f
             (proj2 (dir_liveb_true datd kk) Hlv)
             (bool_decide_eq_false_2
                (bv_unsigned (dir_inum datd kk) = self) Hnself);
           cbn [negb andb]) in "Hk".
    iDestruct "Hk" as "[Hticket | [_ %Hz]]"; last first.
    { exfalso. exact (Hnzd Hz). }
    destruct (F kk) eqn:EFkk.
    - (* d-flavoured: the record is COUNTED and [dlc_lower] closes *)
      assert (Hcnt : (1 <= dlc_count F datd
                        (dir_nrec (bv_unsigned (di_size dnd))))%nat)
        by exact (dlc_count_pos F datd _ kk Hk2 Hklt Hlv EFkk).
      pose proof (Hlow Hnzd) as Hl2.
      iDestruct ("Hback" with "[Hticket]") as "H".
      { rewrite /dir_link_at_f.
        rewrite (proj2 (dir_liveb_true datd kk) Hlv).
        rewrite (bool_decide_eq_false_2
                   (bv_unsigned (dir_inum datd kk) = self) Hnself).
        cbn [negb andb]. iLeft. rewrite EFkk. iExact "Hticket". }
      iModIntro.
      iSplitR; [iPureIntro; lia |].
      iFrame "Hdni".
      iExists F. iSplitR; [iPureIntro; exact Hbnd |].
      iSplitR; [iPureIntro; exact Hlow |].
      (* V5': the parent tie is untouched -- this lemma BORROWS one record
         and hands it straight back *)
      iSplitL "Htie"; [iExact "Htie" |]. iExact "H".
    - (* plain: dies against (T1') at the child the walk NAMES *)
      iEval (cbn [dlc_tick]) in "Hticket".
      iEval (rewrite -Hieq) in "Hticket".
      iMod (ireg_link_not_dir E γi γfs inodestart nib inum dni HE Hin
              with "Hinv Hdni Hticket") as "(%Hnd & _ & _)".
      exfalso. exact (Hnd Htyi).
  Qed.

End IregDirBit.
