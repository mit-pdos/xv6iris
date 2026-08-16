(* ======================================================================= *)
(*  IregLinkNz.v -- "AN OUTSTANDING [ilink] MEANS A NONZERO COUNT", stated   *)
(*  at a record the caller NAMES, plus the one [dir_links] move that fact    *)
(*  unlocks.                                                                *)
(* ======================================================================= *)

(*  WHY THIS FILE EXISTS.

    [InodeRegion.ireg_link_alloc] is §20.2's payoff at a record the caller
    can NOT name -- it reads the type of a slot out of the dinode block's
    machinery half, because the fragment for a NAMED inum lives wherever
    that inum's owner put it.  A caller that spends its OWN fragment is in
    the opposite position: it holds [dinode_at γi inum dn] and wants (L1)
    read off THAT record.

    That is what a [nlink--] needs.  [SpecIupdate.wp_iupdate_unlink] takes
    the Z equation "the OLD count is the new one plus one", and the only
    honest source of its side condition -- the count it is about to lower
    is not already zero -- is the fragment being spent: (L1) says
    [w <= di_nlink], the fragment says [1 <= w].  Nothing in the WALK can
    supply it, because the record a re-[ilock] returns is a fresh
    existential: sys_link's [bad:] arm unlocks [ip] at +0x6c and re-locks
    it at +0xe8, and between those two another thread may hold the sleep
    lock.  The ledger is what crosses that window, and this is the
    accessor that reads it.

    [dir_links_nlink_drop] is the resource consequence at the same record.
    [DirLinks.dir_link_at]'s GREY disjunct carries [di_nlink dn = 0] as its
    own home condition (§20.17.4), so a record whose count is nonzero is
    necessarily paying with an [ilink] -- and the whole payload therefore
    survives a count change untouched.  Without it a re-park after a
    [nlink--] would have to case on a colour it can refute.

    HOME.  Both belong in [InodeRegion.v] / [DirLinks.v] respectively; they
    are here because those two files sit under ~350 dependents apiece and an
    additive lemma inside either costs that cone on every iteration
    (durable-notes, "the rebuild cone is the dev-loop cost").  Fold them back
    at a milestone.  Nothing here is sys_link-specific -- sys_unlink's
    [dp->nlink--] wants exactly the same pair. *)

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

Section IregLinkNz.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ,
            !logG Σ}.
  Context `{ICFG : icfg}.

  (* ------------------------------------------------------------------ *)
  (*  (L1) AT A RECORD THE CALLER NAMES                                   *)
  (* ------------------------------------------------------------------ *)

  (* [ilink z] ==> [1 <= w] ([IcacheRef.link_w_ge]) ==> (L1) [1 <= nlink].
     Mask-preserving, and everything goes back: the fragment is BORROWED,
     exactly as [ireg_link_alloc] borrows it, because the caller still has
     to spend it at the flush this fact licences. *)
  Lemma ireg_link_nz (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    ilink (bv_unsigned inum) ={E}=∗
    ⌜bv_unsigned (di_nlink dn) <> 0⌝ ∗
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
    iDestruct "Hslot" as "[(%wl & %wd & %gl & %rl & %cl & Hla & %Hlok & %Hrt & %Hdir) [Hep Harm]]".
    iDestruct (link_w_ge with "Hla Hfrag") as %Hw1.
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    (* (L1), read at the caller's own record *)
    assert (Hnz : bv_unsigned (di_nlink dn) <> 0).
    { rewrite -Hdeq. pose proof (di_nlink_nonneg (ds !!! islot inum)) as Hnn.
      destruct Hlok as [Hle _]. lia. }
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
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hnz.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE ROOT INUM, ACROSS THE TWO SPELLINGS                             *)
  (* ------------------------------------------------------------------ *)

  (* [InodeRegion.ireg_root] is the root clause's inum at the REGION's key
     type -- a [Z] literal, stated there rather than imported so that a file
     350 dependents deep does not acquire the whole in-core inode geometry
     for one constant (the comment at [ireg_root] says so).  This is the
     bridge, and it is the reason that choice costs nothing: [ROOTINO] is
     [mword_of_int 1] and the two sides are convertible.

     A consumer of [InodeRegion.ireg_root_ne] -- §20.4's licence (f), whose
     arm is [⌜bv_unsigned z = ROOTINO⌝] -- rewrites with this and is done. *)
  Lemma ireg_root_ROOTINO : bv_unsigned ROOTINO = ireg_root.
  Proof. vm_compute. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE PAYLOAD SURVIVES A COUNT CHANGE AT A LIVE RECORD                *)
  (* ------------------------------------------------------------------ *)

  (* [dir_link_at]'s grey disjunct carries [di_nlink dn = 0], so at a
     nonzero count every ticket in the big-op is the [ilink] one -- and an
     [ilink] says nothing about the HOME record at all.  Hence the whole
     payload rides a [nlink] change untouched, provided the type and the
     size (which decide the shape and the length of the big-op) do not
     move.  Both hold of a [nlink--]: it writes one halfword. *)
  Lemma dir_link_at_nlink_drop (self : Z) (dn dn' : dinode)
      (data : nat -> list (bv 8)) (k : nat) :
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_link_at self dn data k -∗ dir_link_at self dn' data k.
  Proof.
    intros Hnz. rewrite /dir_link_at.
    destruct (dir_liveb data k
              && negb (bool_decide (bv_unsigned (dir_inum data k) = self)));
      [| iIntros "_"; done].
    iIntros "[H | [_ %Hz]]"; [iLeft; iExact "H" |].
    exfalso. exact (Hnz Hz).
  Qed.

  Lemma dir_links_nlink_drop (self : Z) (dn dn' : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_nlink dn) <> 0 ->
    di_type dn' = di_type dn ->
    di_size dn' = di_size dn ->
    dir_links self dn data -∗ dir_links self dn' data.
  Proof.
    intros Hnz Hty Hsz. rewrite /dir_links Hty Hsz.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z));
      [| iIntros "_"; done].
    iIntros "H".
    iApply (big_sepL_mono with "H").
    iIntros (kk k0 _) "Hk".
    iApply (dir_link_at_nlink_drop self dn dn' data k0 Hnz with "Hk").
  Qed.

End IregLinkNz.
