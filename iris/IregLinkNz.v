(* ======================================================================= *)
(*  IregLinkNz.v -- "AN OUTSTANDING [ilink] MEANS A NONZERO COUNT", stated   *)
(*  at a record the caller NAMES, plus the one [dir_links] move that fact    *)
(*  unlocks.                                                                *)
(* ======================================================================= *)

(*  WHY THIS FILE EXISTS.

    A caller that is about to spend a link unit holds [dinode_at γi inum
    dn] and wants "this record's count is not already zero" read off THAT
    record.

    That is what a [nlink--] needs.  [SpecIupdate.wp_iupdate_unlink] takes
    the Z equation "the OLD count is the new one plus one", and the only
    honest source of its side condition -- the count it is about to lower
    is not already zero -- is the unit being spent: the counting RA says
    "an outstanding [FsStateLink.link_tok] at [z] bounds [z]'s own
    [di_nlink] below" ([InodeRegion.ireg_lnk_tok_nz]).  Nothing in the
    WALK can supply it, because the record a re-[ilock] returns is a fresh
    existential: sys_link's [bad:] arm unlocks [ip] at +0x6c and re-locks
    it at +0xe8, and between those two another thread may hold the sleep
    lock.  The token is what crosses that window, and [ireg_tok_nz] is the
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
Require Import FsBlocks.
Require Import LogInv.
Require Import DinodeEnc.
Require Import DirView.
Require Import IcacheRef.
Require Import InodeInv.
Require Import InodeRegion.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Local Open Scope Z_scope.

Section IregLinkNz.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{ICFG : icfg}.

  (* ------------------------------------------------------------------ *)
  (*  "A HELD TOKEN MEANS A NONZERO COUNT", AT A RECORD THE CALLER NAMES  *)
  (* ------------------------------------------------------------------ *)

  (* THE COUNTING RA's READING, and it REPLACES the old ledger's (durable-
     disk lane G, slice 6b).  This used to be [ireg_link_nz] / [_fl]: an
     [IcacheRef.ilink] (resp. [ilink_fl]) bounded the ledger's [wl+wdu+wdt]
     below, and (L1) turned that into [1 <= di_nlink].  The same fact off
     the counting RA is [InodeRegion.ireg_lnk_tok_nz] -- one outstanding
     [FsStateLink.link_tok] at [z] bounds [z]'s own [di_nlink] below, by
     the RA's own law -- and it is FLAVOUR-BLIND, so the two old spellings
     collapse into this one.  Every walk that used to present a colour
     already holds the token beside it ([SpecIupdate.wp_iupdate_link] pays
     both out and [_unlink] takes the token back), so no caller gained a
     premise.

     Mask-preserving, and everything goes back: the token is BORROWED,
     exactly as the fragment was, because the caller still has to spend it
     at the flush this fact licences ([ireg_tok_root_min2] below borrows
     its token the same way). *)
  (* TWO FRAGMENTS AT ONE INUM AGREE (durable-disk G5, (D1)'s walk lemma).
     The authority is a UNIFORM multiset, so any two held fragments carry
     the SAME value -- and the value is the record's kind.  rmdir reads the
     child's own ["."] fragment (which pins the child's [".."] target)
     against the parent's name record for the child (which asserts
     [TDir dp]), and the two together ARE (D1).  Stated as an ACCESSOR over
     [ireg_inv] for §7.1.4's reason, exactly as [ireg_tok_nz] is. *)
  Lemma ireg_toks_agree (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) (v v' : ity) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    FsStateLink.link_tok (FsBytesGamma.fs_gamma_L γfs) (bv_unsigned inum) v -∗
    FsStateLink.link_tok (FsBytesGamma.fs_gamma_L γfs) (bv_unsigned inum) v'
    ={E}=∗
    ⌜v = v' /\ ireg_reg_ok (bv_unsigned (di_type dn)) v⌝ ∗
    dinode_at γi inum dn ∗
    FsStateLink.link_tok (FsBytesGamma.fs_gamma_L γfs) (bv_unsigned inum) v ∗
    FsStateLink.link_tok (FsBytesGamma.fs_gamma_L γfs) (bv_unsigned inum) v'.
  Proof.
    iIntros (HE Hin) "#Hinv Hdn Hfrag Hfrag2".
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
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    iDestruct (ireg_lnk_toks_agree with "Hlnk Hfrag Hfrag2") as %Hnz0.
    iDestruct (ireg_lnk_tok_ty with "Hlnk Hfrag") as %Hty0.
    rewrite Hdeq in Hty0.
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
                cl rl fz cn Hlok Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn Hfrag Hfrag2". iPureIntro.
    split; [exact Hnz0 | exact Hty0].
  Qed.

  Lemma ireg_tok_nz (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) (v : ity) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    FsStateLink.link_tok (FsBytesGamma.fs_gamma_L γfs) (bv_unsigned inum) v
    ={E}=∗
    ⌜bv_unsigned (di_nlink dn) <> 0
     /\ ireg_reg_ok (bv_unsigned (di_type dn)) v⌝ ∗
    dinode_at γi inum dn ∗
    FsStateLink.link_tok (FsBytesGamma.fs_gamma_L γfs) (bv_unsigned inum) v.
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
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    iDestruct (ireg_lnk_tok_nz with "Hlnk Hfrag") as %Hnz0.
    iDestruct (ireg_lnk_tok_ty with "Hlnk Hfrag") as %Hty0.
    rewrite Hdeq in Hnz0. rewrite Hdeq in Hty0.
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
                cl rl fz cn Hlok Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. split; [exact Hnz0 | exact Hty0].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE BOOT SHELTER, AS A THEOREM (fs-fragments.md §7.12 / §7.1.7)     *)
  (* ------------------------------------------------------------------ *)

  (* Holding the exclusive pre-userspace token [ireg_boot], NO in-region slot
     can be CLAIMED.  §7.1.7's threat is that ireclaim's [iget] fires exactly
     at a claim-shaped record (type ≠ 0, nlink 0) -- indistinguishable from a
     mid-window claim box -- and the licence alone cannot exclude it; the model
     stated the exclusion only as the boot-order comment "ireclaim runs before
     kexec, before any second process".  Here it is a ghost consequence:

       an [iclaim z] pins the slot's claim component to [Some]
       ([IcacheRef.link_claim_agree]) -> the slot's boot-shelter clause is
       forced onto its SEALED arm [ireg_open] -> [ireg_boot_open_excl] refutes
       it, because the exclusive boot token and the sealed one-shot cannot
       coexist ([ity_pending_shot_excl]).

     ireclaim carries [ireg_boot] on the boot thread ([SpecIreclaim] premise),
     so this discharges the boot-order fact §7.1.7 left to a comment.  Stated
     as an ACCESSOR over [ireg_inv] (the §7.1.4 constraint: name the record by
     opening the region, never a free-standing entailment over a free [dn]);
     the token is refuted-against, not consumed, so it survives for the caller
     -- when [iclaim] is actually mintable (F1.5c's (M1)), this is what lets
     ireclaim's free supply the [c = None] that §7.1.5 shows it needs. *)
  Lemma ireg_boot_no_claim (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (ty : bv 16)
      (t : nat) (qt : Qp) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    ireg_boot -∗
    iclaim (bv_unsigned inum) ty t qt ={E}=∗ False.
  Proof.
    iIntros (HE Hin) "#Hinv Hboot Hcl".
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
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iDestruct (ireg_rcol_claim_agree with "Hla Hcl") as %Hc.
    iDestruct "Hdisj" as "[%Hnone | Hopen]".
    { exfalso. rewrite Hnone in Hc. discriminate. }
    iDestruct (ireg_boot_open_excl with "Hboot Hopen") as %[].
  Qed.

  (* THE ROOT'S MINIMUM AT A HELD TOKEN (S7-unlink's dir arm, (D1) step 2):
     the region's unspendable keep-alive token plus ANY token the caller
     holds put the root's count at TWO or more -- so a directory whose count
     is ONE is not the root, which is what lets [dir_links_dotdot_out]'s V5'
     extension name a create-episode for [ip].  FINDING 3's [nlink ip = 1]
     is the consumer.

     The content is [InodeRegion.ireg_lnk_root_min2], read at the slot's own
     [ireg_lnk]; this is its ACCESSOR, and the token is BORROWED and handed
     straight back, exactly as [ireg_tok_nz] borrows its token -- the caller
     still has to spend it at the [nlink--] this refutation licences. *)
  Lemma ireg_tok_root_le (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode)
      (k : nat) (v : ity) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    FsStateLink.link_toks (FsBytesGamma.fs_gamma_L γfs) (bv_unsigned inum)
      (FsStateLink.link_reps k v) ={E}=∗
    ⌜bv_unsigned inum = ireg_root -> Z.of_nat k <= bv_unsigned (di_nlink dn)⌝ ∗
    dinode_at γi inum dn ∗
    FsStateLink.link_toks (FsBytesGamma.fs_gamma_L γfs) (bv_unsigned inum)
      (FsStateLink.link_reps k v).
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
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    iDestruct (ireg_lnk_root_le with "Hlnk Hfrag") as %Hmin0.
    rewrite Hdeq in Hmin0.
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
                cl rl fz cn Hlok Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hmin0.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE ROOT INUM, ACROSS THE TWO SPELLINGS                             *)
  (* ------------------------------------------------------------------ *)

  (* [InodeRegion.ireg_root] is the root's inum at the REGION's key type --
     a [Z] literal, stated there rather than imported so that a file 350
     dependents deep does not acquire the whole in-core inode geometry for
     one constant (the comment at [ireg_root] says so).  This is the bridge,
     and it is the reason that choice costs nothing: [ROOTINO] is
     [mword_of_int 1] and the two sides are convertible.

     A walk that has to say "this inum is (not) the root" -- namex's
     absolute walk, or [ireg_tok_root_min2]'s consumer -- rewrites with this
     and is done. *)
  Lemma ireg_root_ROOTINO : bv_unsigned ROOTINO = ireg_root.
  Proof. vm_compute. reflexivity. Qed.


End IregLinkNz.
