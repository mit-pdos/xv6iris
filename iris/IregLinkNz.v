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
Require Import FsBlocks.
Require Import LogInv.
Require Import DinodeEnc.
Require Import DirView.
Require Import IcacheRef.
Require Import DirLinks.
Require Import InodeInv.
Require Import InodeRegion.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Local Open Scope Z_scope.

Section IregLinkNz.
  Context `{!riscvGS Σ, !xv6G Σ}.
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
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (ireg_rcol_w_ge with "Hla Hfrag") as %Hw1.
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
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hnz.
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
      (inodestart : Z) (nib : nat) (inum : bv 32) (ty : bv 16) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    ireg_boot -∗
    iclaim (bv_unsigned inum) ty ={E}=∗ False.
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
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (ireg_rcol_claim_agree with "Hla Hcl") as %Hc.
    iDestruct "Hdisj" as "[%Hnone | Hopen]".
    { exfalso. rewrite Hnone in Hc. discriminate. }
    iDestruct (ireg_boot_open_excl with "Hboot Hopen") as %[].
  Qed.

  (* ...AND ITS FLAVOURED FORM.  After V4's flip create's [dp->nlink++]
     mints [ilinkd], and the read-back the fused deposit needs
     ([DirLinks.dlc_bv_add1_nz_eq]'s nonzero premise) is this same fact
     off the d-flavoured unit.  Any flavour bounds the SUM below, and
     (L1) does the rest. *)
  Lemma ireg_link_nz_fl (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode)
      (fl : option (option Z)) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    ilink_fl fl (bv_unsigned inum) ={E}=∗
    ⌜bv_unsigned (di_nlink dn) <> 0⌝ ∗
    dinode_at γi inum dn ∗ ilink_fl fl (bv_unsigned inum).
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
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (ireg_rcol_wsum_ge with "Hla Hfrag") as %Hw1.
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    assert (Hnz : bv_unsigned (di_nlink dn) <> 0).
    { rewrite -Hdeq. pose proof (di_nlink_nonneg (ds !!! islot inum)) as Hnn.
      destruct Hlok as [Hle _]. lia. }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hnz.
  Qed.

  (* THE ROOT'S MINIMUM AT A HELD UNIT (V5''s consumption, step 2): the
     strict root clause plus ANY outstanding unit put the root's count at
     TWO or more -- so a directory whose count is ONE is not the root,
     which is what lets [dir_links_dotdot_out]'s V5' extension name a
     create-episode for [ip].  FINDING 3's [nlink ip = 1] is the consumer. *)
  Lemma ireg_link_root_min2 (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode)
      (fl : option (option Z)) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    ilink_fl fl (bv_unsigned inum) ={E}=∗
    ⌜bv_unsigned inum = ireg_root -> 2 <= bv_unsigned (di_nlink dn)⌝ ∗
    dinode_at γi inum dn ∗ ilink_fl fl (bv_unsigned inum).
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
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (ireg_rcol_wsum_ge with "Hla Hfrag") as %Hw1.
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    rewrite Hdeq in Hrt.
    assert (Hmin2 : bv_unsigned inum = ireg_root ->
                    2 <= bv_unsigned (di_nlink dn)).
    { intro Hz. pose proof (Hrt Hz) as Hlt.
      pose proof (di_nlink_nonneg dn). lia. }
    rewrite -Hdeq in Hrt.
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hmin2.
  Qed.

  (* ...AND THE SAME READING OFF THE **TAGGED** UNIT (V5' increment W).
     The walk that needs the root refutation for [ip] holds exactly one
     fragment for it -- the [ilinkdp ip dp] the zeroing released -- and
     that is not an [ilink_fl]: the payload keeps only the payment half,
     the [iparent] half being the child's own and still locked inside the
     payload this refutation is about to open.  So the [wdt] bound is read
     directly ([IcacheRef.link_wdt_ge]) and the proof is otherwise
     [ireg_link_root_min2]'s, line for line. *)
  Lemma ireg_link_root_min2_dp (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) (pv : Z) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    ilinkdp (bv_unsigned inum) pv ={E}=∗
    ⌜bv_unsigned inum = ireg_root -> 2 <= bv_unsigned (di_nlink dn)⌝ ∗
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
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (ireg_rcol_wdt_ge with "Hla Hfrag") as %[Hw1 _].
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    rewrite Hdeq in Hrt.
    assert (Hmin2 : bv_unsigned inum = ireg_root ->
                    2 <= bv_unsigned (di_nlink dn)).
    { intro Hz. pose proof (Hrt Hz) as Hlt.
      pose proof (di_nlink_nonneg dn). lia. }
    rewrite -Hdeq in Hrt.
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn Hfrag". iPureIntro. exact Hmin2.
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

  (* ...AND THE THIRD SPELLING (V5' increment P).  [DirLinks.dl_root] is
     the root inum at the PAYLOAD's key type, restated there for the same
     layering reason [ireg_root] is restated in [InodeRegion] -- DirLinks
     sits below both files and can import neither.  This is the bridge, and
     it is what S7-unlink's T_DIR arm rewrites with after
     [ireg_link_root_min2] has refuted [ip = ireg_root]. *)
  Lemma dl_root_ireg_root : dl_root = ireg_root.
  Proof. reflexivity. Qed.

  Lemma dl_root_ROOTINO : bv_unsigned ROOTINO = dl_root.
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

  (* THE COUNT PREMISE IS THE LEMMA'S OWN NAME MADE HONEST (V2).  The
     payload now carries [DirView.dlc_bound], which is an UPPER bound on
     the home's count -- so the big-op rides a count change only DOWNWARDS,
     which is the only direction this lemma was ever applied in (sys_link's
     [bad:] tail, sys_unlink's decrements).  The tickets themselves still
     say nothing about the home. *)
  (* V4 NARROWED THIS TO NON-DIRECTORIES, and that is its honest scope:
     [dlc_lower] pins a LIVE directory's count to exactly [1 + count], so
     no directory's [nlink] can move with its bytes fixed except by the
     movers that price the count ([dir_links_dirlink_d], the unlink wand).
     Every landed caller is at a FILE (sys_link's [bad:] tail refuted
     T_DIR at ARM E2), where both sides are [emp]. *)
  Lemma dir_links_nlink_drop (self : Z) (dn dn' : dinode)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_type dn) <> T_DIR_z ->
    di_type dn' = di_type dn ->
    dir_links self dn data -∗ dir_links self dn' data.
  Proof.
    intros Hnd Hty. rewrite /dir_links Hty.
    destruct (decide (bv_unsigned (di_type dn) = T_DIR_z)) as [Hc | _];
      [exfalso; exact (Hnd Hc) | iIntros "_"; done].
  Qed.

End IregLinkNz.
