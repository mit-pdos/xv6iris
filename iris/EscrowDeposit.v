(* ============================================================================
   OPTION A (reordered iput) -- the OFF-LOCK DEPOSIT accessor (iput +0xb6).
   A leaf above EscrowInode/InodeRegion: it opens [ireg_inv], absorbs the
   freer's fragment, DEPOSITS the region marker into the 0x86-minted escrow
   ([escA_deposit] -> [committedA]), rebinds+splits the marked slot's [reg_full]
   (structural since the reg-fold), and parks the region PENDING arm.  Body =
   [InodeRegion.ireg_free_au] with the closing action swapped.  In its own file
   so the fs-cone imports it needs ([DiskPtsto]/[LogInv]/[FsBlocks]/[DinodeEnc])
   do not disturb [EscrowInode]'s escrow proofs (import-order/instance hygiene,
   as in the EscrowRegionA de-risk).
   ========================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import excl.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map mono_nat own.
Require Import RiscvPtsto.
Require Import DiskPtsto.
Require Import LogInv.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import InodeRegion.
Require Import EscrowDefs.
Require Import EscrowInode.

Section EscrowDeposit.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ,
            !logG Σ}.
  Context `{ICFG : icfg}.

  Lemma ireg_free_deposit_au (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) (ge gr : gname) :
    ↑iregN ⊆ E ->
    ↑escAN (bv_unsigned inum) ⊆ E ∖ ↑iregN ->
    (bv_unsigned inum < 16 * Z.of_nat nib)%Z ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') = 0 ->
    di_nlink_stable dn' dn ->
    ireg_inv γi γfs inodestart nib -∗
    escA_inv ge gr γi (bv_unsigned inum) -∗
    dinode_at γi inum dn -∗
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock γfs (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock γfs (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ committedA ge).
  Proof.
    iIntros (HE Hesc_mask Hin Hwf Hdn' Hz Hnl) "#Hinv #Hesc Hdn".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds0) "(>%Hwf0 & >%Hcp0 & >Hfsb & >Hsls)".
    iModIntro.
    rewrite (ireg_bi_iblock inum inodestart).
    iExists (diblk_bytes ds0).
    iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    assert (Hds0 : ds0 = ds) by exact (diblk_bytes_inj ds0 ds Hwf0 Hwf Hbytes).
    subst ds0.
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj) [Hep Harm]]".
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(_ & Hpz & _)"; iExFalso; iApply (dinode_at_excl with "Hpz Hdn")].
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp0 (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    rewrite Hdeq in Hlok. rewrite Hdeq in Hrt.
    assert (Hnl0' : bv_unsigned (di_nlink dn') = 0) by exact (proj2 Hnl Hz).
    assert (Hnl0 : bv_unsigned (di_nlink dn) = 0).
    { rewrite -(proj1 Hnl). exact Hnl0'. }
    assert (Hw0 : (wl + wdu + wdt = 0)%nat)
      by exact (ireg_wle_zero (bv_unsigned (di_nlink dn)) _ (proj1 Hlok) Hnl0).
    destruct (ireg_sum_zero3 wl wdu wdt Hw0) as (Hzz1 & Hzz2 & Hzz3).
    assert (Hlok' : ireg_link_ok dn' (wl + wdu + wdt)).
    { rewrite Hzz1 Hzz2 Hzz3.
      split_and!; [lia | intros _; exact Hnl0' | rewrite Hnl0'; lia]. }
    assert (Hdir' : ireg_dir_ok dn' (wdu + wdt))
      by (rewrite Hzz2 Hzz3; exact (ireg_dir_ok_zero dn')).
    assert (Hwl0' : ireg_dir_wl0 dn' wl)
      by (rewrite Hzz1; exact (ireg_dir_wl0_zero dn')).
    assert (Hnr : bv_unsigned inum <> ireg_root)
      by exact (ireg_root_ok_ne _ dn _ Hrt Hnl0).
    assert (Hrt' : ireg_root_ok (bv_unsigned inum) dn' (wl + wdu + wdt))
      by exact (ireg_root_ok_nonroot _ dn' _ Hnr).
    assert (Hzm : bv_unsigned (di_nlink dn') = 0 ->
                  bv_unsigned (di_nlink (ds !!! islot inum)) = 0).
    { intros _. rewrite Hdeq. exact Hnl0. }
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    (* ===== THE DEPOSIT: rebind + escA_deposit + split + park PENDING ===== *)
    iDestruct "Hrf" as (ge0 gr0) "Hrf".
    iEval (rewrite /reg_full) in "Hrf".
    iDestruct "Hreg" as (mr) "[%Hcovr Hauthr]".
    iMod (ghost_map_update (ge, gr) with "Hauthr Hrf") as "[Hauthr Hrf]".
    iMod (escA_deposit (E ∖ ↑iregN) ge gr γi (bv_unsigned inum) Hesc_mask
            with "Hesc Hmk") as "#Hcom".
    iDestruct (reg_split (bv_unsigned inum) ge gr with "[Hrf]") as "[Hrh1 Hrh2]".
    { rewrite /reg_full. iExact "Hrf". }
    iAssert (ireg_registry nib) with "[Hauthr]" as "Hreg".
    { iExists (<[bv_unsigned inum := (ge, gr)]> mr). iSplitR; [| iExact "Hauthr"].
      iPureIntro. intros w Hw. destruct (decide (w = bv_unsigned inum)) as [->|Hne].
      - rewrite lookup_insert. done.
      - rewrite lookup_insert_ne; [exact (Hcovr w Hw) | congruence]. }
    iMod ("Hclose" with "[Ha Hreg Hfsb' Hdn Hla Hep Hslback Hback Hrh1 Hrh2]") as "_".
    { iNext. iExists m'. iFrame "Ha Hreg".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hdn Hla Hep Hslback Hrh1 Hrh2]").
      { intros j i Hne Hi. rewrite /m' lookup_insert_ne; [done |].
        rewrite (ireg_key_split inum). intros Hc.
        destruct (ireg_key_inj (ireg_bi inum) j (islot inum) i Hsl Hi Hc)
          as [Hj _].
        exact (Hne (eq_sym Hj)). }
      iExists (<[islot inum := dn']> ds).
      iSplitR; [iPureIntro; exact (diblk_wf_insert ds (islot inum) dn' Hwf Hdn') |].
      iSplitR.
      { iPureIntro. intros i Hi.
        destruct Hwf as [Hlen _].
        destruct (decide (i = islot inum)) as [->|Hne].
        - rewrite /m' -(ireg_key_split inum) lookup_insert.
          rewrite list_lookup_total_insert; [done | lia].
        - rewrite /m' lookup_insert_ne; last first.
          { rewrite (ireg_key_split inum). intros Hc.
            destruct (ireg_key_inj (ireg_bi inum) (ireg_bi inum)
                        (islot inum) i Hsl Hi Hc) as [_ Hi'].
            exact (Hne (eq_sym Hi')). }
          rewrite list_lookup_total_insert_ne; [| by apply not_eq_sym].
          exact (Hcp0 i Hi). }
      iSplitL "Hfsb'"; [iExact "Hfsb'" |].
      iApply ("Hslback" $! dn' with "[Hdn Hla Hep Hrh1 Hrh2]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl wdu wdt gl cl rl pl
                Hlok' Hrt' Hdir' Hwl0' Hpar
                with "Hla Hep Hdisj").
      iRight. iSplitR; [iPureIntro; exact Hz |].
      iSplitL "Hdn"; [iExact "Hdn" |].
      iSplitL "Hrh1"; [iExists ge, gr; iExact "Hrh1" |].
      iExists ge, gr. iFrame "Hrh2 Hcom". }
    iModIntro. iExact "Hcom".
  Qed.

End EscrowDeposit.
