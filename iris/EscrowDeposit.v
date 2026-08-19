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

   ---- WHAT IT RETIRES, AND THE ONE THING IT DOES NOT (increment IVa) ------

   Since iclaim-ledger.md §1.4 this accessor also RETIRES THE FREEZE: it takes
   the [FrzPost] token the walk carries from iput+0x8a and steps the column to
   [FrzOff] in the same region open that absorbs [dinode_at] and fills the
   escrow.  It has to take a TOKEN and not a premise -- see the note at the
   premise itself.

   §3.12's RULING A″ additionally asks the retire to hand back a SOLE-HOLDER
   WITNESS, parked by [InodeRegion.ireg_freeze_au] at the mint, so that a
   foreign idup's up-count can refute a standing [FrzPre] by fraction
   collision.  THAT WITNESS IS NOT HERE, and iclaim-ledger.md §3.13 records
   why it cannot be: every resource that collides with a foreign holder's
   supply is keyed by the itable SLOT [k] ([live_frac], [iref_frag],
   [slh_tok (icfg_isl k)], the [ientry k] cells), while [ireg_slot] -- the
   freeze arm -- is keyed by the INUM.  A parked [∃ k0, W k0] and a caller's
   slice at [k] compose to a perfectly valid element of the same map, so there
   is no validity goal to close.  The collision itself is right and already
   proven ([IcacheInv.live_whole_share_absurd]); only its home is open.
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
      (ds : list dinode) (ge gr gd : gname) (rg : bool) :
    ↑iregN ⊆ E ->
    ↑escAN (bv_unsigned inum) ⊆ E ∖ ↑iregN ->
    (bv_unsigned inum < 16 * Z.of_nat nib)%Z ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') = 0 ->
    di_nlink_stable dn' dn ->
    ireg_inv γi γfs inodestart nib -∗
    escA_inv ge gr gd γi (bv_unsigned inum) rg -∗
    dinode_at γi inum dn -∗
    (* THE FREEZE, RETIRED HERE (iclaim-ledger.md §1.4, and [ireg_free_au]'s
       own row in RULING A's mover table).  The deposit is a type-0 write over
       a slot the pin constrains, so it cannot re-park an untouched f column:
       it takes the [FrzPost] token the walk carries from iput+0x8a and steps
       the column back to [FrzOff], so the pin's post arm DISSOLVES exactly as
       the type goes to zero.  What comes back is [ifreeze_off], which is what
       the parked pool entry wants ([IcacheEscrow.ipool_shape]'s pending arm).
       WHY A TOKEN AND NOT A PREMISE: nothing in the depositor's hand refutes a
       standing freeze at a LIVE record -- [dn] has a nonzero type and a zero
       nlink, which is precisely what both frozen phases admit -- so the pin at
       the old record is no help and the column has to be OWNED to be moved. *)
    (* THE DEPOSIT TICKET, not the phase fragment (iclaim-ledger.md §3.16).
       A⁗ moved the standing [ifreeze_post] into the ESCROW's own EMPTY state
       -- it has to live somewhere the pool's await arm can be refuted from,
       and the walk gave it up at iput+0x8a when it minted the escrow.  What
       the depositor carries from +0x8a to +0xba instead is this ticket, which
       is also what rules out a second deposit at the same escrow.  The retire
       therefore happens INSIDE [escA_deposit_acc]'s opening: the token comes
       out at [FrzPost], the column steps to [FrzOff], and the token goes back
       in at [FrzOff] for whoever peels the pool entry next. *)
    redeem_ticketA gd -∗
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock γfs (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock γfs (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       (* RULING G, THE RETURN LEG (iclaim-ledger.md §6′).  iput BORROWS the
          regime -- the sealed [ireg_open] a runtime freezer must exhibit, or
          the exclusive [ireg_boot] ireclaim's boot thread carries instead --
          and this is where it gives it back.  It is not invented here: the
          slot's own boot-shelter clause (§2.3) is on its SEALED arm at this
          open, because the column stands at [FrzPost] and ⌜f = FrzOff⌝ is
          therefore refuted, so the disjunction is simply lifted out of the
          record the freeze window opened.  Without it a boot-thread iput
          could lend [ireg_boot] and never get it back, and ireclaim's loop
          -- which needs it on every iteration -- would not close. *)
       ={E ∖ ↑iregN, E}=∗ committedA ge ∗ ireg_regime rg).
  Proof.
    iIntros (HE Hesc_mask Hin Hwf Hdn' Hz Hnl) "#Hinv #Hesc Hdn Hdep".
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
    (* THE LEDGER's FULL ARITY since §2.2/§2.3: the [icnt] half, the two
       in-transition pins and the f column's boot-shelter clause all ride in
       the ∃ beside the seven original columns.  [ireg_free_au]'s pattern
       verbatim -- this accessor IS that lemma with the closing action
       swapped, and every consumer of the slot destructures it identically. *)
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
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
    (* THE CLAIM PIN IS VACUOUS HERE (iclaim-ledger.md §2.4): the caller's own
       [dinode_at] put this open on the MARKED arm, whose clause says
       [cl = None].  The deposit is a byte-writing mover, so §2.4's "writes
       cannot dent the pin" applies to it exactly as it does to
       [ireg_free_au]: no premise, no obligation, nothing to re-establish. *)
    assert (Hclm' : ireg_claim_ok cl (Some (Excl FrzOff)) dn')
      by (rewrite (proj2 Ht2); exact I).
    (* THE RETIRE (§1.4).  The token pins the column at [FrzPost]
       ([link_freeze_agree]) and the fragment-side step hands it back at
       [FrzOff]; the pin at the type-0 record about to be parked is then
       vacuous, which is the whole reason the mover takes the token. *)
    (* the escrow opens HERE, and its EMPTY state hands over the standing
       freeze; it closes again three lines below the region's re-park, with
       the marker and the retired token. *)
    iMod (escA_deposit_acc (E ∖ ↑iregN) ge gr gd γi (bv_unsigned inum) rg
            Hesc_mask with "Hesc Hdep") as "[Hfz Hescl]".
    iDestruct (ireg_rcol_freeze_agree with "Hla Hfz") as %->.
    (* RULING G's EXTRACTION.  With the column pinned at [FrzPost] the
       boot-shelter clause's left arm is a refutable equation, so what the
       slot is holding is the REGIME the freezer lent at the mint.  The
       re-park below owes nothing in its place: it lands on [FrzOff], where
       the clause's left arm holds outright. *)
    (* RULING G' (iclaim-ledger.md §6''): the walk's own [ifreeze_post rg]
       token has just pinned this slot's f column at [FrzPost rg]
       ([ireg_rcol_freeze_agree], one line above), so the AGREEMENT selects the
       parked arm and what comes out is the INDEXED regime -- the very arm the
       mint was handed at iput+0x50, not an un-indexed disjunction ireclaim
       could not re-bind. *)
    iAssert (ireg_regime rg)%I with "[Hfdisj]" as "Hgreg".
    { iApply (ireg_fsh_post_acc rg with "Hfdisj"). }
    (* THE FREEZE RECEIPT RIDES THROUGH (iclaim-ledger.md §3.14 as built):
       the deposit runs at [FrzPost] and leaves [FrzOff], and neither is
       [FrzPre], so the slot's receipt clause is on its [frzown] arm both
       sides and this mover neither takes nor returns it. *)
    iDestruct (ireg_frzc_off_acc (bv_unsigned inum) (Some (Excl (FrzPost rg)))
                 ltac:(reflexivity) with "Hfrcp") as "[Hrcpt Hmr]".
    (* RULING R's (R2), PAID BY THE DEPOSIT (§5'.2, landed by 7a-wire).  This
       is the deposit's own type-0 write, it runs at [FrzPost], and the freeze
       pin puts the in-core count at ZERO there ([Hcn0]) -- so (R1) collapses
       both r columns and the clause at the record this mover parks is
       [ireg_ref_ok_zero].  No premise and no token beyond the one the
       deposit already retires. *)
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    assert (Hcn0 : cn = 0%nat) by exact (proj2 (proj2 Hfrz)).
    destruct (ireg_ref_ok_count0 rl rcl cn cl (ds !!! islot inum) Href Hcn0)
      as [Hrl0 Hrcl0].
    assert (Href0 : forall d0 : dinode, ireg_ref_ok rl rcl cn cl d0)
      by (intros d0; rewrite Hrl0 Hrcl0; exact (ireg_ref_ok_zero cn cl d0)).
    iMod (link_freeze_step _ _ _ _ _ _ _ _ (FrzPost rg) FrzOff with "Hla Hfz")
      as "[Hla Hoff]".
    iDestruct (ireg_rcol_intro (bv_unsigned inum) wl wdu wdt gl cl rl pl
                 (Some (Excl FrzOff)) cn rcl dn' (Href0 dn')
                 with "Hla") as "Hla".
    assert (Hfrz' : ireg_frz_ok (Some (Excl FrzOff)) cn dn')
      by exact (ireg_frz_ok_off cn dn').
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
    iMod ("Hescl" with "Hmk Hoff") as "#Hcom".
    iDestruct (reg_split (bv_unsigned inum) ge gr with "[Hrf]") as "[Hrh1 Hrh2]".
    { rewrite /reg_full. iExact "Hrf". }
    iAssert (ireg_registry nib) with "[Hauthr]" as "Hreg".
    { iExists (<[bv_unsigned inum := (ge, gr)]> mr). iSplitR; [| iExact "Hauthr"].
      iPureIntro. intros w Hw. destruct (decide (w = bv_unsigned inum)) as [->|Hne].
      - rewrite lookup_insert. done.
      - rewrite lookup_insert_ne; [exact (Hcovr w Hw) | congruence]. }
    iMod ("Hclose" with "[Ha Hreg Hfsb' Hdn Hla Hep Hslback Hback Hrh1 Hrh2 Hcnt Hrcpt Hmr]") as "_".
    { iNext. iExists m'. iFrame "Ha Hreg".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hdn Hla Hep Hslback Hrh1 Hrh2 Hcnt Hrcpt Hmr]").
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
      iApply ("Hslback" $! dn' with "[Hdn Hla Hep Hrh1 Hrh2 Hcnt Hrcpt Hmr]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl wdu wdt gl cl rl pl
                (Some (Excl FrzOff)) cn
                Hlok' Hrt' Hdir' Hwl0' Hpar Hclm' Hfrz'
                with "Hla Hep Hdisj Hcnt [] [Hrcpt Hmr]").
      { iApply ireg_fsh_off. }
      { iApply (ireg_frzc_off_intro (bv_unsigned inum) (Some (Excl FrzOff))
                  ltac:(reflexivity) with "Hrcpt Hmr"). }
      iRight. iSplitR; [iPureIntro; exact Hz |].
      iSplitL "Hdn"; [iExact "Hdn" |].
      iSplitL "Hrh1"; [iExists ge, gr; iExact "Hrh1" |].
      iExists ge, gr. iFrame "Hrh2 Hcom". }
    iModIntro. iSplitR; [iExact "Hcom" | iExact "Hgreg"].
  Qed.

End EscrowDeposit.
