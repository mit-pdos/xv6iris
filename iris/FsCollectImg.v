(* ====================================================================== *)
(*  FsCollectImg.v -- THE COLLECTION'S GEOMETRY, WITNESSED AT THE REAL      *)
(*  BOOT CONFIGURATION (durable-disk lane C-2; durable-fs-plan.md          *)
(*  section 7, the vacuity discipline)                                     *)
(*                                                                        *)
(*  [FsCollect.col_geom] is the ONE pure premise of the collection that    *)
(*  does not come off a resource: the superblock's own arithmetic, the     *)
(*  region's extent, and: a covered block is inside the bitmap's range.    *)
(*  That last one is what turns holding a block's bytes into a refutation  *)
(*  of its bit reading clear.  Plan section 7 rules that                   *)
(*  every such conjunct gets a non-vacuity witness AT THE REAL INSTANCE,   *)
(*  so here it is: [FsCfgBoot.fs_boot_image_wf] -- the ONE bundle both     *)
(*  adequacy theorems already carry, discharged at the literal mkfs image  *)
(*  by [FsAdequacyImg.fsimg_image_wf] -- yields it outright, with no new   *)
(*  image sweep and no new computation on the adequacy cone.               *)
(*                                                                        *)
(*  IT IS ITS OWN FILE for [FsCollect.v]'s sake: [FsCollect] must stay a   *)
(*  LEAF over the predicate layer (the commit's cone must not acquire the  *)
(*  boot chain), and [fs_boot_image_wf] lives in [FsCfgBoot].  Same        *)
(*  arrangement as [FsAdequacyImg] over [FsDurImg].                        *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list sets coPset namespaces bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import invariants.

Require Import SailStdpp.Values.  (* [mword] *)
Require Import RiscvLang.        (* [GenId] -- [log_ctx]'s swap receipt *)
Require Import RiscvPtsto.
Require Import Xv6G.
Require Import FsImg.
Require Import LogDefs.        (* [fs_home_set] *)
Require Import FsCrash.        (* [fs_blocks] *)
Require Import FsBoot.         (* [fs_cov_in] *)
Require Import FsCfgBoot.      (* [fs_boot_image_wf] *)
Require Import DinodeEnc.     (* [dinode], [di_type], [di_nlink]           *)
Require Import InodeRegion.   (* [free_node], [ireg_bare], [ireg_top_park] *)
Require Import FsStateEra.    (* [inode_owned_era] *)
Require Import FsCollect.      (* [col_geom], [col_bundle_free]           *)
Require Import BioDefs.        (* [bio_names] *)
Require Import FsBlocks.       (* [fs_names], [fsblock] *)
Require Import SbPark.         (* [sb_park], [sb_parked], [sb_park_acc]   *)
Require Import LogInv.         (* [log_ctx], [log_ctx_sb]                 *)
Require Import FsBytesGamma.   (* [gamma_blk_owned], the bridge           *)
Require Import FsStateDefs.    (* [blk_owned_q], [blk_owned_ne_full]      *)
Require Import FsState.        (* [sb_owned] -- what [col_hand] asks for  *)

Local Open Scope Z_scope.

(* THE BOOT BUNDLE YIELDS THE COLLECTION'S GEOMETRY.  Clause by clause:
   [cg_sbok] is W1's [FsImg.fs_sb_ok]; [cg_reg] is conjunct (6) against
   [FsImg.sbo_bmapstart] -- mkfs rounds [ninodes] up to a whole block, so
   the region is EXACTLY [[inodestart, bmapstart)] and [nib] blocks wide;
   [cg_nin] and [cg_wide] are conjuncts (3) and (4); and [cg_size] is
   [FsBoot.fs_cov_in] against conjunct (12) (the disk image is no larger
   than [size] blocks), which is the only place the bitmap's range meets
   the coverage set. *)
Lemma img_col_geom (dk : Z -> bv 8) (ndisk : nat) (sb : fs_sb) (nib : nat)
    (cov : gset Z) :
  fs_boot_image_wf dk ndisk sb nib cov ->
  col_geom sb (sb_inodestart sb) nib (fs_home_set cov (sb_logstart sb)).
Proof.
  intros (Hwf & Hrwf & Hnin & Hwide & Hnib0 & Hnibeq & Hcov & Hcovm & Hcovd
          & Hparse & Hus & Hnd & Hleq & Hbare & Hself).
  pose proof (fsimg_wf_sb (fs_blocks dk) sb Hwf) as Hsbok.
  split.
  - exact Hsbok.
  - reflexivity.
  - pose proof (sbo_bmapstart sb Hsbok). lia.
  - exact Hnin.
  - exact Hwide.
  - intros b Hb.
    rewrite /fs_home_set in Hb. apply elem_of_difference in Hb as [Hb _].
    destruct (Hcov b Hb) as [Hb0 Hbn]. lia.
Qed.

(* THE SUPERBLOCK'S BLOCK IS A HOME BLOCK, which is the half of
   [FsDurSnap.sk_sb] that is pure: block 1 is covered (mkfs's metadata
   range) and sits below the log, so [FsCollect.col_view] holds SOMETHING
   there and [sk_sb] is satisfied by construction at [fss_sbb S] := that
   value.  WHAT IS NOT PURE is [sk_parse] and [SB_BNO ∈ used]; both need
   block 1's byte run, which is [SbPark]'s park -- the accessors at the
   bottom of this file are what the collection reads it through. *)
Lemma img_sb_home (dk : Z -> bv 8) (ndisk : nat) (sb : fs_sb) (nib : nat)
    (cov : gset Z) :
  fs_boot_image_wf dk ndisk sb nib cov ->
  SB_BNO ∈ fs_home_set cov (sb_logstart sb).
Proof.
  intros (Hwf & Hrwf & Hnin & Hwide & Hnib0 & Hnibeq & Hcov & Hcovm & Hcovd
          & Hparse & Hus & Hnd & Hleq & Hbare & Hself).
  pose proof (fsimg_wf_sb (fs_blocks dk) sb Hwf) as Hsbok.
  pose proof (sbo_logstart sb Hsbok). pose proof (sbo_nlog sb Hsbok).
  pose proof (sbo_inodestart sb Hsbok). pose proof (sbo_bmapstart sb Hsbok).
  pose proof (sbo_ninodes sb Hsbok).
  assert (Hdiv : 0 <= sb_ninodes sb / 16) by (apply Z.div_pos; unfold ROOTINO in *; lia).
  assert (Hds : 1 < fs_data_start sb) by (unfold fs_data_start; lia).
  rewrite /fs_home_set. apply elem_of_difference. split.
  - apply Hcovm. rewrite /SB_BNO. lia.
  - rewrite /log_region_set. intros Hin.
    apply elem_of_union in Hin as [Hin | Hin].
    + apply elem_of_list_to_set, elem_of_list_fmap in Hin as (i & Heq & _).
      rewrite /log_slot_bno /SB_BNO in Heq. lia.
    + apply elem_of_singleton in Hin. rewrite /log_hdr_bno /SB_BNO in Hin. lia.
Qed.


(* ====================================================================== *)
(*  BLOCK 1, IN THE COLLECTION'S OWN VOCABULARY (durable-disk lane C-3a)   *)
(*                                                                        *)
(*  [SbPark] states the park in [FsBlocks]' spelling, because it sits      *)
(*  below [LogInv] and the abstract byte view does not.  This is the same  *)
(*  accessor read through [FsBytesGamma.gamma_blk_owned], i.e. at exactly  *)
(*  the conjunct [FsCollect.col_hand] asks for: [FsState.sb_owned].        *)
(*  Everything the collection concludes from block 1 is pure, so the       *)
(*  closing wand takes back the very resource it handed out.               *)
(* ====================================================================== *)

Section SbOwnedAcc.
  (* [log_ctx]'s OWN binder list, verbatim, plus [xv6G] for the byte view:
     a shorter one leaves [log_ctx]'s capacity parameters as undischarged
     evars at [Qed] (durable-notes, "a lemma's binder list must match the
     definition it is about"). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{GEN : GenId}.

  Lemma sb_park_owned_acc (E : coPset) (γfs : fs_names) (sb : fs_sb) :
    ↑sbN ⊆ E ->
    sb_park γfs sb ={E, E ∖ ↑sbN}=∗
      ∃ sbb : list (bv 8),
        sb_owned (fs_gamma_L γfs) sb sbb ∗
        (sb_owned (fs_gamma_L γfs) sb sbb ={E ∖ ↑sbN, E}=∗ True).
  Proof.
    intros HE. iIntros "#Hp".
    iMod (sb_park_acc E γfs sb HE with "Hp") as (bs) "(%Hparse & Hb & Hclose)".
    iModIntro. iExists bs.
    rewrite /sb_owned gamma_blk_owned.
    iSplitL "Hb".
    { iSplitL "Hb"; [iExact "Hb" | iPureIntro; exact Hparse]. }
    iIntros "[Hb _]". iApply ("Hclose" with "Hb").
  Qed.

  (* ...and off the bundle end_op threads.  The record is the one the park
     was born at; a caller that has to identify it with the boot
     configuration's holds the concrete [sb_park] instead (fsinit and
     initlog both do). *)
  Lemma log_ctx_sb_owned_acc (E : coPset) (γ : log_names) (bn : bio_names)
      (γfs : fs_names) (cov : gset Z) (logstart : Z) (dev : mword 32) :
    ↑sbN ⊆ E ->
    log_ctx γ bn γfs cov logstart dev ={E, E ∖ ↑sbN}=∗
      ∃ (sb : fs_sb) (sbb : list (bv 8)),
        ⌜fs_sb_ok sb⌝ ∗
        sb_owned (fs_gamma_L γfs) sb sbb ∗
        (sb_owned (fs_gamma_L γfs) sb sbb ={E ∖ ↑sbN, E}=∗ True).
  Proof.
    intros HE. iIntros "#Hctx".
    iDestruct (log_ctx_sb with "Hctx") as (sb) "[%Hok #Hp]".
    iMod (sb_park_owned_acc E γfs sb HE with "Hp") as (sbb) "[Hsb Hclose]".
    iModIntro. iExists sb, sbb.
    iSplitR; [iPureIntro; exact Hok |]. iFrame.
  Qed.

  (* NON-VACUITY, AND IT IS THE CLAUSE THE FRACTION EXISTS FOR.
     [FsDurSnap.sk_meta_used] says no inode owns block 1, and the
     collection reads that off the separating conjunction between the park
     and a bundle's block.  Here it is, end to end, off [log_ctx] alone:
     the park's FULL share excludes any other, whatever the bundle's is
     (fraction 1 for an unlocked inode, 3/4 for a read-locked one).  A
     [DfracDiscarded] park would not close this goal -- which is why the
     run is parked at fraction 1 and not made persistent. *)
  Lemma log_ctx_sb_not_owned (E : coPset) (γ : log_names) (bn : bio_names)
      (γfs : fs_names) (cov : gset Z) (logstart : Z) (dev : mword 32)
      (dq : dfrac) (b : Z) (bs : list (bv 8)) :
    ↑sbN ⊆ E ->
    log_ctx γ bn γfs cov logstart dev -∗
    blk_owned_q (fs_gamma_L γfs) dq b bs ={E}=∗
      ⌜b <> SB_BNO⌝ ∗ blk_owned_q (fs_gamma_L γfs) dq b bs.
  Proof.
    intros HE. iIntros "#Hctx Hblk".
    iMod (log_ctx_sb_owned_acc E γ bn γfs cov logstart dev HE with "Hctx")
      as (sb sbb) "(_ & Hsb & Hclose)".
    rewrite /sb_owned. iDestruct "Hsb" as "[Hsbb %Hparse]".
    iDestruct (blk_owned_ne_full (fs_gamma_L γfs) (fs_gamma_L_excl γfs)
                 dq SB_BNO b sbb bs with "Hsbb Hblk") as %Hne.
    iMod ("Hclose" with "[Hsbb]") as "_".
    { rewrite /sb_owned. iSplitL "Hsbb"; [iExact "Hsbb" |].
      iPureIntro; exact Hparse. }
    iModIntro. iSplitR; [iPureIntro; intros ->; exact (Hne eq_refl) | ].
    iExact "Hblk".
  Qed.

End SbOwnedAcc.

(* ====================================================================== *)
(*  SUPPLIER (D) AT THE BOOT STATE (durable-disk lane C-3c)                *)
(*                                                                        *)
(*  Plan section 7's discipline applied to the park: [InodeRegion.         *)
(*  ireg_top_park]'s tie is GUARDED by [di_type = 0], so a witness is owed *)
(*  that the guard really fires -- and at the mkfs image it fires at       *)
(*  nearly every inum of the region, since boot stocks EVERY free inum's   *)
(*  slot on the IN arm.  What the accessor then hands the commit is a      *)
(*  bundle at THE IMAGE'S OWN NODE, [FsCfgBoot.img_node] -- the very value *)
(*  [FsCfgBoot.img_nodes] puts in [InodeRegion.ftop_inv]'s map at boot --   *)
(*  so [FsCollect.col_hand]'s big-op is satisfied at the abstract state    *)
(*  the authority holds, and not at some node of the witness's choosing.   *)
(*                                                                        *)
(*  Conjunct (14) [FsImg.fs_region_bare] is the whole of what it costs,    *)
(*  and it is already in the bundle both adequacy theorems carry.          *)
(* ====================================================================== *)

Section CollectImgFree.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* a free inum's node at the image IS [InodeRegion.free_node] of its
     record: conjunct (14) makes the node bare, and a bare node has no
     freedom left ([InodeRegion.free_node_of_bare]) *)
  Lemma img_free_node (dk : Z -> bv 8) (ndisk : nat) (sb : fs_sb) (nib : nat)
      (cov : gset Z) (z : Z) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    0 <= z < 16 * Z.of_nat nib ->
    bv_unsigned (di_type (fs_dinode (fs_blocks dk) sb z)) = 0 ->
    img_node (fs_blocks dk) sb z = free_node (fs_dinode (fs_blocks dk) sb z).
  Proof.
    intros Hwf Hz Hty.
    destruct Hwf as (_ & Hrw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                     & Hbare & _).
    exact (free_node_of_bare (img_node (fs_blocks dk) sb z)
             (img_node_bare (fs_blocks dk) sb nib z Hbare
                (fs_region_wf_nlink _ _ _ Hrw) Hz Hty)).
  Qed.

  (* THE EXERCISE: the region's two halves at a free inum of the mkfs image
     are a [FsCollect.col_bundle] at the image's own node. *)
  Lemma img_col_bundle_free (dk : Z -> bv 8) (ndisk : nat) (sb : fs_sb)
      (nib : nat) (cov : gset Z) (γfs : fs_names) (γi : gname)
      (inum : bv 32) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    bv_unsigned (di_type (fs_dinode (fs_blocks dk) sb (bv_unsigned inum))) = 0 ->
    dinode_at γi inum (fs_dinode (fs_blocks dk) sb (bv_unsigned inum)) -∗
    ireg_top_park γfs (bv_unsigned inum)
      (fs_dinode (fs_blocks dk) sb (bv_unsigned inum)) -∗
    col_bundle γfs γi (bv_unsigned inum)
      (img_node (fs_blocks dk) sb (bv_unsigned inum)).
  Proof.
    intros Hwf Hlt Hty.
    pose proof (bv_unsigned_in_range _ inum) as [Hlo _].
    assert (Hz : 0 <= bv_unsigned inum < 16 * Z.of_nat nib) by lia.
    pose proof Hwf as Hwf'.
    destruct Hwf' as (_ & Hrw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & Hbare & _).
    assert (Hb : ireg_bare (fs_dinode (fs_blocks dk) sb (bv_unsigned inum))).
    { exact (ireg_bare_of_fn_bare (img_node (fs_blocks dk) sb (bv_unsigned inum))
               (img_node_bare (fs_blocks dk) sb nib (bv_unsigned inum) Hbare
                  (fs_region_wf_nlink _ _ _ Hrw) Hz Hty)). }
    assert (Hnl : bv_unsigned
                    (di_nlink (fs_dinode (fs_blocks dk) sb (bv_unsigned inum)))
                  = 0)
      by exact (fs_region_nlink_free (fs_blocks dk) sb nib (bv_unsigned inum)
                  (fs_region_wf_nlink _ _ _ Hrw) Hz Hty).
    rewrite (img_free_node dk ndisk sb nib cov (bv_unsigned inum) Hwf Hz Hty).
    iIntros "Hdn Hpk".
    iApply (col_bundle_free γfs γi inum
              (fs_dinode (fs_blocks dk) sb (bv_unsigned inum)) Hb Hnl Hty
              with "Hdn Hpk").
  Qed.

End CollectImgFree.
