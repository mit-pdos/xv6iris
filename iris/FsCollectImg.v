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
Require Import FsCollect.      (* [col_geom] *)
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
