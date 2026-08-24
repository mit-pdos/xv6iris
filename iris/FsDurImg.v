(* ====================================================================== *)
(* FsDurImg.v -- THE DURABLE FILE SYSTEM, BUILT FROM AN IMAGE              *)
(*                                                                        *)
(* durable-disk 2c-img, leaf 2.  Design of record:                        *)
(* claude-notes/design/fs-state.md sections 1-4;                          *)
(* claude-notes/projects/durable-disk.md item 2c, finding (iv).           *)
(*                                                                        *)
(* [FsCrash.P_fs_alloc] fills the durable byte map [riscv_dview_name] with *)
(* [LogDefs.fs_dbytes D0] -- the flat byte elements of the boot era's      *)
(* committed BLOCK view, which at a clean image is                        *)
(* [fs_restrict (fs_blocks dk) (fs_home_set cov logstart)].  Stage 2c's    *)
(* [P_wf] is not that blob but [FsState.fs_view Gamma_D].  THIS FILE IS    *)
(* THE ONE CONVERSION, and it is where the image is decoded.               *)
(*                                                                        *)
(* IT COMPUTES NOTHING AND NAMES NO LITERAL IMAGE (ruling R3, as           *)
(* [FsCfgBoot] follows it): every image fact arrives as a HYPOTHESIS, in   *)
(* [FsCfgBoot.fs_boot_image_wf]'s own vocabulary, and both adequacy        *)
(* theorems already carry that bundle.  The literal-image discharge stays  *)
(* in [FsImgCheck.v]/[FsAdequacyImg.v] and does not move.                  *)
(*                                                                        *)
(* THREE THINGS A READER SHOULD KNOW BEFORE ANYTHING ELSE.                 *)
(*                                                                        *)
(* (1) [Gamma_D] IS [FsBytesGamma.fs_gamma_L] AT A DURABLE NAME BUNDLE.    *)
(*     [fs_gamma_L] reads exactly three fields of [FsBlocks.fs_names] --   *)
(*     [fs_bytes], [fs_link], [fs_top] -- so filling those three with the  *)
(*     DURABLE gnames makes [Gamma_D] an instance of the same constructor  *)
(*     ([fs_gamma_dur] below is [reflexivity]), and every lemma the tree   *)
(*     states at [fs_gamma_L] -- [FsStateEra.inode_blocks_era],            *)
(*     [FsStateEra.ind_res_era], [FsImgBridge.img_inode_blocks_res] --     *)
(*     applies verbatim at the durable view.  None of those three opens an *)
(*     invariant or reads the logged view; each is pure resource           *)
(*     shuffling over [FsBytesGamma.gamma_blk_owned].                      *)
(*     THE PROPER FIX is to make those three Gamma-GENERIC (they use only  *)
(*     [gamma_blk_owned]), which this additive lane could not do; the      *)
(*     bundle below is the standing workaround and should go when they     *)
(*     move.  The two cache-side fields are never read and are filled with *)
(*     the byte gname rather than fresh ones, so nothing is allocated.     *)
(*                                                                        *)
(* (2) THE FREE RECORDS NEED THEIR OWN SWEEP: CONJUNCT (14).              *)
(*     [FsState.fs_inodes] iterates [inode_owned] over the WHOLE inode     *)
(*     map, and [inode_owned] carries [FsStateInode.inode_local].  At a    *)
(*     LIVE inum that is [FsStateEra.inode_local_of_ok_rec] off W3/W6/W8   *)
(*     as [FsCfgBoot] already does it; at a FREE one (type 0) NOTHING in   *)
(*     [fsimg_wf] or [fs_region_wf] constrains the record's [size] or      *)
(*     [addrs], so [inl_size] and [inl_covers] are not derivable -- both   *)
(*     would be false of a garbage type-0 record.  [FsImg.fs_region_bare]  *)
(*     is the sweep, in [FsImg.fs_region_free]'s own idiom and reading the *)
(*     same thirteen inode blocks; [FsImgCheck.fsimg_region_bare]          *)
(*     discharges it at the literal image.                                 *)
(*                                                                        *)
(* (3) THE LINK FAMILY'S VALIDITY IS A THEOREM, and it costs ONE MORE      *)
(*     IMAGE SWEEP: CONJUNCT (15).  [FsState.fs_boot_alloc_at] needs       *)
(*     [✓ FsState.link_elem I]; [FsState.v]'s header says a map read off   *)
(*     the image discharges it from W9 ([FsImg.fs_links_wf]) plus conjunct *)
(*     (13) ([FsImg.fs_links_eq]).  Those two are NOT enough, because the  *)
(*     image's ticket discipline ([FsImg.fs_rec_ticket], which exempts a   *)
(*     record naming its OWN home under ANY name) and the RA's             *)
(*     ([FsStateInode.ent_tokenless], which exempts only the two dot       *)
(*     NAMES) disagree on exactly one shape: a root record called "foo"    *)
(*     pointing at the root.  [FsImg.fs_root_no_self] rules that shape     *)
(*     out, and section 9 then PROVES [img_link_valid] -- W9 forces the    *)
(*     image to have exactly ONE directory, so the family is one authority *)
(*     per inum composed with the root's outgoing tokens, and the tokens   *)
(*     are covered record by record.                                       *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl numbers.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import RiscvPtsto.
(* EARLY, before the block layer: [FsState] exports four names that collide
   with live ones ([fs_view], [link_auth], [byte_range], [blk_owned]) and
   the LAST import wins -- durable-notes.md. *)
Require Import FsState.
Require Import BioDefs.
Require Import BitmapEnc.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.
Require Import InodeInv.
Require Import InodeLock.
Require Import Xv6Cameras.
Require Import IcacheEscrow.    (* [region_inums] *)
Require Import IcacheBoot.      (* [diblk_bytes_surj] *)
Require Import FsBlocks.
Require Import FsBoot.          (* [big_sepS_carve] / [big_sepS_split_sub] *)
Require Import FsCrash.
Require Import LogDefs.
Require Import FsImg.
Require Import FsImgBridge.
Require Import FsStateBitmap.
Require Import FsStateEra.
Require Import FsBytesGamma.
Require Import FsCfgBoot.       (* [img_nodes] / [fs_boot_image_wf] *)
Require Import Xv6G.
(* LAST: it re-exports [FsStateDefs], whose [byte_range]/[blk_owned] must
   win over the block layer's twins. *)
Require Import FsDurBytes.
(* the durable tie's vocabulary (durable-disk 3b'): the object/kind algebra
   and the bridge [FsCrash.P_fs_alloc] now has to be handed at the image *)
Require Import FsDurObj.
Require Import FsDurWire.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  WHERE THE TWO EXTRA IMAGE SWEEPS LIVE                             *)
(* ===================================================================== *)

(*  [FsImg.fs_region_bare] (conjunct (14)) and [FsImg.fs_root_no_self]
    (conjunct (15)) are stated in [FsImg.v], beside [fs_region_free] and
    [fs_links_eq] whose idiom they follow, and discharged at the literal
    image by [FsImgCheck.fsimg_region_bare] / [fsimg_root_no_self].  This
    file only CONSUMES them: (14) in section 2a, (15) in section 10.       *)

(* ===================================================================== *)
(*  2.  THE IMAGE'S NODE, READ                                            *)
(* ===================================================================== *)

(* the three [fn_*] readings of [FsCfgBoot.img_node] that this file uses,
   each one delta-step off [FsStateEra.era_node_*] *)
Lemma img_node_rec (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fn_rec (img_node P sb z) = fs_dinode P sb z.
Proof. reflexivity. Qed.

Lemma img_node_ent (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fn_ent (img_node P sb z) = bm_ent (img_blkmap P (fs_dinode P sb z)).
Proof. reflexivity. Qed.

Lemma img_node_blk (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fn_blk (img_node P sb z)
  = node_blk (img_blkmap P (fs_dinode P sb z))
             (fs_data_of P (fs_dinode P sb z)).
Proof. reflexivity. Qed.

(* ---- 2a. A FREE INUM'S NODE IS BARE --------------------------------- *)

Lemma img_node_bare (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) (z : Z) :
  fs_region_bare P sb nib = true -> fs_region_nlink P sb nib = true ->
  0 <= z < 16 * Z.of_nat nib ->
  bv_unsigned (di_type (fs_dinode P sb z)) = 0 ->
  fn_bare (img_node P sb z).
Proof.
  intros Hbare Hnl Hz Hty.
  set (dn := fs_dinode P sb z).
  assert (Hwf : length (di_addrs dn) = 13%nat) by exact (fs_dinode_wf P sb z).
  assert (Ha : forall k : nat, (k < 13)%nat ->
                 bv_unsigned (di_addrs dn !!! k) = 0)
    by (intros k Hk; exact (fs_region_bare_addr P sb nib z k Hbare Hz Hty Hk)).
  assert (Hsz : bv_unsigned (di_size dn) = 0)
    by exact (fs_region_bare_size P sb nib z Hbare Hz Hty).
  (* the addresses, as a list *)
  assert (Haddrs : di_addrs dn = replicate 13 (bv_0 32)).
  { apply list_eq. intros k.
    destruct (Nat.lt_ge_cases k 13) as [Hk | Hk].
    - rewrite (lookup_replicate_2 _ _ _ Hk).
      destruct (lookup_lt_is_Some_2 (di_addrs dn) k ltac:(lia)) as [a Hk'].
      rewrite Hk'. f_equal. apply bv_eq.
      rewrite -(list_lookup_total_correct _ _ _ Hk') (Ha k Hk).
      by change (bv_unsigned (bv_0 32)) with 0.
    - assert (H1 : di_addrs dn !! k = None)
        by (apply lookup_ge_None; lia).
      assert (H2 : (replicate 13 (bv_0 32) : list (bv 32)) !! k = None)
        by (apply lookup_ge_None; rewrite length_replicate; lia).
      rewrite H1 H2 //. }
  assert (Hind : bv_unsigned (bm_ind (img_blkmap P dn)) = 0).
  { rewrite img_blkmap_ind. apply Ha. lia. }
  (* the indirect entries, as a list *)
  assert (Hent : bm_ent (img_blkmap P dn) = replicate FS_NINDIRECT (bv_0 32)).
  { rewrite (img_blkmap_noind P dn Hind). rewrite /NINDIRECT /FS_NINDIRECT //. }
  (* every slot reads zero, so the node owns no block *)
  assert (Hget : forall k : nat, (k < MAXFILE)%nat ->
                   bv_unsigned (blkmap_get (img_blkmap P dn) k) = 0).
  { intros k Hk. rewrite (img_blkmap_get P dn k Hwf Hk) /fs_blk_addr.
    destruct (Nat.ltb_spec k FS_NDIRECT) as [Hd | Hd].
    - apply Ha. unfold FS_NDIRECT in Hd. lia.
    - rewrite /fs_ind_ents. cbv zeta.
      rewrite (proj2 (Z.eqb_eq _ _) (Ha 12%nat ltac:(lia))).
      rewrite lookup_total_replicate_2; [reflexivity |].
      unfold MAXFILE, NDIRECT, NINDIRECT, FS_MAXFILE, FS_NDIRECT,
             FS_NINDIRECT in *. lia. }
  rewrite /fn_bare img_node_rec img_node_ent img_node_blk.
  split; [exact Haddrs |].
  split; [exact Hent |].
  split.
  { apply map_eq. intros k. rewrite node_blk_lookup lookup_empty.
    case_decide as Hc; [| reflexivity].
    exfalso. destruct Hc as [Hk Hnz]. apply Hnz. exact (Hget k Hk). }
  split.
  { rewrite /fn_size img_node_rec. exact Hsz. }
  rewrite /fn_nlink img_node_rec.
  rewrite (fs_region_nlink_free P sb nib z Hnl Hz Hty). reflexivity.
Qed.

Lemma img_inode_local_free (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  fs_region_bare P sb nib = true -> fs_region_nlink P sb nib = true ->
  0 <= z < 16 * Z.of_nat nib ->
  bv_unsigned (di_type (fs_dinode P sb z)) = 0 ->
  inode_local z (img_node P sb z).
Proof.
  intros Hbare Hnl Hz Hty.
  apply (inode_local_bare z (img_node P sb z)
           (img_node_bare P sb nib z Hbare Hnl Hz Hty)).
  left. rewrite /fn_type img_node_rec. exact Hty.
Qed.

(* ---- 2b. A LIVE INUM'S NODE, exactly as [FsCfgBoot] reads it --------- *)

Lemma img_inode_ok_at (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z)
    (z : Z) :
  fsimg_wf P sb = true -> fs_blocks_full P ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
  0 <= z < FsImg.sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
  inode_ok cov (sb_logstart sb) (fs_dinode P sb z)
    (img_blkmap P (fs_dinode P sb z)) (fs_data_of P (fs_dinode P sb z)).
Proof.
  intros Hwf Hfull Hcov Hran Hty.
  exact (img_inode_ok P sb cov (sb_logstart sb) (fs_dinode P sb z)
           (fs_dinode_wf P sb z) (fsimg_wf_sb P sb Hwf) eq_refl Hfull Hcov
           (fsimg_wf_inode P sb z Hwf Hran Hty) Hty
           (fsimg_wf_slot_inj P sb z Hwf Hran Hty)).
Qed.

Lemma img_inode_local_live (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z)
    (nib : nat) (z : Z) :
  fsimg_wf P sb = true -> fs_region_nlink P sb nib = true ->
  fs_blocks_full P ->
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
  0 <= z < FsImg.sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
  inode_local z (img_node P sb z).
Proof.
  intros Hwf Hrnl Hfull Hnin Hcov Hran Hty.
  set (dn := fs_dinode P sb z).
  assert (Hok : fs_inode_ok P sb dn)
    by exact (fsimg_wf_inode P sb z Hwf Hran Hty).
  assert (Hdir : bv_unsigned (di_type dn) = T_DIR_z -> fs_dir_ok P sb z dn)
    by (intros Hd; exact (fsimg_wf_dir P sb z Hwf Hran Hd)).
  (* the three record-only facts, each off the sweep that proves it *)
  assert (Hrl : inode_rec_local dn).
  { split_and!.
    - right. exact (fio_type P sb dn Hok).
    - apply (fs_region_nlink_short P sb nib z Hrnl). lia.
    - intros Hd. exact (fdo_gran P sb z dn (Hdir Hd)). }
  apply (inode_local_of_ok_rec z cov (sb_logstart sb) dn
           (img_blkmap P dn) (fs_data_of P dn)
           (img_inode_ok_at P sb cov z Hwf Hfull Hcov Hran Hty) Hrl).
  - exact (img_dir_uniq P sb z dn Hdir).
  - intros Hd Hnl0. exact (fsimg_wf_dots P sb z Hwf Hran Hd Hd Hnl0).
Qed.

(* ...and the two arms as ONE fact over the whole region *)
Lemma img_inode_local (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z)
    (nib : nat) (z : Z) :
  fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
  fs_region_bare P sb nib = true ->
  fs_blocks_full P ->
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
  z ∈ region_inums nib ->
  inode_local z (img_node P sb z).
Proof.
  intros Hwf Hrw Hbare Hfull Hnin Hcov Hz.
  apply region_inums_spec in Hz.
  destruct (decide (bv_unsigned (di_type (fs_dinode P sb z)) = 0))
    as [H0 | Hnz].
  - exact (img_inode_local_free P sb nib z Hbare
             (fs_region_wf_nlink _ _ _ Hrw) Hz H0).
  - assert (Hran : 0 <= z < FsImg.sb_ninodes sb).
    { split; [lia |].
      destruct (Z_lt_ge_dec z (FsImg.sb_ninodes sb)) as [Hlt | Hge];
        [exact Hlt |].
      exfalso. apply Hnz.
      exact (fs_region_free_spec P sb nib z (fs_region_wf_free _ _ _ Hrw)
               ltac:(lia) ltac:(lia) ltac:(lia)). }
    exact (img_inode_local_live P sb cov nib z Hwf
             (fs_region_wf_nlink _ _ _ Hrw) Hfull Hnin Hcov Hran Hnz).
Qed.

(* ===================================================================== *)
(*  3.  THE DURABLE VIEW, AS AN INSTANCE OF THE ERA'S CONSTRUCTOR         *)
(* ===================================================================== *)

Section DurImg.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* THE DURABLE NAME BUNDLE -- header (1).  [fs_gamma_L] reads exactly
     [fs_bytes], [fs_link] and [fs_top]; the two cache-side fields are
     never read, so they are filled with the byte gname rather than with
     fresh ones and nothing is allocated. *)
  Definition fs_dur_bundle (g : gname) (Gd : fs_dur_names) : fs_names :=
    MkFsNames g g g (fdn_link Gd) (fdn_top Gd).

  Lemma fs_gamma_dur (g : gname) (Gd : fs_dur_names) :
    fs_gamma_L (fs_dur_bundle g Gd) = fs_gamma_D g Gd.
  Proof. reflexivity. Qed.

  (* ...so the block layer's own block ownership IS the durable view's *)
  Lemma dur_blk_owned (g : gname) (Gd : fs_dur_names) (b : Z)
      (bs : list (bv 8)) :
    blk_owned (fs_gamma_D g Gd) b bs ⊣⊢ fsblock g b bs.
  Proof.
    rewrite -(fs_gamma_dur g Gd).
    exact (gamma_blk_owned (fs_dur_bundle g Gd) b bs).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  ONE LIVE INODE'S FOOTPRINT                                     *)
  (*                                                                      *)
  (*  [FsImgBridge.img_inode_blocks_res] turns one inode's block SET into *)
  (*  [InodeInv]'s slot-keyed pair; [FsStateEra.inode_blocks_era] /       *)
  (*  [ind_res_era] read that pair as the era vocabulary's own.  Both are *)
  (*  stated at [fs_gamma_L], and the bundle above is what makes them     *)
  (*  apply at [Gamma_D].                                                 *)
  (* ------------------------------------------------------------------ *)

  Lemma img_inode_phi_res (g : gname) (Gd : fs_dur_names)
      (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z) (nib : nat) (z : Z) :
    fsimg_wf P sb = true -> fs_region_nlink P sb nib = true ->
    fs_blocks_full P ->
    FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
    (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
    0 <= z < FsImg.sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
    ([∗ set] b ∈ fs_inode_blocks_set P sb z,
       blk_owned (fs_gamma_D g Gd) b (P b)) -∗
    ([∗ map] k ↦ bs ∈ fn_blk (img_node P sb z),
       blk_owned (fs_gamma_D g Gd) (fn_naddr (img_node P sb z) k) bs)
      ∗ ind_owned (fs_gamma_D g Gd) (img_node P sb z).
  Proof.
    intros Hwf Hrnl Hfull Hnin Hcov Hran Hty.
    pose proof (fsimg_wf_inode P sb z Hwf Hran Hty) as Hok.
    pose proof (fsimg_wf_slot_inj P sb z Hwf Hran Hty) as Hinj.
    pose proof (img_inode_local_live P sb cov nib z Hwf Hrnl Hfull Hnin Hcov
                  Hran Hty) as Hl.
    pose proof (node_shape_ok_of_inode_ok cov (sb_logstart sb)
                  (fs_dinode P sb z) (img_blkmap P (fs_dinode P sb z))
                  (fs_data_of P (fs_dinode P sb z))
                  (img_inode_ok_at P sb cov z Hwf Hfull Hcov Hran Hty))
      as Hshape.
    assert (Hbm : bm_of (img_node P sb z) = img_blkmap P (fs_dinode P sb z))
      by exact (bm_of_era_node _ _ _ Hshape).
    iIntros "H".
    (* to the block layer's own spelling of a block *)
    iAssert ([∗ set] b ∈ fs_inode_blocks_set P sb z,
               fsblock (fs_bytes (fs_dur_bundle g Gd)) b (P b))%I
      with "[H]" as "H".
    { iApply (big_sepS_mono with "H"). intros b _. rewrite dur_blk_owned //. }
    rewrite /fs_inode_blocks_set.
    iDestruct (img_inode_blocks_res (fs_dur_bundle g Gd) P sb
                 (fs_dinode P sb z) (fs_dinode_wf P sb z) Hfull Hok Hinj
                 with "H") as "[Hb Hi]".
    rewrite -(fs_gamma_dur g Gd).
    rewrite -(inode_blocks_era (fs_dur_bundle g Gd) z (img_node P sb z) Hl).
    rewrite -(ind_res_era (fs_dur_bundle g Gd) (img_node P sb z)).
    iSplitL "Hb"; [| rewrite Hbm; iExact "Hi"].
    rewrite Hbm.
    rewrite (inode_blocks_data_ext (fs_dur_bundle g Gd)
               (img_blkmap P (fs_dinode P sb z))
               (fs_data_of P (fs_dinode P sb z))
               (fn_data (img_node P sb z))); [iExact "Hb" |].
    intros k Hk. symmetry. exact (fn_data_era_node _ _ _ k Hshape Hk).
  Qed.

End DurImg.

(* ===================================================================== *)
(*  5.  THE INODE REGION'S RECORDS                                        *)
(*                                                                        *)
(*  [FsStateInode.rec_owned_at_diblk] is the sixteen-fold split of ONE    *)
(*  inode block at the region's own numbering; this is that at the        *)
(*  image's decoded records, and then over the whole region.  Nothing     *)
(*  here reads a ghost name, so the section binds a bare [Σ].             *)
(* ===================================================================== *)

Section DurImgRec.
  Context {Σ : gFunctors}.
  Implicit Types Gam : fs_view_names Σ.

  (* a range of [m * n], as [n] runs of [m].  Generic; it belongs beside
     [FsStateInode.big_sepL_seq0] and should move there. *)
  Lemma big_sepL_seq_chunks (Phi : nat -> iProp Σ) (m n : nat) :
    ([∗ list] i ∈ seq 0 n, [∗ list] k ∈ seq 0 m, Phi (m * i + k)%nat)
    ⊣⊢ ([∗ list] j ∈ seq 0 (m * n), Phi j).
  Proof.
    induction n as [| n IH].
    - rewrite Nat.mul_0_r //.
    - rewrite seq_S big_sepL_app big_sepL_cons big_sepL_nil right_id.
      rewrite Nat.add_0_l IH.
      replace (m * S n)%nat with (m * n + m)%nat by lia.
      rewrite seq_app big_sepL_app.
      apply bi.sep_proper; [done |].
      replace (seq (0 + m * n)%nat m) with (seq (m * n + 0)%nat m)
        by (f_equal; lia).
      rewrite -(fmap_add_seq (m * n)%nat 0%nat m) big_sepL_fmap.
      apply big_sepL_proper. intros k j Hk.
      apply lookup_seq in Hk as [-> _]. rewrite Nat.add_0_l //.
  Qed.

  (* ONE INODE BLOCK'S SIXTEEN RECORDS.  The block's bytes decode to SOME
     record list ([IcacheBoot.diblk_bytes_surj], which needs only the
     block's length), and [FsImg.fs_dinode_of_diblk] says that list's slot
     [k] IS the record [FsImg]'s own reader produces at inum [16*bi + k]. *)
  Lemma img_recs_of_block Gam (P : Z -> list (bv 8)) (sb : fs_sb)
      (nib bi : nat) :
    fs_blocks_full P -> (bi < nib)%nat -> 16 * Z.of_nat nib <= 2 ^ 32 ->
    blk_owned Gam (FsImg.sb_inodestart sb + Z.of_nat bi)
                  (P (FsImg.sb_inodestart sb + Z.of_nat bi))
    ⊢ [∗ list] k ∈ seq 0 16,
        rec_owned Gam sb (Z.of_nat (16 * bi + k)%nat)
                  (fs_dinode P sb (Z.of_nat (16 * bi + k)%nat)).
  Proof.
    intros Hfull Hbi Hnib.
    destruct (diblk_bytes_surj
                (P (FsImg.sb_inodestart sb + Z.of_nat bi)) (Hfull _))
      as (ds & Hdwf & Hde).
    iIntros "Hb". rewrite /blk_owned. iDestruct "Hb" as "[_ Hb]".
    rewrite Hde.
    rewrite (rec_owned_at_diblk Gam (FsImg.sb_inodestart sb) (Z.of_nat bi)
               ds Hdwf).
    iApply (big_sepL_mono with "Hb"). intros j k Hk.
    apply lookup_seq in Hk as [-> Hlt].
    (* the inum, and the two arithmetic readings of it *)
    assert (Hz : Z.of_nat (16 * bi + j)%nat = 16 * Z.of_nat bi + Z.of_nat j)
      by lia.
    assert (Hrng : 0 <= Z.of_nat (16 * bi + j)%nat < 2 ^ 32) by lia.
    assert (Hbv : bv_unsigned (fs_inum_bv (Z.of_nat (16 * bi + j)%nat))
                  = Z.of_nat (16 * bi + j)%nat).
    { rewrite /fs_inum_bv. apply Z_to_bv_small.
      assert (Hm : bv_modulus 32 = 2 ^ 32) by (vm_compute; reflexivity).
      rewrite Hm. lia. }
    assert (Hslot : islot (fs_inum_bv (Z.of_nat (16 * bi + j)%nat)) = j).
    { rewrite /islot Hbv Hz.
      rewrite (Z.mul_comm 16 (Z.of_nat bi)) Z.add_comm Z_mod_plus_full.
      rewrite Z.mod_small; [lia | lia]. }
    assert (Hblk : P (IBLOCK (fs_inum_bv (Z.of_nat (16 * bi + j)%nat))
                             (FsImg.sb_inodestart sb))
                   = diblk_bytes ds).
    { rewrite /IBLOCK Hbv Hz.
      assert (Hd : (16 * Z.of_nat bi + Z.of_nat j) `div` 16 = Z.of_nat bi).
      { rewrite (Z.mul_comm 16 (Z.of_nat bi)) Z.div_add_l; [| lia].
        rewrite (Z.div_small (Z.of_nat j) 16); lia. }
      rewrite Hd. replace (Z.of_nat bi + FsImg.sb_inodestart sb)
        with (FsImg.sb_inodestart sb + Z.of_nat bi) by lia.
      exact Hde. }
    rewrite (rec_owned_sb Gam sb (Z.of_nat (16 * bi + j)%nat) _ Hrng).
    rewrite (fs_dinode_of_diblk P sb (Z.of_nat (16 * bi + j)%nat) ds
               Hdwf Hblk) Hslot Hz //.
  Qed.

  (* ...and the whole region, at the region's inum set *)
  Lemma img_recs_of_region Gam (P : Z -> list (bv 8)) (sb : fs_sb)
      (nib : nat) :
    fs_blocks_full P -> 16 * Z.of_nat nib <= 2 ^ 32 ->
    ([∗ list] bi ∈ seq 0 nib,
       blk_owned Gam (FsImg.sb_inodestart sb + Z.of_nat bi)
                     (P (FsImg.sb_inodestart sb + Z.of_nat bi)))
    ⊢ [∗ set] z ∈ region_inums nib, rec_owned Gam sb z (fs_dinode P sb z).
  Proof.
    intros Hfull Hnib.
    iIntros "H".
    iAssert ([∗ list] bi ∈ seq 0 nib, [∗ list] k ∈ seq 0 16,
               rec_owned Gam sb (Z.of_nat (16 * bi + k)%nat)
                         (fs_dinode P sb (Z.of_nat (16 * bi + k)%nat)))%I
      with "[H]" as "H".
    { iApply (big_sepL_mono with "H"). intros j bi Hbi.
      apply lookup_seq in Hbi as [-> Hlt].
      iApply (img_recs_of_block Gam P sb nib j Hfull Hlt Hnib). }
    rewrite (big_sepL_seq_chunks
               (fun j => rec_owned Gam sb (Z.of_nat j) (fs_dinode P sb (Z.of_nat j)))
               16 nib).
    iApply (region_of_seq
              (fun z => rec_owned Gam sb z (fs_dinode P sb z)) nib with "H").
  Qed.

End DurImgRec.

(* ===================================================================== *)
(*  6.  THE WHOLE INODE MAP'S FOOTPRINT                                   *)
(* ===================================================================== *)

Section DurImgInodes.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* the free arm's fact: outside the live set the record is typed 0,
     whether it is below [ninodes] (by [FsImg.fs_live_set_elem_of]) or in
     the [[ninodes, 16*nib)] tail ([FsImg.fs_region_free]).  Verbatim
     [FsCfgBoot.ipool_alloc_of_image]'s. *)
  Lemma img_free_ty (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) (z : Z) :
    fs_region_free P sb nib = true ->
    z ∈ region_inums nib -> z ∉ fs_live_set P sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) = 0.
  Proof.
    intros Hrf Hz Hna. apply region_inums_spec in Hz.
    destruct (Z_lt_ge_dec z (FsImg.sb_ninodes sb)) as [Hlt | Hge].
    - destruct (decide (bv_unsigned (di_type (fs_dinode P sb z)) = 0))
        as [H0 | H0]; [exact H0 |].
      exfalso. apply Hna, fs_live_set_elem_of. split; [lia | exact H0].
    - exact (fs_region_free_spec P sb nib z Hrf
               ltac:(lia) ltac:(lia) ltac:(lia)).
  Qed.

  (* THE INODE MAP'S PHI HALF.  The records come from the inode region's
     own blocks (section 5); the data blocks come one live inode at a time
     out of [FsBoot.big_sepS_carve]'s cut; a FREE inum owns neither, which
     is what the bare sweep buys. *)
  Lemma img_inodes_phi (g : gname) (Gd : fs_dur_names)
      (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z) (nib : nat) :
    fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
    fs_region_bare P sb nib = true -> fs_blocks_full P ->
    FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
    (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
    ([∗ set] z ∈ region_inums nib,
       rec_owned (fs_gamma_D g Gd) sb z (fs_dinode P sb z)) -∗
    ([∗ set] i ∈ fs_live_set P sb,
       [∗ set] b ∈ fs_inode_blocks_set P sb i,
         blk_owned (fs_gamma_D g Gd) b (P b)) -∗
    [∗ map] i ↦ n ∈ img_nodes P sb nib,
      inode_phi (fs_gamma_D g Gd) sb i n.
  Proof.
    intros Hwf Hrw Hbare Hfull Hnin Hcov.
    pose proof (fs_region_wf_free _ _ _ Hrw) as Hrf.
    pose proof (fs_region_wf_nlink _ _ _ Hrw) as Hrnl.
    assert (HAsub : fs_live_set P sb ⊆ region_inums nib).
    { apply elem_of_subseteq. intros z Hz.
      apply fs_live_set_elem_of in Hz as [Hran _].
      apply region_inums_spec. lia. }
    iIntros "Hrec Hblk".
    (* the LIVE arm, one named application per inum *)
    iAssert ([∗ set] z ∈ fs_live_set P sb,
               (([∗ map] k ↦ bs ∈ fn_blk (img_node P sb z),
                   blk_owned (fs_gamma_D g Gd) (fn_naddr (img_node P sb z) k) bs)
                ∗ ind_owned (fs_gamma_D g Gd) (img_node P sb z)))%I
      with "[Hblk]" as "HpA".
    { iApply (big_sepS_mono with "Hblk"). intros z Hz.
      apply fs_live_set_elem_of in Hz as [Hran Hty].
      iApply (img_inode_phi_res g Gd P sb cov nib z Hwf Hrnl Hfull Hnin
                Hcov Hran Hty). }
    (* the FREE arm: a bare node owns no block and has no indirect block *)
    iAssert ([∗ set] z ∈ region_inums nib ∖ fs_live_set P sb,
               (([∗ map] k ↦ bs ∈ fn_blk (img_node P sb z),
                   blk_owned (fs_gamma_D g Gd) (fn_naddr (img_node P sb z) k) bs)
                ∗ ind_owned (fs_gamma_D g Gd) (img_node P sb z)))%I
      as "HpF".
    { iApply big_sepS_intro. iModIntro. iIntros (z Hz).
      apply elem_of_difference in Hz as [Hz1 Hz2].
      pose proof (img_free_ty P sb nib z Hrf Hz1 Hz2) as Hty0.
      pose proof (img_node_bare P sb nib z Hbare Hrnl
                    (proj1 (region_inums_spec nib z) Hz1) Hty0) as Hb.
      pose proof Hb as (_ & _ & Hblk0 & _ & _).
      rewrite Hblk0 big_sepM_empty.
      rewrite (ind_owned_none (fs_gamma_D g Gd) (img_node P sb z)
                 (fn_bare_indb _ Hb)).
      by iSplit. }
    (* the two arms, back as one big-op over the region *)
    iDestruct (big_sepS_union with "[$HpA $HpF]") as "Hp";
      [set_solver |].
    rewrite -(union_difference_L (fs_live_set P sb) (region_inums nib) HAsub).
    (* ...beside the records, and that pair IS [inode_phi] *)
    iDestruct (big_sepS_sep_2 with "Hrec Hp") as "Hphi".
    rewrite (big_sepM_img_nodes
               (fun i n => inode_phi (fs_gamma_D g Gd) sb i n) P sb nib).
    iApply (big_sepS_mono with "Hphi"). intros z _.
    iIntros "H". iExact "H".
  Qed.

End DurImgInodes.

(* ===================================================================== *)
(*  7.  THE BITMAP BLOCK AND THE FREE POOL                                *)
(*                                                                        *)
(*  [FsCfgBoot.bitmap_res_of_image] at [Gamma] instead of at              *)
(*  [BitmapInv.bitmap_res]: same two pieces, same [used] set (the block's *)
(*  OWN bits, so the byte-level equation is [FsImg.bm_bytes_fs_bmap_set]  *)
(*  and no image sweep is added), same disjointness argument.             *)
(* ===================================================================== *)

Section DurImgBitmap.
  Context {Σ : gFunctors}.

  Lemma img_free_bitmap (Gam : fs_view_names Σ) (P : Z -> list (bv 8))
      (sb : fs_sb) :
    fsimg_wf P sb = true -> fs_blocks_full P ->
    ([∗ set] b ∈ fs_bitmap_spent P sb, blk_owned Gam b (P b))
    ⊢ free_bitmap Gam sb
        (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb))).
  Proof.
    intros Hwf Hfull.
    pose proof (fsimg_wf_sb P sb Hwf) as Hsb.
    destruct (fsimg_wf_used P sb Hwf) as (u & _ & _ & Hbw).
    (* the bitmap block is below the data region, so it is not in the pool *)
    assert (Hdj : ({[ FsImg.sb_bmapstart sb ]} : gset Z)
                  ## free_set (FsImg.sb_size sb)
                       (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb)))).
    { apply disjoint_singleton_l. intros Hin.
      apply elem_of_free_set in Hin as [Hran Hnu].
      destruct (fs_bmap_set_free P sb u (FsImg.sb_bmapstart sb) Hsb Hbw
                  Hran Hnu) as [Hge _].
      unfold fs_data_start in Hge. lia. }
    assert (Hbytes : bm_bytes BSIZE
                       (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb)))
                     = P (FsImg.sb_bmapstart sb))
      by (apply bm_bytes_fs_bmap_set; apply Hfull).
    rewrite /fs_bitmap_spent (big_sepS_union _ _ _ Hdj) big_sepS_singleton.
    iIntros "[Hbm Hpool]".
    rewrite /free_bitmap /free_bitmap_at Hbytes.
    iSplitL "Hbm"; [iExact "Hbm" |].
    iApply free_pool_intro.
    iApply (big_sepS_mono with "Hpool"). intros b Hb.
    iIntros "Hf". by iExists (P b).
  Qed.

  (* THE RESTRICTED VIEW, AS A BIG-OP OVER ITS SET.  [LogDefs.fs_restrict]
     is [set_to_map], i.e. [list_to_map] over the set's elements, so this
     is [FsCfgBoot.big_sepM_img_nodes]' proof at a different map.  It
     belongs beside [fs_restrict]'s own theory in [LogDefs.v]. *)
  Lemma fs_restrict_keys (P : Z -> list (bv 8)) (S : gset Z) :
    ((fun b : Z => (b, P b)) <$> elements S).*1 = elements S.
  Proof.
    rewrite -list_fmap_compose.
    rewrite (list_fmap_ext _ id); [apply list_fmap_id | intros; reflexivity].
  Qed.

  Lemma big_sepM_fs_restrict (Phi : Z -> list (bv 8) -> iProp Σ)
      (P : Z -> list (bv 8)) (S : gset Z) :
    ([∗ map] b ↦ bs ∈ fs_restrict P S, Phi b bs)
    ⊣⊢ ([∗ set] b ∈ S, Phi b (P b)).
  Proof.
    rewrite /fs_restrict /set_to_map.
    assert (Hnd : base.NoDup (((fun b : Z => (b, P b)) <$> elements S).*1))
      by (rewrite fs_restrict_keys; apply NoDup_elements).
    rewrite (big_sepM_list_to_map Phi _ Hnd).
    rewrite big_sepL_fmap /=.
    rewrite big_sepS_elements //.
  Qed.

End DurImgBitmap.

(* ===================================================================== *)
(*  8.  THE IMAGE'S ABSTRACT STATE, AND THE BLOCKS IT OWNS                *)
(* ===================================================================== *)

(* the state [fs_view Gamma_D] binds at boot.  Every field is a FUNCTION of
   the image: the parsed superblock, block 1's raw bytes (there is no
   superblock encoder in the tree, so [FsState.fs_state_rec] carries the
   bytes), the region's decoded nodes, and the bitmap block's own bit set. *)
Definition img_state (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : fs_state_rec :=
  MkFsS sb (P SB_BNO) (img_nodes P sb nib)
        (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb))).

(* ...and the blocks its footprint covers: the superblock, the inode
   region, the bitmap block and the whole free pool, and every live
   inode's own blocks.  [FsCfgBoot.fs_kit_spent] MINUS the log region,
   which is outside the home set to begin with. *)
Definition img_owned (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : gset Z :=
  ({[ (1:Z) ]} ∪ ireg_blk_set (FsImg.sb_inodestart sb) nib
     ∪ fs_bitmap_spent P sb)
  ∪ fs_live_blocks P sb (fs_live_set P sb).

(* ===================================================================== *)
(*  9.  THE LINK FAMILY'S VALIDITY, PROVED FROM THE IMAGE CONJUNCTS      *)
(*                                                                        *)
(*  [FsState.fs_boot_alloc_at]'s premise [✓ link_elem I] is the           *)
(*  tokens-<=-nlink law of the initial map -- the fact                    *)
(*  [FsState.fs_links_valid] READS OFF a durable instance and which the   *)
(*  boot, having none, owes.  It is [img_link_valid] below, and it takes  *)
(*  FOUR image facts: W9 ([FsImg.fs_links_wf]), W6/W7, conjunct (13)      *)
(*  ([FsImg.fs_links_eq]) and conjunct (15)                               *)
(*  ([FsImg.fs_root_no_self]).  The first three are what [FsState.v]'s    *)
(*  header expected; (15) is what this lane found missing, and its        *)
(*  definition's header says why.                                        *)
(*                                                                        *)
(*  THE SHAPE OF THE PROOF, in three moves.                              *)
(*                                                                        *)
(*  (i)  W9 gives the STRUCTURAL half outright, and it is stronger than   *)
(*       expected: at every live inum which is a DIRECTORY W9 forces      *)
(*       [z = ROOTINO], so the image has EXACTLY ONE directory and every  *)
(*       other node's entry map is empty ([img_dir_entries_empty]).  The  *)
(*       family therefore splits into one authority per inum, times the   *)
(*       root's outgoing tokens ([link_elem_split] + [ent_ops_one]), and  *)
(*       since the all-at-home family [FsState.link_full_map] is valid    *)
(*       unconditionally, validity follows from ONE inclusion in          *)
(*       [fsLinkUR] ([link_elem_valid_of_root]).                          *)
(*                                                                        *)
(*  (ii) THE TOKEN-TO-TICKET BRIDGE ([img_link_incl]).  The root's        *)
(*       outgoing tokens are covered by the inodes' own [nlink]s.  The    *)
(*       two counting disciplines exempt different records --             *)
(*       [FsImg.fs_rec_ticket] exempts a record naming its OWN home under *)
(*       ANY name, [FsStateInode.ent_tokenless] only ["."] and an         *)
(*       orphaned-or-self [".."] -- and conjunct (15) is exactly the      *)
(*       difference: with it, every NON-tokenless entry of the root names *)
(*       something other than the root, hence is live-and-not-self, hence *)
(*       bears a ticket.                                                  *)
(*       The counting is done ONCE, by induction on the record count      *)
(*       ([view_ops_incl]): [DirView.dir_view]'s one-step recursion adds  *)
(*       at most one entry, at a name the prefix does not carry, so       *)
(*       [big_opM_insert] applies and the step is a single record's       *)
(*       comparison.  NO multiset argument and NO                         *)
(*       [FsTree.dir_names_unique] is needed -- a name is served by ONE   *)
(*       record because [DirView.dir_first] returns one, and W6's         *)
(*       uniqueness is what the CONVERSE (tickets <= tokens) would want.  *)
(*                                                                        *)
(*  (iii) THE ARITHMETIC ([toks_of_list_incl]).  A ticket list's element  *)
(*       in [fsLinkUR] has, at each key [z], the fragment                 *)
(*       [◯ (fs_tick_count L z)]; [link_toks_of I] is [◯ ∘ fn_nlink]      *)
(*       fmapped over [I].  So the inclusion is per-key [<=], which is    *)
(*       conjunct (13) at a live file inum and W9's directory arm at the  *)
(*       root -- with the root's own tickets bounded by the whole image's *)
(*       supply because [fs_all_tickets] JOINS the per-directory lists.   *)
(* ===================================================================== *)

(* ---- 9a.   THE FAMILY, SPLIT INTO AUTHORITIES AND TOKENS ------------ *)

(* one inode's outgoing tokens, as ONE resource-algebra element: the
   second half of [FsStateInode.link_elem_node] *)
Definition ent_ops (i : Z) (n : fs_node) : fsLinkUR :=
  [^op map] s ↦ t ∈ dir_entries n, ent_elem i (fn_orphan n) s t.

(* ...and the two halves of [FsState.link_full_map] *)
Definition link_auths (I : gmap Z fs_node) : fsLinkUR :=
  [^op map] i ↦ n ∈ I, link_auth_elem i (fn_nlink n).
Definition link_toks_of (I : gmap Z fs_node) : fsLinkUR :=
  [^op map] i ↦ n ∈ I, link_tok_elem i (fn_nlink n).

Lemma link_full_map_split (I : gmap Z fs_node) :
  link_full_map I ≡ link_auths I ⋅ link_toks_of I.
Proof.
  rewrite /link_full_map /link_auths /link_toks_of -big_opM_op //.
Qed.

Lemma link_elem_split (I : gmap Z fs_node) :
  link_elem I ≡ link_auths I ⋅ ([^op map] i ↦ n ∈ I, ent_ops i n).
Proof.
  rewrite /link_elem /link_auths /link_elem_node -big_opM_op //.
Qed.

Lemma ent_ops_empty (i : Z) (n : fs_node) :
  dir_entries n = ∅ -> ent_ops i n = ε.
Proof. rewrite /ent_ops. intros ->. rewrite big_opM_empty //. Qed.

(* AT MOST ONE NODE HAS ENTRIES, so the whole family's token half is that
   one node's *)
Lemma ent_ops_one (I : gmap Z fs_node) (d : Z) (nd : fs_node) :
  I !! d = Some nd ->
  (forall i n, I !! i = Some n -> i <> d -> dir_entries n = ∅) ->
  ([^op map] i ↦ n ∈ I, ent_ops i n) ≡ ent_ops d nd.
Proof.
  intros Hd Hrest.
  rewrite (big_opM_delete (fun i n => ent_ops i n) I d nd Hd).
  rewrite (big_opM_proper (fun i n => ent_ops i n)
             (fun (_ : Z) (_ : fs_node) => ε) (delete d I)); last first.
  { intros i n Hi. apply lookup_delete_Some in Hi as [Hne Hi].
    rewrite (ent_ops_empty i n (Hrest i n Hi ltac:(congruence))) //. }
  rewrite big_opM_unit right_id //.
Qed.

(* THE REDUCTION.  [FsState.link_full_map_valid] is unconditional, and
   validity is downward closed, so the whole obligation is one inclusion. *)
Lemma link_elem_valid_of_root (I : gmap Z fs_node) (d : Z) (nd : fs_node) :
  I !! d = Some nd ->
  (forall i n, I !! i = Some n -> i <> d -> dir_entries n = ∅) ->
  ent_ops d nd ≼ link_toks_of I ->
  ✓ link_elem I.
Proof.
  intros Hd Hrest [x Hx].
  apply (cmra_valid_included (link_elem I) (link_full_map I)
           (link_full_map_valid I)).
  rewrite link_full_map_split link_elem_split (ent_ops_one I d nd Hd Hrest).
  rewrite Hx. exists x. rewrite assoc //.
Qed.

(* ---- 9b.   A LIST OF TOKENS AS ONE RA ELEMENT ----------------------- *)

Definition toks_of_list (L : list Z) : fsLinkUR :=
  [^op list] t ∈ L, link_tok_elem t 1%nat.

Lemma toks_of_list_cons (t : Z) (L : list Z) :
  toks_of_list (t :: L) ≡ link_tok_elem t 1%nat ⋅ toks_of_list L.
Proof. rewrite /toks_of_list big_opL_cons //. Qed.

Lemma toks_of_list_app (L1 L2 : list Z) :
  toks_of_list (L1 ++ L2) ≡ toks_of_list L1 ⋅ toks_of_list L2.
Proof. rewrite /toks_of_list big_opL_app //. Qed.

Lemma toks_of_list_singleton (t : Z) :
  toks_of_list [t] ≡ link_tok_elem t 1%nat.
Proof. rewrite /toks_of_list big_opL_singleton //. Qed.

Lemma fs_tick_count_cons (t : Z) (L : list Z) (z : Z) :
  fs_tick_count (t :: L) z
  = (if bool_decide (t = z) then S (fs_tick_count L z)
     else fs_tick_count L z).
Proof. rewrite /fs_tick_count /=. by destruct (bool_decide (t = z)). Qed.

(* THE LOOKUP, in the two directions the inclusion needs: a key carries
   one fragment per naming, and nothing at all when nothing names it --
   [FsImg.fs_tick_count]'s reading in the RA. *)
Lemma toks_of_list_lookup_zero (L : list Z) (z : Z) :
  fs_tick_count L z = 0%nat -> toks_of_list L !! z = None.
Proof.
  induction L as [| t L IH]; intros H0.
  - reflexivity.
  - rewrite fs_tick_count_cons in H0.
    assert (Hne : t <> z).
    { intros ->. rewrite (bool_decide_eq_true_2 (z = z) eq_refl) in H0.
      discriminate. }
    rewrite (bool_decide_eq_false_2 (t = z) Hne) in H0.
    rewrite /toks_of_list big_opL_cons -/(toks_of_list L) lookup_op.
    rewrite /link_tok_elem lookup_singleton_ne; [| exact Hne].
    rewrite (IH H0). reflexivity.
Qed.

Lemma toks_of_list_lookup_pos (L : list Z) (z : Z) :
  (0 < fs_tick_count L z)%nat ->
  toks_of_list L !! z ≡ Some (◯ (fs_tick_count L z) : authR natUR).
Proof.
  induction L as [| t L IH]; intros Hp.
  - rewrite /fs_tick_count /= in Hp. lia.
  - rewrite /toks_of_list big_opL_cons -/(toks_of_list L) lookup_op.
    rewrite fs_tick_count_cons in Hp |- *.
    destruct (decide (t = z)) as [-> | Hne].
    + rewrite (bool_decide_eq_true_2 (z = z) eq_refl) in Hp |- *.
      rewrite /link_tok_elem lookup_singleton.
      destruct (decide (fs_tick_count L z = 0%nat)) as [H0 | H0].
      * rewrite (toks_of_list_lookup_zero L z H0) H0 right_id. reflexivity.
      * assert (Heq : (1%nat ⋅ fs_tick_count L z) = S (fs_tick_count L z))
          by (rewrite nat_op; lia).
        rewrite (IH ltac:(lia)) -Some_op -auth_frag_op Heq. reflexivity.
    + rewrite (bool_decide_eq_false_2 (t = z) Hne) in Hp |- *.
      rewrite /link_tok_elem lookup_singleton_ne; [| exact Hne].
      rewrite left_id. exact (IH Hp).
Qed.

(* ...and the boot family's token half, as an fmap ([link_full_map_fmap]'s
   twin at the fragment column) *)
Lemma link_toks_of_fmap (I : gmap Z fs_node) :
  link_toks_of I ≡ (fun n => (◯ (fn_nlink n) : authR natUR)) <$> I.
Proof.
  induction I as [| i n I Hi IH] using map_ind.
  - rewrite /link_toks_of big_opM_empty fmap_empty //.
  - rewrite /link_toks_of big_opM_insert //.
    rewrite -/(link_toks_of I) IH fmap_insert /link_tok_elem.
    rewrite insert_singleton_op; [done |]. rewrite lookup_fmap Hi //.
Qed.

(* THE INCLUSION, per key *)
Lemma toks_of_list_incl (L : list Z) (I : gmap Z fs_node) :
  (forall z : Z, (0 < fs_tick_count L z)%nat ->
     exists n : fs_node,
       I !! z = Some n /\ (fs_tick_count L z <= fn_nlink n)%nat) ->
  toks_of_list L ≼ link_toks_of I.
Proof.
  intros H. apply lookup_included. intros z.
  destruct (decide (fs_tick_count L z = 0%nat)) as [H0 | H0].
  - rewrite (toks_of_list_lookup_zero L z H0). apply option_included. by left.
  - destruct (H z ltac:(lia)) as (n & Hn & Hle).
    rewrite (toks_of_list_lookup_pos L z ltac:(lia)).
    rewrite (link_toks_of_fmap I) lookup_fmap Hn /=.
    apply Some_included_2. right. apply auth_frag_mono, nat_included. lia.
Qed.

(* ---- 9c.   THE COUNT OVER A JOINED TICKET SUPPLY --------------------- *)

Lemma fs_tick_count_app (L1 L2 : list Z) (z : Z) :
  fs_tick_count (L1 ++ L2) z
  = (fs_tick_count L1 z + fs_tick_count L2 z)%nat.
Proof. rewrite /fs_tick_count List.filter_app length_app //. Qed.

Lemma fs_tick_count_join (ls : list (list Z)) (l : list Z) (z : Z) :
  l ∈ ls -> (fs_tick_count l z <= fs_tick_count (mjoin ls) z)%nat.
Proof.
  induction ls as [| a ls IH]; intros Hl.
  - by apply elem_of_nil in Hl.
  - change (mjoin (a :: ls)) with (a ++ mjoin ls).
    rewrite fs_tick_count_app.
    apply elem_of_cons in Hl as [-> | Hl]; [lia |].
    pose proof (IH Hl). lia.
Qed.

Lemma fs_tick_count_elem (L : list Z) (z : Z) :
  (0 < fs_tick_count L z)%nat -> z ∈ L.
Proof.
  rewrite /fs_tick_count. intros H.
  destruct (List.filter (fun t => bool_decide (t = z)) L) as [| a l] eqn:E;
    [cbn in H; lia |].
  assert (Hin : List.In a (List.filter (fun t => bool_decide (t = z)) L))
    by (rewrite E; left; reflexivity).
  apply List.filter_In in Hin as [Hin Ha].
  apply bool_decide_eq_true in Ha. subst a.
  by apply elem_of_list_In.
Qed.

(* ---- 9d.   A DIRECTORY'S VIEW READ AT AGREEING BYTES ----------------- *)

(*  [FsStateInode.dir_entries] reads [FsStateInode.fn_data] of the node --
    the node's own block map, with a zero block at every hole -- while the
    image's sweeps read [FsImg.fs_data_of].  The two agree on every block a
    directory's records can reach ([img_node_file_byte]), and these three
    are the transport.  [DirView]'s [dir_win_agree] family does the
    per-record half; only the two SCANS need saying.                       *)

(* [DirView.dir_bname_agree] is stated at the UNFOLDED [bname 14 …]; the
   two scans below meet it folded as [FsTree.dir_bname]. *)
Lemma dir_bname_win_agree (data data' : nat -> list (bv 8)) (k : nat) :
  dir_win_agree data data' k -> dir_bname data' k = dir_bname data k.
Proof. intros H. unfold dir_bname. exact (dir_bname_agree data data' k H). Qed.

Lemma dir_first_agree (data data' : nat -> list (bv 8)) (n : nat)
    (s : fname) :
  (forall k : nat, (k < n)%nat -> dir_win_agree data data' k) ->
  dir_first data' n s = dir_first data n s.
Proof.
  intros H. unfold dir_first. apply dfirst_ext. intros j Hj.
  unfold dir_matchb.
  rewrite (dir_liveb_agree data data' j (H j Hj)).
  rewrite (dir_bname_agree data data' j (H j Hj)). reflexivity.
Qed.

Lemma dir_wins_agree (data data' : nat -> list (bv 8)) (n : nat) :
  (forall k : nat, (k <= n)%nat -> dir_win_agree data data' k) ->
  dir_wins data' n = dir_wins data n.
Proof.
  intros H. unfold dir_wins.
  rewrite (dir_liveb_agree data data' n ltac:(apply H; lia)).
  rewrite (dir_bname_win_agree data data' n ltac:(apply H; lia)).
  rewrite (dir_first_agree data data' n (dir_bname data n)
             ltac:(intros k Hk; apply H; lia)).
  reflexivity.
Qed.

Lemma dir_view_agree (data data' : nat -> list (bv 8)) (n : nat) :
  (forall k : nat, (k < n)%nat -> dir_win_agree data data' k) ->
  dir_view data' n = dir_view data n.
Proof.
  induction n as [| n IH]; intros H; [reflexivity |].
  rewrite !dir_view_S.
  rewrite (IH ltac:(intros k Hk; apply H; lia)).
  rewrite (dir_wins_agree data data' n ltac:(intros k Hk; apply H; lia)).
  destruct (dir_wins data n); [| reflexivity].
  rewrite (dir_bname_win_agree data data' n ltac:(apply H; lia)).
  rewrite (dir_inum_agree data data' n ltac:(apply H; lia)).
  reflexivity.
Qed.

(* ...and the agreement itself, at the image's node *)
Lemma img_blkmap_holes (P : Z -> list (bv 8)) (dn : dinode) :
  dinode_wf dn -> blk_holes_zero (img_blkmap P dn) (fs_data_of P dn).
Proof.
  intros Hwf i Hi H0. apply fs_data_of_holes.
  rewrite <- (img_blkmap_get P dn i Hwf Hi). exact H0.
Qed.

Lemma img_node_data (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) (k : nat) :
  (k < MAXFILE)%nat ->
  fn_data (img_node P sb z) k = fs_data_of P (fs_dinode P sb z) k.
Proof.
  intros Hk.
  exact (era_node_data (fs_dinode P sb z) (img_blkmap P (fs_dinode P sb z))
           (fs_data_of P (fs_dinode P sb z)) k
           (img_blkmap_holes P (fs_dinode P sb z) (fs_dinode_wf P sb z)) Hk).
Qed.

Lemma img_node_file_byte (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z)
    (x : nat) :
  (x < MAXFILE * BSIZE)%nat ->
  file_byte (fn_data (img_node P sb z)) x
  = file_byte (fs_data_of P (fs_dinode P sb z)) x.
Proof.
  intros Hx. unfold file_byte. rewrite img_node_data; [reflexivity |].
  apply Nat.div_lt_upper_bound; [unfold BSIZE; lia | lia].
Qed.

(* THE ROOT'S ENTRY MAP, at the image's own byte reading *)
Lemma img_root_entries (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true ->
  dir_entries (img_node P sb FsImg.ROOTINO)
  = dir_view (fs_data_of P (fs_dinode P sb FsImg.ROOTINO))
      (dir_nrec (bv_unsigned (di_size (fs_dinode P sb FsImg.ROOTINO)))).
Proof.
  intros Hwf.
  assert (Hty : bv_unsigned (di_type (fs_dinode P sb FsImg.ROOTINO))
                = T_DIR_z)
    by exact (fs_root_wf_type P sb (fsimg_wf_root P sb Hwf)).
  assert (Hnin : 0 <= FsImg.ROOTINO < FsImg.sb_ninodes sb).
  { pose proof (sbo_ninodes sb (fsimg_wf_sb P sb Hwf)).
    unfold FsImg.ROOTINO in *. lia. }
  assert (Hok : fs_inode_ok P sb (fs_dinode P sb FsImg.ROOTINO)).
  { apply (fsimg_wf_inode P sb FsImg.ROOTINO Hwf Hnin).
    rewrite Hty. unfold T_DIR_z. lia. }
  pose proof (fio_size P sb (fs_dinode P sb FsImg.ROOTINO) Hok) as Hsz.
  pose proof (proj1 (bv_unsigned_in_range _
                       (di_size (fs_dinode P sb FsImg.ROOTINO)))) as Hsz0.
  rewrite /dir_entries.
  assert (Hdir : fn_is_dir (img_node P sb FsImg.ROOTINO) = true)
    by (apply bool_decide_eq_true; exact Hty).
  rewrite Hdir.
  change (fn_nrec (img_node P sb FsImg.ROOTINO))
    with (dir_nrec (bv_unsigned (di_size (fs_dinode P sb FsImg.ROOTINO)))).
  apply dir_view_agree. intros k Hk j Hj.
  apply img_node_file_byte.
  (* the records live below [MAXFILE] blocks, by W3's size cap *)
  assert (H16 : 16 * (bv_unsigned (di_size (fs_dinode P sb FsImg.ROOTINO))
                      / 16)
                <= bv_unsigned (di_size (fs_dinode P sb FsImg.ROOTINO)))
    by (apply Z.mul_div_le; lia).
  unfold dir_nrec in Hk.
  unfold MAXFILE, BSIZE. unfold FS_MAXFILE, BSIZE_z in Hsz. lia.
Qed.

(* ---- 9e.   THE INDUCTION: EVERY NON-TOKENLESS ENTRY BEARS A TICKET ---- *)

(*  Generic in the ticket function, so nothing here knows about an image:
    the RA's [FsStateInode.ent_elem] and a ticket are compared record by
    record.  The premise is the WHOLE content of the bridge -- a record
    that WINS its name and owes a token has a ticket naming the same inum
    -- and the induction is [DirView.dir_view]'s own one-step recursion,
    which adds at most one entry at a name the prefix does not carry, so
    [big_opM_insert] applies and no multiset argument is needed.           *)
Lemma view_ops_incl (data : nat -> list (bv 8)) (self : Z) (orph : bool)
    (tick : nat -> option Z) (n : nat) :
  (forall k : nat, (k < n)%nat -> dir_wins data k = true ->
     ent_tokenless self orph (dir_bname data k)
       (bv_unsigned (dir_inum data k)) = false ->
     tick k = Some (bv_unsigned (dir_inum data k))) ->
  ([^op map] s ↦ t ∈ dir_view data n, ent_elem self orph s t)
    ≼ toks_of_list (omap tick (seq 0 n)).
Proof.
  induction n as [| n IH].
  - intros _. rewrite dir_view_nil big_opM_empty. apply ucmra_unit_least.
  - intros Hself.
    assert (IHn : ([^op map] s ↦ t ∈ dir_view data n, ent_elem self orph s t)
                    ≼ toks_of_list (omap tick (seq 0 n)))
      by (apply IH; intros k Hk; apply Hself; lia).
    rewrite seq_S. replace (0 + n)%nat with n by lia.
    rewrite omap_app toks_of_list_app dir_view_S.
    destruct (dir_wins data n) eqn:Hw; last first.
    { rewrite right_id_L.
      apply (cmra_included_trans _ (toks_of_list (omap tick (seq 0 n))));
        [exact IHn |].
      exists (toks_of_list (omap tick [n])). reflexivity. }
    (* the record enters the view, at a name the prefix does not carry *)
    assert (Hfresh : dir_view data n !! dir_bname data n = None).
    { apply dir_view_lookup_None.
      exact (proj2 (proj1 (dir_wins_true data n) Hw)). }
    rewrite insert_empty -insert_union_singleton_r; [| exact Hfresh].
    rewrite (big_opM_insert (fun s t => ent_elem self orph s t)
               (dir_view data n) (dir_bname data n)
               (bv_unsigned (dir_inum data n)) Hfresh).
    rewrite (cmra_comm (ent_elem self orph (dir_bname data n)
                          (bv_unsigned (dir_inum data n)))).
    apply cmra_mono; [exact IHn |].
    (* the one record's comparison *)
    destruct (ent_tokenless self orph (dir_bname data n)
                (bv_unsigned (dir_inum data n))) eqn:Htl.
    { rewrite /ent_elem Htl. apply ucmra_unit_least. }
    pose proof (Hself n ltac:(lia) Hw Htl) as Ht.
    assert (Homap : omap tick [n] = [bv_unsigned (dir_inum data n)])
      by (cbn; rewrite Ht; reflexivity).
    rewrite Homap toks_of_list_singleton /ent_elem Htl.
    exists ε. by rewrite right_id.
Qed.

(*  ...at the image's ticket function.  THIS IS WHERE CONJUNCT (15) IS
    SPENT: without it a root record called "foo" naming the root would owe
    a token ([ent_tokenless]'s self clause exempts it) and pay no
    ticket ([fs_rec_ticket] exempts any SELF record).                      *)
Lemma view_ops_incl_tickets (P : Z -> list (bv 8)) (self : Z) (dn : dinode)
    (orph : bool) :
  (forall k : nat,
     (k < dir_nrec (bv_unsigned (di_size dn)))%nat ->
     dir_live (fs_data_of P dn) k ->
     bv_unsigned (dir_inum (fs_data_of P dn) k) = self ->
     dir_bname (fs_data_of P dn) k = DOT
     \/ dir_bname (fs_data_of P dn) k = DOTDOT) ->
  ([^op map] s ↦ t ∈ dir_view (fs_data_of P dn)
                       (dir_nrec (bv_unsigned (di_size dn))),
     ent_elem self orph s t)
    ≼ toks_of_list (fs_dir_tickets P self dn).
Proof.
  intros Hself. rewrite /fs_dir_tickets.
  apply view_ops_incl. intros k Hk Hw Htl.
  assert (Hlv : dir_live (fs_data_of P dn) k)
    by exact (dir_wins_live (fs_data_of P dn) k Hw).
  assert (Hne : bv_unsigned (dir_inum (fs_data_of P dn) k) <> self).
  { (* under 2b-inode-5's [ent_tokenless] the SELF clause refutes directly:
       a live entry targeting its home owes no token, whatever its name.
       [Hself] ((15), [fs_root_no_self]) is no longer needed here and stays
       only to keep the statement (and its callers) unchanged. *)
    clear Hself. intros Hc.
    rewrite /ent_tokenless Hc in Htl.
    rewrite (bool_decide_eq_true_2 (self = self) eq_refl) in Htl.
    cbn [orb] in Htl. discriminate. }
  rewrite /fs_rec_ticket. cbv zeta.
  rewrite (proj2 (dir_liveb_true (fs_data_of P dn) k) Hlv).
  rewrite (bool_decide_eq_false_2 _ Hne). reflexivity.
Qed.

(* ---- 9f.   THE IMAGE'S OWN INSTANCE ---------------------------------- *)

Lemma img_nodes_lookup_inv (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) (n : fs_node) :
  img_nodes P sb nib !! z = Some n ->
  z ∈ region_inums nib /\ n = img_node P sb z.
Proof.
  intros Hz. rewrite /img_nodes in Hz.
  apply elem_of_list_to_map_2 in Hz.
  apply elem_of_list_fmap in Hz as (y & Heq & Hy).
  injection Heq as -> ->. split; [| reflexivity].
  by apply elem_of_elements.
Qed.

(* W9's STRUCTURAL HALF: the image has exactly one directory, the root. *)
Lemma img_dir_entries_empty (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
  z ∈ region_inums nib -> z <> FsImg.ROOTINO ->
  dir_entries (img_node P sb z) = ∅.
Proof.
  intros Hwf Hrw Hz Hne. apply region_inums_spec in Hz.
  rewrite /dir_entries.
  destruct (fn_is_dir (img_node P sb z)) eqn:Hd; [| reflexivity].
  exfalso.
  assert (Hty : bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z)
    by exact (proj1 (bool_decide_eq_true _) Hd).
  assert (Hran : 0 <= z < FsImg.sb_ninodes sb).
  { split; [lia |].
    destruct (Z_lt_ge_dec z (FsImg.sb_ninodes sb)) as [Hlt | Hge];
      [exact Hlt |].
    exfalso.
    rewrite (fs_region_free_spec P sb nib z (fs_region_wf_free _ _ _ Hrw)
               ltac:(lia) ltac:(lia) ltac:(lia)) in Hty.
    rewrite /T_DIR_z in Hty. discriminate. }
  destruct (proj2 (fs_links_wf_at P sb z (fsimg_wf_links P sb Hwf) Hran) Hty)
    as (_ & _ & Hroot).
  exact (Hne Hroot).
Qed.

(* ---- 9g.   THE BRIDGE ------------------------------------------------ *)

Lemma img_link_incl (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  fsimg_wf P sb = true -> fs_links_eq P sb = true ->
  fs_root_no_self P sb = true ->
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  ent_ops FsImg.ROOTINO (img_node P sb FsImg.ROOTINO)
    ≼ link_toks_of (img_nodes P sb nib).
Proof.
  intros Hwf Heq Hns Hnib.
  assert (Hty : bv_unsigned (di_type (fs_dinode P sb FsImg.ROOTINO))
                = T_DIR_z)
    by exact (fs_root_wf_type P sb (fsimg_wf_root P sb Hwf)).
  assert (Hnin : 0 <= FsImg.ROOTINO < FsImg.sb_ninodes sb).
  { pose proof (sbo_ninodes sb (fsimg_wf_sb P sb Hwf)).
    unfold FsImg.ROOTINO in *. lia. }
  pose proof (fsimg_wf_dir P sb FsImg.ROOTINO Hwf Hnin Hty) as Hdok.
  apply (cmra_included_trans _
           (toks_of_list (fs_dir_tickets P FsImg.ROOTINO
                            (fs_dinode P sb FsImg.ROOTINO)))).
  (* STEP ONE: the root's tokens are covered by the root's tickets *)
  { rewrite /ent_ops (img_root_entries P sb Hwf).
    apply view_ops_incl_tickets. intros k Hk Hlv Hc.
    exact (fs_root_no_self_at P sb k Hns Hk Hlv Hc). }
  (* STEP TWO: the root's tickets are covered by the inodes' nlinks *)
  apply toks_of_list_incl. intros z Hz.
  pose proof (fs_tick_count_elem _ z Hz) as Hin.
  rewrite /fs_dir_tickets in Hin.
  apply elem_of_list_omap in Hin as (k & Hk & Hkt).
  apply elem_of_seq in Hk as [_ Hk].
  rewrite /fs_rec_ticket in Hkt. cbv zeta in Hkt.
  destruct (dir_liveb (fs_data_of P (fs_dinode P sb FsImg.ROOTINO)) k
            && negb (bool_decide
                       (bv_unsigned
                          (dir_inum
                             (fs_data_of P (fs_dinode P sb FsImg.ROOTINO)) k)
                        = FsImg.ROOTINO))) eqn:Hg; [| discriminate].
  injection Hkt as <-.
  apply andb_true_iff in Hg as [Hlv Hself].
  apply negb_true_iff, bool_decide_eq_false in Hself.
  destruct (fdo_ent P sb FsImg.ROOTINO (fs_dinode P sb FsImg.ROOTINO) Hdok
              k Hk (proj1 (dir_liveb_true _ k) Hlv)) as [Hran Hlive].
  set (t := bv_unsigned
              (dir_inum (fs_data_of P (fs_dinode P sb FsImg.ROOTINO)) k))
    in *.
  assert (Htran : 0 <= t < FsImg.sb_ninodes sb) by lia.
  exists (img_node P sb t). split.
  { apply img_nodes_lookup. apply region_inums_spec. lia. }
  (* not a directory (W9's arm), so conjunct (13) gives its exact count *)
  assert (Hnd : bv_unsigned (di_type (fs_dinode P sb t)) <> T_DIR_z).
  { intros Hc.
    destruct (proj2 (fs_links_wf_at P sb t (fsimg_wf_links P sb Hwf) Htran)
                Hc) as (_ & _ & Hr).
    exact (Hself Hr). }
  pose proof (fs_links_eq_at P sb t Heq Htran Hlive Hnd) as Hnl.
  (* the root's own tickets are part of the image's whole supply *)
  assert (Hjoin :
    (fs_tick_count (fs_dir_tickets P FsImg.ROOTINO
                      (fs_dinode P sb FsImg.ROOTINO)) t
     <= fs_link_count P sb t)%nat).
  { rewrite /fs_link_count /fs_all_tickets.
    apply fs_tick_count_join. apply elem_of_list_fmap.
    exists (Z.to_nat FsImg.ROOTINO). split.
    - rewrite Z2Nat.id; [| unfold FsImg.ROOTINO; lia].
      rewrite /fs_dir_tickets_at. cbv zeta.
      rewrite (proj2 (Z.eqb_eq _ _) Hty) //.
    - apply elem_of_seq. unfold FsImg.ROOTINO in *. lia. }
  rewrite /fn_nlink img_node_rec Hnl Nat2Z.id. exact Hjoin.
Qed.

(* ---- 9h.   THE FAMILY'S VALIDITY, AS A THEOREM ----------------------- *)

Lemma img_link_valid (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
  fs_links_eq P sb = true -> fs_root_no_self P sb = true ->
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  ✓ link_elem (img_nodes P sb nib).
Proof.
  intros Hwf Hrw Heq Hns Hnin.
  pose proof (sbo_ninodes sb (fsimg_wf_sb P sb Hwf)) as Hni.
  unfold FsImg.ROOTINO in Hni.
  assert (Hrootin : FsImg.ROOTINO ∈ region_inums nib)
    by (apply region_inums_spec; rewrite /FsImg.ROOTINO; lia).
  apply (link_elem_valid_of_root _ FsImg.ROOTINO
           (img_node P sb FsImg.ROOTINO)
           (img_nodes_lookup P sb nib FsImg.ROOTINO Hrootin));
    [| exact (img_link_incl P sb nib Hwf Heq Hns Hnin)].
  intros i n Hi Hne.
  destruct (img_nodes_lookup_inv P sb nib i n Hi) as [Hin ->].
  exact (img_dir_entries_empty P sb nib i Hwf Hrw Hin Hne).
Qed.

(* ===================================================================== *)
(* 10.  THE DURABLE INSTANCE, FROM THE IMAGE                              *)
(* ===================================================================== *)

Section DurImgMain.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Lemma fs_dur_of_image (g : gname) (dk : Z -> bv 8) (ndisk : nat)
      (sb : fs_sb) (nib : nat) (cov : gset Z) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    (* the two image sweeps this file's header (2)/(3) name *)
    fs_region_bare (fs_blocks dk) sb nib = true ->
    fs_root_no_self (fs_blocks dk) sb = true ->
    fs_dbelems g (fs_dbytes (fs_restrict (fs_blocks dk)
                              (fs_home_set cov (FsImg.sb_logstart sb))))
    ⊢ |==> ∃ Gd : fs_dur_names,
        ghost_map_auth (fdn_top Gd) 1 (img_nodes (fs_blocks dk) sb nib)
        (* THE AUTHORITY'S OWN ELEMENTS, AND THEY ARE NOT OPTIONAL
           (durable-disk 2c-body's finding (G)).  A [ghost_map] value
           cannot be retagged without its element, so an authority handed
           out alone makes the durable abstract state IMMUTABLE and every
           commit that moves an inode unprovable.  [FsState]'s own
           [inode_owned] does not carry [top_frag] -- only the ERA bundle
           [FsStateEra.inode_owned_era] does -- so the durable instance
           carries the fragments here, one per inode, exactly as
           [fs-state.md] section 4 says a holder of [inode_owned] does. *)
        ∗ ([∗ map] i ↦ n ∈ img_nodes (fs_blocks dk) sb nib,
             top_frag (fs_gamma_D g Gd) i n)
        ∗ fs_state (fs_gamma_D g Gd) (img_state (fs_blocks dk) sb nib)
        ∗ ([∗ set] b ∈ fs_home_set cov (FsImg.sb_logstart sb)
                       ∖ img_owned (fs_blocks dk) sb nib,
             blk_owned (fs_gamma_D g Gd) b (fs_blocks dk b)).
  Proof.
    intros (Hwf & Hrw & Hnin & Hnib32 & Hnibpos & Hnibq & Hcovin & Hcovmeta
            & Hcovdata & Hparse & Hnib16 & Hndisk & Hlinkeq) Hbare Hns.
    (* the link family's own law, PROVED (section 9h) *)
    pose proof (img_link_valid (fs_blocks dk) sb nib Hwf Hrw Hlinkeq Hns Hnin)
      as Hlink.
    (* ---- the pure geometry, off [fs_sb_ok] alone -------------------- *)
    pose proof (fsimg_wf_sb _ _ Hwf) as Hsb.
    pose proof (sbo_logstart sb Hsb) as Hls.
    pose proof (sbo_nlog sb Hsb) as Hnl.
    pose proof (sbo_inodestart sb Hsb) as Hist.
    pose proof (sbo_bmapstart sb Hsb) as Hbms.
    pose proof (sbo_ninodes sb Hsb) as Hni. unfold FsImg.ROOTINO in Hni.
    assert (Hfull : fs_blocks_full (fs_blocks dk))
      by (intros b; apply fs_blocks_length).
    assert (Hds : fs_data_start sb
                  = FsImg.sb_inodestart sb + Z.of_nat nib + 1)
      by (rewrite /fs_data_start; lia).
    assert (HlogI : forall b : Z,
              b ∈ log_region_set (FsImg.sb_logstart sb) ->
              1 < b < FsImg.sb_inodestart sb).
    { intros b Hb.
      pose proof (log_region_bound (FsImg.sb_logstart sb) b Hb).
      unfold LOGBLOCKS in *. lia. }
    assert (HiregI : forall b : Z,
              b ∈ ireg_blk_set (FsImg.sb_inodestart sb) nib ->
              FsImg.sb_inodestart sb <= b < fs_data_start sb).
    { intros b Hb. apply ireg_blk_set_spec in Hb. lia. }
    (* ---- the three peels, each a subset of what is left ------------- *)
    assert (H1home : ({[ (1:Z) ]} : gset Z)
                     ⊆ fs_home_set cov (FsImg.sb_logstart sb)).
    { rewrite /fs_home_set. apply elem_of_subseteq. intros b Hb.
      apply elem_of_singleton in Hb as ->. apply elem_of_difference.
      split; [apply Hcovmeta; lia |].
      intros Hc. pose proof (HlogI 1 Hc). lia. }
    assert (Hiregsub : ireg_blk_set (FsImg.sb_inodestart sb) nib
                       ⊆ fs_home_set cov (FsImg.sb_logstart sb)
                         ∖ ({[ (1:Z) ]} : gset Z)).
    { apply elem_of_subseteq. intros b Hb. pose proof (HiregI b Hb).
      rewrite /fs_home_set. apply elem_of_difference. split.
      - apply elem_of_difference. split; [apply Hcovmeta; lia |].
        intros Hc. pose proof (HlogI b Hc). lia.
      - rewrite elem_of_singleton. lia. }
    assert (HcovC : forall b : Z, fs_data_start sb <= b < FsImg.sb_size sb ->
              b ∈ (fs_home_set cov (FsImg.sb_logstart sb)
                     ∖ ({[ (1:Z) ]} : gset Z))
                    ∖ ireg_blk_set (FsImg.sb_inodestart sb) nib).
    { intros b Hb. apply elem_of_difference. split.
      - rewrite /fs_home_set. apply elem_of_difference. split.
        + apply elem_of_difference. split; [apply Hcovdata; exact Hb |].
          intros Hc. pose proof (HlogI b Hc). lia.
        + rewrite elem_of_singleton. lia.
      - intros Hc. pose proof (HiregI b Hc). lia. }
    (* ---- the carve's own two premises ------------------------------- *)
    destruct (fsimg_wf_used (fs_blocks dk) sb Hwf) as (u & Hus & Hnd & _).
    assert (HAl : forall z : Z, z ∈ fs_live_set (fs_blocks dk) sb ->
              0 <= z < FsImg.sb_ninodes sb
              /\ bv_unsigned (di_type (fs_dinode (fs_blocks dk) sb z)) <> 0)
      by (intros z Hz; exact (proj1 (fs_live_set_elem_of _ _ z) Hz)).
    assert (Hsub : forall i : Z, i ∈ elements (fs_live_set (fs_blocks dk) sb) ->
              fs_inode_blocks_set (fs_blocks dk) sb i
              ⊆ (fs_home_set cov (FsImg.sb_logstart sb)
                   ∖ ({[ (1:Z) ]} : gset Z))
                  ∖ ireg_blk_set (FsImg.sb_inodestart sb) nib).
    { intros i Hi. apply elem_of_elements in Hi.
      destruct (HAl i Hi) as [Hran Hty].
      apply (fs_inode_blocks_set_sub (fs_blocks dk) sb i _
               (fsimg_wf_inode _ sb i Hwf Hran Hty) HcovC). }
    assert (Hdisj : forall i j : Z,
              i ∈ elements (fs_live_set (fs_blocks dk) sb) ->
              j ∈ elements (fs_live_set (fs_blocks dk) sb) -> i <> j ->
              fs_inode_blocks_set (fs_blocks dk) sb i
              ## fs_inode_blocks_set (fs_blocks dk) sb j).
    { intros i j Hi Hj Hne.
      apply elem_of_elements in Hi. apply elem_of_elements in Hj.
      destruct (HAl i Hi) as [Hrani Htyi].
      destruct (HAl j Hj) as [Hranj Htyj].
      exact (fs_inode_blocks_disjoint (fs_blocks dk) sb i j Hnd Hrani Hranj
               Hne Htyi Htyj). }
    (* ---- the bitmap's own subset (verbatim [fs_cfg_alloc]'s) -------- *)
    assert (Hbmeq : FsImg.sb_bmapstart sb
                    = FsImg.sb_inodestart sb + Z.of_nat nib)
      by (unfold fs_data_start in Hds; lia).
    assert (Hbmsub : fs_bitmap_spent (fs_blocks dk) sb
                     ⊆ ((fs_home_set cov (FsImg.sb_logstart sb)
                           ∖ ({[ (1:Z) ]} : gset Z))
                          ∖ ireg_blk_set (FsImg.sb_inodestart sb) nib)
                         ∖ fs_live_blocks (fs_blocks dk) sb
                             (fs_live_set (fs_blocks dk) sb)).
    { apply elem_of_subseteq. intros b Hb.
      assert (Hlive : b ∈ fs_live_blocks (fs_blocks dk) sb
                            (fs_live_set (fs_blocks dk) sb) -> b ∈ u)
        by (apply (fs_live_blocks_used (fs_blocks dk) sb _ u b Hus HAl)).
      destruct (fs_bitmap_spent_bound (fs_blocks dk) sb u b Hwf Hus Hb)
        as [-> | [Hran Hnu]].
      - apply elem_of_difference. split.
        + apply elem_of_difference. split.
          * rewrite /fs_home_set. apply elem_of_difference. split.
            { apply elem_of_difference. split.
              - apply Hcovmeta. unfold fs_data_start. lia.
              - intros Hc. pose proof (HlogI _ Hc). lia. }
            rewrite elem_of_singleton. lia.
          * intros Hc. apply ireg_blk_set_spec in Hc. lia.
        + intros Hc.
          destruct (fs_live_blocks_range (fs_blocks dk) sb _ _ Hwf HAl Hc)
            as [Hge _]. unfold fs_data_start in Hge. lia.
      - apply elem_of_difference. split.
        + apply elem_of_difference. split.
          * rewrite /fs_home_set. apply elem_of_difference. split.
            { apply elem_of_difference. split.
              - apply Hcovdata. lia.
              - intros Hc. pose proof (HlogI b Hc). lia. }
            rewrite elem_of_singleton. lia.
          * intros Hc. pose proof (HiregI b Hc). lia.
        + intros Hc. exact (Hnu (Hlive Hc)). }
    (* ---- the residual, as one set ----------------------------------- *)
    assert (Hset : ((((fs_home_set cov (FsImg.sb_logstart sb)
                         ∖ ({[ (1:Z) ]} : gset Z))
                        ∖ ireg_blk_set (FsImg.sb_inodestart sb) nib)
                       ∖ fs_live_blocks (fs_blocks dk) sb
                           (fs_live_set (fs_blocks dk) sb))
                      ∖ fs_bitmap_spent (fs_blocks dk) sb)
                   = fs_home_set cov (FsImg.sb_logstart sb)
                       ∖ img_owned (fs_blocks dk) sb nib).
    { apply set_eq. intros b. rewrite /img_owned.
      rewrite 5!elem_of_difference 3!elem_of_union. tauto. }
    (* ================================================================ *)
    iIntros "Hd".
    (* the two durable gnames -- the CLIENT allocates them (2c-names) *)
    iMod (fs_boot_alloc_at (img_nodes (fs_blocks dk) sb nib)
            (img_nodes (fs_blocks dk) sb nib) Hlink)
      as (gl gt) "(Htopa & Htfr & Hlnk)".
    iModIntro. iExists (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib)).
    iSplitL "Htopa"; [iExact "Htopa" |].
    iSplitL "Htfr"; [iExact "Htfr" |].
    (* the flat elements, as one exclusive run per home block *)
    assert (Hlen : forall b bs,
              fs_restrict (fs_blocks dk)
                (fs_home_set cov (FsImg.sb_logstart sb)) !! b = Some bs ->
              length bs = BSIZE).
    { intros b bs Hb. apply fs_restrict_lookup_Some in Hb as [_ ->].
      apply fs_blocks_length. }
    rewrite (fs_dbelems_dbytes g (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib)) _ Hlen).
    rewrite (big_sepM_fs_restrict
               (fun b bs => blk_owned (fs_gamma_D g (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib))) b bs)
               (fs_blocks dk) (fs_home_set cov (FsImg.sb_logstart sb))).
    (* ---- peel block 1 ---------------------------------------------- *)
    iDestruct (big_sepS_split_sub _ _ ({[ (1:Z) ]} : gset Z) H1home
                 with "Hd") as "[Hb1 Hd]".
    rewrite big_sepS_singleton.
    (* ---- peel the inode region, and decode its records -------------- *)
    iDestruct (big_sepS_split_sub _ _
                 (ireg_blk_set (FsImg.sb_inodestart sb) nib) Hiregsub
                 with "Hd") as "[Hbireg Hd]".
    iDestruct (ireg_blk_of_set
                 (fun b => blk_owned (fs_gamma_D g (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib))) b
                             (fs_blocks dk b))
                 (FsImg.sb_inodestart sb) nib with "Hbireg") as "Hbireg".
    iDestruct (img_recs_of_region (fs_gamma_D g (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib)))
                 (fs_blocks dk) sb nib Hfull Hnib32 with "Hbireg") as "Hrec".
    (* ---- carve the live inodes' blocks ------------------------------ *)
    iDestruct (big_sepS_carve
                 (fun b => blk_owned (fs_gamma_D g (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib))) b
                             (fs_blocks dk b))%I
                 _ (elements (fs_live_set (fs_blocks dk) sb))
                 (fs_inode_blocks_set (fs_blocks dk) sb)
                 (NoDup_elements _) Hsub Hdisj with "Hd") as "[Hpc Hd]".
    iDestruct (big_sepS_of_elements
                 (fun i => [∗ set] b ∈ fs_inode_blocks_set (fs_blocks dk) sb i,
                             blk_owned (fs_gamma_D g (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib))) b
                               (fs_blocks dk b))%I
                 (fs_live_set (fs_blocks dk) sb) with "Hpc") as "Hpc".
    (* the carve's remainder, at the folded spelling of the live set *)
    iAssert ([∗ set] b ∈ ((fs_home_set cov (FsImg.sb_logstart sb)
                             ∖ ({[ (1:Z) ]} : gset Z))
                            ∖ ireg_blk_set (FsImg.sb_inodestart sb) nib)
                           ∖ fs_live_blocks (fs_blocks dk) sb
                               (fs_live_set (fs_blocks dk) sb),
               blk_owned (fs_gamma_D g (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib))) b
                 (fs_blocks dk b))%I with "[Hd]" as "Hd";
      [iExact "Hd" |].
    (* ---- peel the bitmap block and the free pool -------------------- *)
    iDestruct (big_sepS_split_sub _ _ (fs_bitmap_spent (fs_blocks dk) sb)
                 Hbmsub with "Hd") as "[Hbm Hd]".
    iDestruct (img_free_bitmap (fs_gamma_D g (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib)))
                 (fs_blocks dk) sb Hwf Hfull with "Hbm") as "Hbm".
    iEval (rewrite Hset) in "Hd".
    iSplitR "Hd"; [| iExact "Hd"].
    (* ================================================================ *)
    (* ---- the inode map's phi half ---------------------------------- *)
    iDestruct (img_inodes_phi g (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib)) (fs_blocks dk) sb cov nib
                 Hwf Hrw Hbare Hfull Hnin Hcovdata with "Hrec Hpc") as "Hphi".
    (* ---- assemble ---------------------------------------------------- *)
    iApply (fs_state_of (fs_gamma_D g (MkFsDurNames gl gt (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb) (16 * Z.of_nat nib)))
              (img_state (fs_blocks dk) sb nib) with "[Hb1 Hphi Hbm] Hlnk []").
    { rewrite /fs_footprint /img_state.
      cbn [fss_sb fss_sbb fss_inodes fss_used].
      iSplitL "Hb1"; [iExact "Hb1" |].
      iSplitL "Hphi"; [iExact "Hphi" |].
      rewrite /free_bitmap /free_bitmap_at.
      iDestruct "Hbm" as "[Hbmb Hpool]". iFrame. }
    rewrite /fs_pure /img_state.
    cbn [fss_sb fss_sbb fss_inodes fss_used].
    iSplitR; [iPureIntro; exact Hparse |].
    rewrite (big_sepM_img_nodes
               (fun i n => ⌜inode_local i n⌝%I) (fs_blocks dk) sb nib).
    iApply big_sepS_intro. iModIntro. iIntros (z Hz). iPureIntro.
    exact (img_inode_local (fs_blocks dk) sb cov nib z Hwf Hrw Hbare Hfull
             Hnin Hcovdata Hz).
  Qed.

  (* ...and the shape [P_wf] is stated in.  [FsState.fs_view] binds the
     state existentially, so the residual is what a caller must still
     account for.  THE RESIDUAL IS NOT OPTIONAL: at the mkfs image it is
     empty (durable-disk 2c's survey (iii) -- home is [{1} ∪ [33,2000)],
     block 0 and the log region are outside it, and [img_owned] covers the
     rest: W5 makes every used data block a live inode's and every unused
     one a member of [free_set]), but nothing makes exactness true of an
     arbitrary reachable state, and returning the leftover elements is
     what keeps [P_wf] honest without a domain sweep.  Its BLOCK-map
     reading is [fs_restrict (fs_blocks dk) (home ∖ img_owned …)], through
     [big_sepM_fs_restrict]. *)
  Corollary fs_dur_view_of_image (g : gname) (dk : Z -> bv 8) (ndisk : nat)
      (sb : fs_sb) (nib : nat) (cov : gset Z) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    fs_region_bare (fs_blocks dk) sb nib = true ->
    fs_root_no_self (fs_blocks dk) sb = true ->
    fs_dbelems g (fs_dbytes (fs_restrict (fs_blocks dk)
                              (fs_home_set cov (FsImg.sb_logstart sb))))
    ⊢ |==> ∃ Gd : fs_dur_names,
        FsState.fs_view (fs_gamma_D g Gd)
        ∗ ([∗ map] i ↦ n ∈ img_nodes (fs_blocks dk) sb nib,
             top_frag (fs_gamma_D g Gd) i n)
        ∗ ([∗ set] b ∈ fs_home_set cov (FsImg.sb_logstart sb)
                       ∖ img_owned (fs_blocks dk) sb nib,
             blk_owned (fs_gamma_D g Gd) b (fs_blocks dk b)).
  Proof.
    intros Himg Hbare Hns.
    iIntros "Hd".
    iMod (fs_dur_of_image g dk ndisk sb nib cov Himg Hbare Hns with "Hd")
      as (Gd) "(Htopa & Htfr & Hst & Hrem)".
    iModIntro. iExists Gd. iFrame "Htfr Hrem".
    rewrite /FsState.fs_view. iExists (img_state (fs_blocks dk) sb nib).
    iFrame "Hst". iExact "Htopa".
  Qed.

End DurImgMain.

(* ===================================================================== *)
(* 11.  THE IMAGE'S KIND ASSIGNMENT, AND THE DURABLE TIE AT IT            *)
(*      (durable-disk 3b')                                                *)
(*                                                                        *)
(*  [FsCrash.P_fs_alloc] used to fill [P_wf] by an unconditional re-base   *)
(*  of a flat byte blob.  With the flip the durable body carries the PURE  *)
(*  tie [FsDurWire.kinds_of_state] beside the blob, so the boot owes THREE *)
(*  pure facts about the image: a kind per home block, that every home     *)
(*  block's bytes ARE that kind's encoding ([dwire_bridge]), and that the  *)
(*  assignment agrees with the image's own abstract state at the image's   *)
(*  own geometry.  All three are here, and all three are PURE -- nothing   *)
(*  in this section mentions a resource.                                   *)
(*                                                                        *)
(*  THE ASSIGNMENT IS THE OBVIOUS ONE and its three arms are exactly the   *)
(*  three [kind_write_ok] discharges the suppliers use: the bitmap block   *)
(*  is the image's own bit set, a block of the inode region is its own     *)
(*  sixteen records, and everything else is its bytes.  The region arm     *)
(*  takes [k mod 16] rather than [k] so that the function is TOTAL in the  *)
(*  slot index: [ko_recwf] quantifies over every [j : nat], and a record   *)
(*  read at a slot past the block's sixteen is not a record of the image   *)
(*  at all (it would name an inum in the NEXT block, whose decode says     *)
(*  nothing about this one).  [di_recs] reads only [0..15], where          *)
(*  [k mod 16 = k], so nothing else ever sees the wrap.                    *)
(* ===================================================================== *)

Definition img_kinds (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : Z -> blk_kind :=
  fun b =>
    if decide (b = FsImg.sb_bmapstart sb)
    then KBitmap (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb)))
    else if decide (FsImg.sb_inodestart sb <= b
                    /\ b < FsImg.sb_inodestart sb + Z.of_nat nib)
    then KInode (fun k : nat =>
                   img_node P sb (16 * (b - FsImg.sb_inodestart sb)
                                  + Z.of_nat (k mod 16)%nat))
    else KData (P b).

Lemma img_kinds_at_bmap (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  img_kinds P sb nib (FsImg.sb_bmapstart sb)
  = KBitmap (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb))).
Proof. rewrite /img_kinds decide_True //. Qed.

Lemma img_kinds_at_region (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (j : Z) :
  FsImg.sb_inodestart sb + Z.of_nat nib <= FsImg.sb_bmapstart sb ->
  0 <= j -> j < Z.of_nat nib ->
  img_kinds P sb nib (FsImg.sb_inodestart sb + j)
  = KInode (fun k : nat => img_node P sb (16 * j + Z.of_nat (k mod 16)%nat)).
Proof.
  intros Hgeo Hj0 Hjn. rewrite /img_kinds.
  rewrite decide_False; [| lia].
  rewrite decide_True; [| lia].
  replace (FsImg.sb_inodestart sb + j - FsImg.sb_inodestart sb) with j
    by lia.
  reflexivity.
Qed.

Lemma img_kinds_at_data (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (b : Z) :
  b <> FsImg.sb_bmapstart sb ->
  ~ (FsImg.sb_inodestart sb <= b
     /\ b < FsImg.sb_inodestart sb + Z.of_nat nib) ->
  img_kinds P sb nib b = KData (P b).
Proof.
  intros H1 H2. rewrite /img_kinds decide_False; [| exact H1].
  rewrite decide_False; [reflexivity | exact H2].
Qed.

(* THE ONE PIECE OF SLOT ARITHMETIC, factored so the encoding lemma and
   the well-formedness lemma share it: at a block of the region whose bytes
   decode to [ds], inum [16*j + k] reads record [k]. *)
Lemma img_region_slot (P : Z -> list (bv 8)) (sb : fs_sb)
    (j : Z) (k : nat) (ds : list dinode) :
  diblk_wf ds -> P (FsImg.sb_inodestart sb + j) = diblk_bytes ds ->
  0 <= j -> 0 <= 16 * j + Z.of_nat k < 2 ^ 32 -> (k < 16)%nat ->
  fs_dinode P sb (16 * j + Z.of_nat k) = ds !!! k.
Proof.
  intros Hdwf Hblk Hj0 Hrng Hk.
  assert (Hbv : bv_unsigned (fs_inum_bv (16 * j + Z.of_nat k))
                = 16 * j + Z.of_nat k).
  { rewrite /fs_inum_bv. apply Z_to_bv_small.
    assert (Hm : bv_modulus 32 = 2 ^ 32) by (vm_compute; reflexivity).
    rewrite Hm. lia. }
  assert (Hslot : islot (fs_inum_bv (16 * j + Z.of_nat k)) = k).
  { rewrite /islot Hbv (Z.mul_comm 16 j) Z.add_comm Z_mod_plus_full.
    rewrite Z.mod_small; lia. }
  assert (Hblk2 : P (IBLOCK (fs_inum_bv (16 * j + Z.of_nat k))
                            (FsImg.sb_inodestart sb)) = diblk_bytes ds).
  { rewrite /IBLOCK Hbv.
    assert (Hd : (16 * j + Z.of_nat k) `div` 16 = j).
    { rewrite (Z.mul_comm 16 j) Z.div_add_l; [| lia].
      rewrite (Z.div_small (Z.of_nat k) 16); lia. }
    rewrite Hd.
    replace (j + FsImg.sb_inodestart sb)
      with (FsImg.sb_inodestart sb + j) by lia.
    exact Hblk. }
  rewrite (fs_dinode_of_diblk P sb (16 * j + Z.of_nat k) ds Hdwf Hblk2)
          Hslot //.
Qed.

(* ...and its two readings *)
Lemma img_region_block_enc (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (j : Z) :
  fs_blocks_full P -> 16 * Z.of_nat nib <= 2 ^ 32 ->
  0 <= j -> j < Z.of_nat nib ->
  diblk_bytes
    (di_recs (fun k : nat => img_node P sb (16 * j + Z.of_nat (k mod 16)%nat)))
  = P (FsImg.sb_inodestart sb + j).
Proof.
  intros Hfull Hnib Hj0 Hjn.
  destruct (diblk_bytes_surj (P (FsImg.sb_inodestart sb + j)) (Hfull _))
    as (ds & Hdwf & Hde).
  rewrite Hde. f_equal.
  pose proof Hdwf as [Hlen Hall].
  apply list_eq. intros k.
  destruct (Nat.lt_ge_cases k 16%nat) as [Hk | Hk].
  - rewrite (di_recs_lookup _ k Hk) era_node_rec.
    assert (Hmod : (k mod 16)%nat = k) by (apply Nat.mod_small; lia).
    rewrite Hmod.
    assert (Hrng : 0 <= 16 * j + Z.of_nat k < 2 ^ 32) by lia.
    rewrite (img_region_slot P sb j k ds Hdwf Hde Hj0 Hrng Hk).
    assert (Hkl : (k < length ds)%nat) by lia.
    destruct (lookup_lt_is_Some_2 ds k Hkl) as [d Hd].
    rewrite Hd (list_lookup_total_correct ds k d Hd) //.
  - rewrite lookup_ge_None_2; [| rewrite di_recs_length; lia].
    rewrite lookup_ge_None_2; [reflexivity | lia].
Qed.

Lemma img_region_rec_wf (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (j : Z) (k : nat) :
  fs_blocks_full P -> 16 * Z.of_nat nib <= 2 ^ 32 ->
  0 <= j -> j < Z.of_nat nib -> (k < 16)%nat ->
  dinode_wf (fs_dinode P sb (16 * j + Z.of_nat k)).
Proof.
  intros Hfull Hnib Hj0 Hjn Hk.
  destruct (diblk_bytes_surj (P (FsImg.sb_inodestart sb + j)) (Hfull _))
    as (ds & Hdwf & Hde).
  pose proof Hdwf as [Hlen Hall].
  assert (Hrng : 0 <= 16 * j + Z.of_nat k < 2 ^ 32) by lia.
  rewrite (img_region_slot P sb j k ds Hdwf Hde Hj0 Hrng Hk).
  assert (Hkl : (k < length ds)%nat) by lia.
  destruct (lookup_lt_is_Some_2 ds k Hkl) as [d Hd].
  rewrite (list_lookup_total_correct ds k d Hd).
  exact (Forall_lookup_1 _ _ _ _ Hall Hd).
Qed.

(* EVERY HOME BLOCK'S BYTES ARE ITS KIND'S ENCODING -- and in fact every
   block's are, so the bridge below needs no home-set case analysis. *)
Lemma img_kinds_enc (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) (b : Z) :
  fs_blocks_full P -> 16 * Z.of_nat nib <= 2 ^ 32 ->
  FsImg.sb_inodestart sb + Z.of_nat nib <= FsImg.sb_bmapstart sb ->
  kind_enc (img_kinds P sb nib b) = P b.
Proof.
  intros Hfull Hnib Hgeo.
  destruct (decide (b = FsImg.sb_bmapstart sb)) as [-> | Hbm].
  { rewrite img_kinds_at_bmap. cbn [kind_enc].
    exact (bm_bytes_fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb))
             (Hfull _)). }
  destruct (decide (FsImg.sb_inodestart sb <= b
                    /\ b < FsImg.sb_inodestart sb + Z.of_nat nib))
    as [Hin | Hout].
  { assert (Hj0 : 0 <= b - FsImg.sb_inodestart sb) by lia.
    assert (Hjn : b - FsImg.sb_inodestart sb < Z.of_nat nib) by lia.
    replace b with (FsImg.sb_inodestart sb + (b - FsImg.sb_inodestart sb))
      by lia.
    rewrite (img_kinds_at_region P sb nib (b - FsImg.sb_inodestart sb)
               Hgeo Hj0 Hjn).
    cbn [kind_enc].
    exact (img_region_block_enc P sb nib (b - FsImg.sb_inodestart sb)
             Hfull Hnib Hj0 Hjn). }
  rewrite (img_kinds_at_data P sb nib b Hbm Hout) //.
Qed.

Lemma img_kinds_blocksized (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (cov : gset Z) (ls : Z) :
  fs_blocks_full P -> 16 * Z.of_nat nib <= 2 ^ 32 ->
  FsImg.sb_inodestart sb + Z.of_nat nib <= FsImg.sb_bmapstart sb ->
  kinds_blocksized (img_kinds P sb nib) cov ls.
Proof.
  intros Hfull Hnib Hgeo b _.
  rewrite (img_kinds_enc P sb nib b Hfull Hnib Hgeo). exact (Hfull b).
Qed.

Lemma img_kinds_bridge (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (cov : gset Z) (ls : Z) :
  fs_blocks_full P -> 16 * Z.of_nat nib <= 2 ^ 32 ->
  FsImg.sb_inodestart sb + Z.of_nat nib <= FsImg.sb_bmapstart sb ->
  dwire_bridge (img_kinds P sb nib)
    (fs_restrict P (fs_home_set cov ls)) cov ls.
Proof.
  intros Hfull Hnib Hgeo. split.
  - apply fs_restrict_dom.
  - intros b Hb.
    assert (Hlk : fs_restrict P (fs_home_set cov ls) !! b = Some (P b)).
    { apply fs_restrict_lookup_Some. split; [exact Hb | reflexivity]. }
    rewrite Hlk (img_kinds_enc P sb nib b Hfull Hnib Hgeo) //.
Qed.

(* THE TIE ITSELF, at the image's own geometry.  [nin] is [16 * nib] --
   the inums the REGION holds, which is what indexes [ko_slot] -- and not
   [sb_ninodes], because [ko_inodeblk] has to cover every block of the
   region and mkfs rounds the inode count up to a whole block. *)
Lemma img_kinds_of_state (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  fs_blocks_full P -> 16 * Z.of_nat nib <= 2 ^ 32 ->
  FsImg.sb_inodestart sb + Z.of_nat nib <= FsImg.sb_bmapstart sb ->
  kinds_of_state
    (MkDGeom (FsImg.sb_bmapstart sb) (FsImg.sb_inodestart sb))
    (16 * Z.of_nat nib) (img_state P sb nib) (img_kinds P sb nib).
Proof.
  intros Hfull Hnib Hgeo. split; cbn [dg_bmap dg_ist].
  - rewrite img_kinds_at_bmap /img_state. cbn [fss_used]. reflexivity.
  - intros j Hj0 Hjn16.
    assert (Hjn : j < Z.of_nat nib) by lia.
    eexists. exact (img_kinds_at_region P sb nib j Hgeo Hj0 Hjn).
  - intros i n Hi. rewrite /img_state in Hi. cbn [fss_inodes] in Hi.
    destruct (img_nodes_lookup_inv P sb nib i n Hi) as [Hreg ->].
    apply region_inums_spec in Hreg.
    assert (Hd0 : 0 <= i `div` 16) by (apply Z.div_pos; lia).
    assert (Hdn : i `div` 16 < Z.of_nat nib).
    { apply (Z.div_lt_upper_bound i 16 (Z.of_nat nib)); lia. }
    split; [lia |].
    eexists. split.
    + exact (img_kinds_at_region P sb nib (i `div` 16) Hgeo Hd0 Hdn).
    + cbv beta.
      assert (Hm : (Z.to_nat (i `mod` 16) mod 16)%nat
                   = Z.to_nat (i `mod` 16)).
      { apply Nat.mod_small.
        pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as [Ha Hb]. lia. }
      rewrite Hm.
      pose proof (Z.div_mod i 16 ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as [Ha Hb].
      replace (16 * (i `div` 16) + Z.of_nat (Z.to_nat (i `mod` 16)))
        with i by lia.
      reflexivity.
  - intros b nd HK j.
    destruct (decide (b = FsImg.sb_bmapstart sb)) as [-> | Hbm].
    { rewrite img_kinds_at_bmap in HK. discriminate. }
    destruct (decide (FsImg.sb_inodestart sb <= b
                      /\ b < FsImg.sb_inodestart sb + Z.of_nat nib))
      as [Hin | Hout];
      [| rewrite (img_kinds_at_data P sb nib b Hbm Hout) in HK;
         discriminate].
    assert (Hj0 : 0 <= b - FsImg.sb_inodestart sb) by lia.
    assert (Hjn : b - FsImg.sb_inodestart sb < Z.of_nat nib) by lia.
    assert (Hb : b = FsImg.sb_inodestart sb
                     + (b - FsImg.sb_inodestart sb)) by lia.
    rewrite Hb (img_kinds_at_region P sb nib (b - FsImg.sb_inodestart sb)
                  Hgeo Hj0 Hjn) in HK.
    injection HK as <-. rewrite era_node_rec.
    assert (Hmod : (j mod 16 < 16)%nat)
      by (apply Nat.mod_upper_bound; lia).
    exact (img_region_rec_wf P sb nib (b - FsImg.sb_inodestart sb)
             (j mod 16)%nat Hfull Hnib Hj0 Hjn Hmod).
Qed.
