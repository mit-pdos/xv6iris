(* ====================================================================== *)
(*  FsCollect.v -- COLLECTION AT QUIESCENCE, THE BYTE SIDE                 *)
(*  (durable-disk lane C-2; claude-notes/design/durable-fs-plan.md         *)
(*   section 4, "Where the commit's proof comes from")                     *)
(*                                                                        *)
(*  [FsDurSnap.fs_snap_alloc] takes [snap_ok S D]: the bytes are the       *)
(*  encoding of [S], every inode is well formed, no two share a block --   *)
(*  and NOTHING MAINTAINS THAT FACT INCREMENTALLY (plan section 8, the     *)
(*  machine-checked refutation [FsDurTrunc.v]).  The commit RECONSTRUCTS   *)
(*  it at the one moment the file system's own invariants are all clean.   *)
(*                                                                        *)
(*  THIS FILE IS THE HALF THAT DOES THE ARITHMETIC, and nothing else: it   *)
(*  takes the era's pieces AS ALREADY COLLECTED -- the superblock's block, *)
(*  the bitmap and the free pool, the region's records, one bundle per     *)
(*  region inum at a share whose double is invalid, and the link family -- *)
(*  and reads [snap_ok] off their separating conjunction against the byte  *)
(*  view's authority.  WHERE the pieces come from (fifty cache escrows,    *)
(*  the pool invariant, [InodeRegion.ireg_inv], [BitmapInv.bitmap_inv])    *)
(*  is the other half, and it is deliberately not here: this file is a     *)
(*  LEAF over the predicate layer, so it costs [ProofEndOp]'s cone         *)
(*  nothing and iterates in seconds.                                       *)
(*                                                                        *)
(*  EVERY CONCLUSION IS PURE, so no lemma below consumes anything: an      *)
(*  [iDestruct .. as %H] against a [⌜ ⌝] conclusion leaves its hypotheses  *)
(*  in place, which is what lets the commit hold all fifty escrows open at *)
(*  ONE ghost step and hand every one of them back untouched (plan         *)
(*  section 3, "it moves NO durable resource").                            *)
(*                                                                        *)
(*  WHAT THE SEPARATING CONJUNCTION BUYS, and it is the whole design:      *)
(*                                                                        *)
(*   - [sk_disj] (no two nodes share a block) and [sk_own_used] (a node's  *)
(*     blocks are marked in use and none of them is metadata) are read     *)
(*     off the [∗], never maintained.  Two bundles at shares whose         *)
(*     DOUBLES are invalid cannot alias ([dfrac_nvalid_pair] below is the  *)
(*     arithmetic: an unlocked inode holds 1, a read-locked one 3/4, and   *)
(*     3/4 + 3/4 > 1 -- which is exactly why a read-locker's withdrawal    *)
(*     is a QUARTER and not a half).                                       *)
(*   - [sk_slot] ("one node never names one block twice") is the same      *)
(*     refutation INSIDE one bundle.                                       *)
(*   - the byte ties [sk_sb]/[sk_bmap]/[sk_rec]/[sk_blk]/[sk_ind] are      *)
(*     AGREEMENTS against the byte authority, so any share suffices.       *)
(*                                                                        *)
(*  THE BLOCK MAP THE SNAPSHOT IS STATED AT is [col_view C home] -- the    *)
(*  bio layer's cache map restricted to the home blocks, which is exactly  *)
(*  [FsCrash.fs_commit_L_sector0_rec]'s new committed view [D'] (it        *)
(*  concludes at [fs_restrict (dv_of_D L) (fs_home_set cov ls)] for [L]    *)
(*  the very cache map [LogInv.log_state] carries).  So the commit's       *)
(*  receipt and this lemma's [D] are one term.                            *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list sets bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_map.

Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types.
Require Import RiscvPtsto.   (* [riscvGS] -- IMPORTED: a capacity class used
                                as a Context binder is inert otherwise      *)
Require Import Xv6G.         (* [xv6G], the ghost bundle                    *)
Require Import BioDefs.      (* [BSIZE]                                     *)
Require Import FsImg.        (* [fs_sb], [SB_BNO], [fs_sb_ok], [FS_MAXFILE] *)
Require Import BitmapEnc.    (* [bm_bytes]                                  *)
Require Import BlockWords.   (* [ind_bytes] -- [FsDurSnap.sk_ind]'s encoder  *)
Require Import DinodeEnc.    (* [diblk_bytes], [diblk_wf], [dinode_bytes]   *)
Require Import LogDefs.      (* [fs_restrict]                               *)
Require Import FsWf.         (* [dv_of_D]                                   *)
Require Import FsBlocks.     (* [fs_names], [fsblock_q], [bytes_dom]        *)
Require Import FsBytesGamma. (* [fs_gamma_L] and the two bridges            *)
Require Import FsStateDefs.  (* [blk_owned_q], [phi_excl]                   *)
Require Import FsStateInode. (* [inode_local], [ind_owned_q]                *)
Require Import FsStateBitmap. (* [free_bitmap_at], [free_pool_used_q]        *)
Require Import FsState.       (* [fs_state_rec], [fs_links], [sb_owned]     *)
Require Import FsStateEra.    (* [inode_owned_era_q]                        *)
Require Import InodeRegion.   (* [dinode_at], [ireg_recs], [ireg_couple]    *)
Require Import FsDurSnap.     (* [snap_bytes], [snap_local], [snap_ok]      *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  0.  TWO SHARES WHOSE DOUBLES ARE INVALID CANNOT MEET                   *)
(*                                                                        *)
(*  The cover lemma ([IcacheEscrow.ic_escrow_body_cover]) hands each slot's *)
(*  bundle out at a share [dq] with [~ ✓ (dq ⋅ dq)] -- fraction 1 for an   *)
(*  unlocked inode, 3/4 for a read-locked one.  Cross-inode disjointness   *)
(*  needs the MIXED product to be invalid too, and it is: the condition    *)
(*  forces the owned part of each share to exceed a half, so any two of    *)
(*  them exceed the whole.  This is the arithmetic plan section 4 states   *)
(*  as "3/4 + 3/4 > 1, which is why the reader's share is a quarter".      *)
(* ====================================================================== *)

(* TWO SHARES THAT EACH EXCEED A HALF CANNOT BOTH FIT INSIDE ONE, twice:
   the strict half (two [DfracOwn]s, whose sum must merely be [<= 1]) and
   the non-strict one (a [DfracBoth] on either side, whose sum must be
   [< 1]).  Both are the same contradiction -- if the sum fitted, each
   share would have to be smaller than the other. *)
Lemma qp_no_pair_lt (q1 q2 : Qp) :
  (1 < q1 + q1)%Qp -> (1 < q2 + q2)%Qp -> (q1 + q2 ≤ 1)%Qp -> False.
Proof.
  intros H1 H2 Hle.
  assert (Ha : (q2 < q1)%Qp).
  { apply (proj2 (Qp.add_lt_mono_l q2 q1 q1)).
    exact (Qp.le_lt_trans _ _ _ Hle H1). }
  assert (Hb : (q1 < q2)%Qp).
  { apply (proj2 (Qp.add_lt_mono_l q1 q2 q2)).
    rewrite (Qp.add_comm q2 q1).
    exact (Qp.le_lt_trans _ _ _ Hle H2). }
  exact (proj1 (Qp.lt_nge q2 q1) Ha (Qp.lt_le_incl _ _ Hb)).
Qed.

Lemma qp_no_pair_le (q1 q2 : Qp) :
  (1 ≤ q1 + q1)%Qp -> (1 ≤ q2 + q2)%Qp -> (q1 + q2 < 1)%Qp -> False.
Proof.
  intros H1 H2 Hlt.
  assert (Ha : (q2 < q1)%Qp).
  { apply (proj2 (Qp.add_lt_mono_l q2 q1 q1)).
    exact (Qp.lt_le_trans _ _ _ Hlt H1). }
  assert (Hb : (q1 < q2)%Qp).
  { apply (proj2 (Qp.add_lt_mono_l q1 q2 q2)).
    rewrite (Qp.add_comm q2 q1).
    exact (Qp.lt_le_trans _ _ _ Hlt H2). }
  exact (proj1 (Qp.lt_nge q2 q1) Ha (Qp.lt_le_incl _ _ Hb)).
Qed.

(* A SHARE WHOSE DOUBLE IS INVALID owns more than a half and is not the
   bare discarded knowledge (which doubles to itself). *)
Lemma dfrac_nvalid_shape (dq : dfrac) :
  ~ ✓ (dq ⋅ dq) ->
  exists q : Qp,
    (dq = DfracOwn q /\ (1 < q + q)%Qp)
    \/ (dq = DfracBoth q /\ (1 ≤ q + q)%Qp).
Proof.
  destruct dq as [q | | q]; intros Hn.
  - exists q. left. split; [reflexivity |].
    apply (proj2 (Qp.lt_nge 1 (q + q))). intros Hc. apply Hn.
    rewrite dfrac_op_own. apply dfrac_valid_own. exact Hc.
  - exfalso. apply Hn. rewrite dfrac_op_discarded.
    exact dfrac_valid_discarded.
  - exists q. right. split; [reflexivity |].
    apply (proj2 (Qp.le_ngt 1 (q + q))). intros Hc. apply Hn.
    apply dfrac_valid. cbn. exact Hc.
Qed.

Lemma dfrac_nvalid_pair (dq1 dq2 : dfrac) :
  ~ ✓ (dq1 ⋅ dq1) -> ~ ✓ (dq2 ⋅ dq2) -> ~ ✓ (dq1 ⋅ dq2).
Proof.
  intros H1 H2 Hv.
  destruct (dfrac_nvalid_shape dq1 H1) as (q1 & [[-> Hq1] | [-> Hq1]]);
    destruct (dfrac_nvalid_shape dq2 H2) as (q2 & [[-> Hq2] | [-> Hq2]]).
  - apply dfrac_valid in Hv. cbn in Hv.
    exact (qp_no_pair_lt q1 q2 Hq1 Hq2 Hv).
  - apply dfrac_valid in Hv. cbn in Hv.
    exact (qp_no_pair_le q1 q2 (Qp.lt_le_incl _ _ Hq1) Hq2 Hv).
  - apply dfrac_valid in Hv. cbn in Hv.
    exact (qp_no_pair_le q1 q2 Hq1 (Qp.lt_le_incl _ _ Hq2) Hv).
  - apply dfrac_valid in Hv. cbn in Hv.
    exact (qp_no_pair_le q1 q2 Hq1 Hq2 Hv).
Qed.

(* ...and the one reading of it the collection runs. *)
Lemma dfrac_full_pair (dq : dfrac) : ~ ✓ (DfracOwn 1 ⋅ dq).
Proof. exact (dfrac_full_nvalid dq). Qed.

(* ====================================================================== *)
(*  0a. A RECORD SITS AT ITS SLOT OF ITS BLOCK                             *)
(*                                                                        *)
(*  [FsDurImg.diblk_bytes_split] verbatim.  FOR RELOCATION: both belong    *)
(*  beside [DinodeEnc.diblk_bytes_lookup]; the copy is here for the same   *)
(*  reason the original is in [FsDurImg] -- an additive change to a file   *)
(*  that low rebuilds its whole cone on every iteration -- and this file   *)
(*  must not import [FsDurImg] (its cone reaches the whole boot chain).    *)
(* ====================================================================== *)

Lemma col_diblk_split (ds : list dinode) (k : nat) :
  Forall dinode_wf ds -> (k < length ds)%nat ->
  exists pre post,
    diblk_bytes ds = (pre ++ dinode_bytes (ds !!! k) ++ post)%list
    /\ length pre = (64 * k)%nat.
Proof.
  revert k. induction ds as [| d ds IH]; intros k Hall Hk;
    [simpl in Hk; lia |].
  inversion Hall as [| xd xds Hd Hall']; subst.
  destruct k as [| k].
  - exists [], (diblk_bytes ds).
    rewrite diblk_bytes_cons. split; reflexivity.
  - simpl in Hk.
    destruct (IH k Hall' ltac:(lia)) as (pre & post & Heq & Hlen).
    exists (dinode_bytes d ++ pre)%list, post.
    assert (Hs : (d :: ds) !!! S k = ds !!! k) by reflexivity.
    assert (Hla : length ((dinode_bytes d ++ pre)%list)
                  = (length (dinode_bytes d) + length pre)%nat)
      by apply length_app.
    pose proof (dinode_bytes_length d Hd) as H64.
    split; [| lia].
    rewrite Hs diblk_bytes_cons Heq.
    first [ exact (app_assoc (dinode_bytes d) pre
                     (dinode_bytes (ds !!! k) ++ post)%list)
          | exact (eq_sym (app_assoc (dinode_bytes d) pre
                     (dinode_bytes (ds !!! k) ++ post)%list)) ].
Qed.

Section Collect.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Implicit Types γfs : fs_names.

  (* ==================================================================== *)
  (*  1.  THE BLOCK READING OF THE LOGGED VIEW                             *)
  (* ==================================================================== *)

  (* The committed view the commit installs, BY NAME.  It is
     [FsCrash.fs_commit_L_sector0_rec]'s [D'] on the nose. *)
  Definition col_view (C : gmap Z (list (bv 8))) (home : gset Z)
    : gmap Z (list (bv 8)) := fs_restrict (dv_of_D C) home.

  (* What the WAL holds at the commit's ghost step: the byte view's
     authority and the pure rows of [FsBlocks.fs_bytes_body] (the log's own
     invariant, opened), beside the cache map's value.  Nothing else about
     the log is needed -- this is the whole of the interface. *)
  Definition col_auth γfs (Lb : gmap Z (bv 8))
      (C : gmap Z (list (bv 8))) (home : gset Z) : iProp Σ :=
    (ghost_map_auth (fs_bytes γfs) 1 Lb ∗
     ⌜dom C = home⌝ ∗
     ⌜forall b bs, C !! b = Some bs -> length bs = BSIZE⌝ ∗
     ⌜bytes_tie Lb C⌝ ∗ ⌜bytes_dom Lb home⌝)%I.

  (* THE ONE AGREEMENT EVERY BYTE TIE GOES THROUGH, and it needs no share:
     holding ANY fraction of a block's run says the block is a home block
     and that the committed view holds exactly those bytes there. *)
  Lemma col_blk γfs Lb C home (dq : dfrac) (b : Z) (bs : list (bv 8)) :
    col_auth γfs Lb C home -∗
    blk_owned_q (fs_gamma_L γfs) dq b bs -∗
    ⌜b ∈ home /\ col_view C home !! b = Some bs⌝.
  Proof.
    iIntros "(Ha & %Hdom & %Hlens & %Htie & %Hdm) Hb".
    rewrite gamma_blk_owned_q.
    iDestruct (fsblock_q_home (fs_bytes γfs) dq Lb home b bs Hdm with "Ha Hb")
      as %Hhome.
    assert (Hin : is_Some (C !! b))
      by (apply elem_of_dom; rewrite Hdom; exact Hhome).
    destruct Hin as [bsi Hbsi].
    (* [fsblock_q] is [Typeclasses Opaque] -- it has to be, a 1024-element
       [big_sepL] behind a definition is an [iFrame] hang -- so the pair is
       opened by an explicit unfold, not by [iDestruct] alone. *)
    rewrite /fsblock_q. iDestruct "Hb" as "[%Hlb Hr]".
    iDestruct (byte_range_q_lookup with "Ha Hr") as %Hsub.
    rewrite Z.add_0_r in Hsub.
    assert (Hbe : bs = bsi).
    { apply (map_seqZ_inj bs bsi (b * BSZ) Lb);
        [ rewrite Hlb (Hlens b bsi Hbsi) // | exact Hsub
        | exact (Htie b bsi Hbsi) ]. }
    iPureIntro. split; [exact Hhome |].
    rewrite /col_view fs_restrict_lookup_Some.
    split; [exact Hhome |]. rewrite /dv_of_D Hbsi /=. exact Hbe.
  Qed.

  Lemma col_blk_full γfs Lb C home (b : Z) (bs : list (bv 8)) :
    col_auth γfs Lb C home -∗
    blk_owned (fs_gamma_L γfs) b bs -∗
    ⌜b ∈ home /\ col_view C home !! b = Some bs⌝.
  Proof.
    rewrite blk_owned_1. iApply (col_blk γfs Lb C home (DfracOwn 1) b bs).
  Qed.

  (* ==================================================================== *)
  (*  2.  THE COLLECTED HAND                                               *)
  (* ==================================================================== *)

  (* ONE REGION INUM'S BUNDLE, at a share whose double is invalid.  This is
     alternative (c) of [IcacheEscrow.ic_slot_cover] and the ordinary pool
     row's payload, in one shape: an unlocked inode is at 1, a read-locked
     one at 3/4, and NOTHING ELSE reaches a commit (a write-locked one holds
     a positive share of an open transaction's token, which an empty
     [ln_tx] authority refutes -- [IcacheEscrow.ic_out_no_write_arm]). *)
  Definition col_bundle γfs (γi : gname) (i : Z) (n : fs_node) : iProp Σ :=
    (∃ (dq : dfrac) (inum : bv 32),
       ⌜bv_unsigned inum = i⌝ ∗ ⌜~ ✓ (dq ⋅ dq)⌝ ∗
       inode_owned_era_q γfs dq γi inum n)%I.

  (* THE REGION'S RECORDS, with the proxy authority they are coupled to.
     This is [InodeRegion.ireg_body] minus the slot columns: records park
     region-side at fraction 1 always (plan section 2, ruling (i)), so the
     commit reads every one of them off ONE opening of [iregN]. *)
  Definition col_recs γfs (γi : gname) (ist : Z) (nib : nat)
      (m : gmap Z dinode) : iProp Σ :=
    (ghost_map_auth γi 1 m ∗
     [∗ list] bi ∈ seq 0 nib,
        ∃ ds : list dinode,
          ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝ ∗ ireg_recs γfs ist bi ds)%I.

  (* THE GEOMETRY, and every clause of it is the boot configuration's.
     [col_size] is what turns "I hold this block's bytes" into "this block
     is inside the bitmap's range", which is how the free pool refutes a
     clear bit; the rest is [FsCfgBoot.fs_boot_image_wf]'s own arithmetic
     ([FsImg.fs_sb_ok], "the region is exactly [[inodestart, bmapstart)]",
     [sb_ninodes <= 16 * nib], [16 * nib <= 2 ^ 32]). *)
  Record col_geom (sb : fs_sb) (ist : Z) (nib : nat) (home : gset Z)
    : Prop := MkColGeom {
    cg_sbok  : fs_sb_ok sb;
    cg_ist   : sb_inodestart sb = ist;
    cg_reg   : ist + Z.of_nat nib <= sb_bmapstart sb;
    cg_nin   : sb_ninodes sb <= 16 * Z.of_nat nib;
    cg_wide  : 16 * Z.of_nat nib <= 2 ^ 32;
    cg_size  : forall b : Z, b ∈ home -> 0 <= b < sb_size sb;
  }.

  Global Arguments cg_sbok {_ _ _ _} _.
  Global Arguments cg_ist {_ _ _ _} _.
  Global Arguments cg_reg {_ _ _ _} _.
  Global Arguments cg_nin {_ _ _ _} _.
  Global Arguments cg_wide {_ _ _ _} _.
  Global Arguments cg_size {_ _ _ _} _.

  (* THE HAND.  Every conjunct is a piece the era already parks somewhere an
     invariant opening reaches (plan section 4's second bullet); assembling
     them is the OTHER half of the collection and is not this file's. *)
  Definition col_hand γfs (γi : gname) (ist : Z) (nib : nat)
      (sb : fs_sb) (sbb : list (bv 8)) (used : gset Z)
      (I : gmap Z fs_node) (m : gmap Z dinode)
      (Lb : gmap Z (bv 8)) (C : gmap Z (list (bv 8))) (home : gset Z)
    : iProp Σ :=
    (⌜col_geom sb ist nib home⌝ ∗
     ⌜forall i : Z, i ∈ dom I <-> 0 <= i < 16 * Z.of_nat nib⌝ ∗
     col_auth γfs Lb C home ∗
     sb_owned (fs_gamma_L γfs) sb sbb ∗
     free_bitmap_at (fs_gamma_L γfs) (sb_bmapstart sb) (sb_size sb) used ∗
     col_recs γfs γi ist nib m ∗
     ([∗ map] i ↦ n ∈ I, col_bundle γfs γi i n) ∗
     fs_links (fs_link γfs) I)%I.

  (* the abstract state the hand describes: the superblock the region was
     configured from, block 1's bytes, the map the [ftop_inv] authority
     holds, and the bitmap's own bits *)
  Definition col_state (sb : fs_sb) (sbb : list (bv 8))
      (I : gmap Z fs_node) (used : gset Z) : fs_state_rec :=
    MkFsS sb sbb I used.

  (* ==================================================================== *)
  (*  3.  READING ONE BUNDLE                                               *)
  (* ==================================================================== *)

  (* a node's OWN block, out of its bundle: a data block it holds or its
     indirect block ([FsDurSnap.fn_owns] is exactly those two) *)
  Lemma col_bundle_owns γfs γi (i b : Z) (n : fs_node) :
    fn_owns n b ->
    col_bundle γfs γi i n -∗
    ∃ (dq : dfrac) (bs : list (bv 8)),
      ⌜~ ✓ (dq ⋅ dq)⌝ ∗ blk_owned_q (fs_gamma_L γfs) dq b bs.
  Proof.
    intros Howns. iIntros "H".
    iDestruct "H" as (dq inum Hbv Hnv) "H".
    rewrite /inode_owned_era_q.
    iDestruct "H" as "(_ & Hblk & Hind & _ & _)".
    destruct Howns as [(k & [bs Hbs] & Hk) | [Hnz Hind]].
    - iExists dq, bs. iSplitR; [iPureIntro; exact Hnv |].
      rewrite (big_sepM_lookup _ _ k bs Hbs). rewrite Hk. iExact "Hblk".
    - iExists dq, (ind_bytes (fn_ent n)).
      iSplitR; [iPureIntro; exact Hnv |].
      rewrite /ind_owned_q (decide_False _ _ Hnz) Hind. iExact "Hind".
  Qed.

  (* the bundle's own local clause, and its record proxy *)
  Lemma col_bundle_local γfs γi (i : Z) (n : fs_node) :
    col_bundle γfs γi i n -∗ ⌜inode_local i n⌝.
  Proof.
    iIntros "H". iDestruct "H" as (dq inum Hbv Hnv) "H".
    rewrite /inode_owned_era_q.
    iDestruct "H" as "(_ & _ & _ & _ & %Hloc)".
    iPureIntro. rewrite -Hbv. exact Hloc.
  Qed.

  Lemma col_bundle_rec γfs γi (i : Z) (n : fs_node) (m : gmap Z dinode) :
    ghost_map_auth γi 1 m -∗ col_bundle γfs γi i n -∗
    ⌜m !! i = Some (fn_rec n)⌝.
  Proof.
    iIntros "Ha H". iDestruct "H" as (dq inum Hbv Hnv) "H".
    rewrite /inode_owned_era_q. iDestruct "H" as "(Hd & _)".
    rewrite /dinode_at Hbv.
    iApply (ghost_map_lookup with "Ha Hd").
  Qed.

  (* ONE NODE NEVER NAMES ONE BLOCK TWICE, off its own [∗]: two of its slots
     at one nonzero address would be two owners of that block at a share
     whose double is invalid. *)
  Lemma col_bundle_slot γfs γi (i : Z) (n : fs_node) :
    col_bundle γfs γi i n -∗ ⌜fn_slot_inj n⌝.
  Proof.
    iIntros "H".
    iDestruct (col_bundle_local with "H") as %Hloc.
    rewrite /fn_slot_inj.
    rewrite bi.pure_forall. iIntros (k).
    rewrite bi.pure_forall. iIntros (j).
    rewrite bi.pure_forall. iIntros (Hk).
    rewrite bi.pure_forall. iIntros (Hj).
    rewrite bi.pure_forall. iIntros (Hnz).
    rewrite bi.pure_forall. iIntros (Heq).
    destruct (decide (k = j)) as [-> | Hne]; [by iPureIntro |].
    (* the two slots are two blocks of THIS node's footprint *)
    iExFalso.
    iAssert (∃ (dq : dfrac) (bs1 bs2 : list (bv 8)),
               ⌜~ ✓ (dq ⋅ dq)⌝ ∗
               blk_owned_q (fs_gamma_L γfs) dq (fn_slot n k) bs1 ∗
               blk_owned_q (fs_gamma_L γfs) dq (fn_slot n j) bs2)%I
      with "[H]" as (dq bs1 bs2 Hnv) "[H1 H2]".
    { iDestruct "H" as (dq inum Hbv Hnv) "H".
      rewrite /inode_owned_era_q.
      iDestruct "H" as "(_ & Hblk & Hind & _ & _)".
      iExists dq.
      (* slot [FS_MAXFILE] is the indirect block; the others are data *)
      destruct (decide (k = FS_MAXFILE)) as [-> | HkD].
      - (* k is the indirect slot, so j is a data slot (k <> j) *)
        assert (HjD : (j < FS_MAXFILE)%nat) by lia.
        rewrite fn_slot_ind in Hnz. rewrite fn_slot_ind.
        rewrite (fn_slot_data n j HjD).
        rewrite (fn_slot_ind n) (fn_slot_data n j HjD) in Heq.
        assert (Hjnz : fn_naddr n j <> 0) by (rewrite -Heq; exact Hnz).
        destruct (proj2 (inl_blk_dom Hloc j HjD) Hjnz) as [bsj Hbsj].
        iExists (ind_bytes (fn_ent n)), bsj.
        iSplitR; [iPureIntro; exact Hnv |].
        iSplitL "Hind".
        + rewrite /ind_owned_q (decide_False _ _ Hnz). iExact "Hind".
        + rewrite (big_sepM_lookup _ _ j bsj Hbsj). iExact "Hblk".
      - assert (HkD' : (k < FS_MAXFILE)%nat) by lia.
        rewrite (fn_slot_data n k HkD') in Hnz.
        rewrite (fn_slot_data n k HkD') in Heq.
        rewrite (fn_slot_data n k HkD').
        destruct (proj2 (inl_blk_dom Hloc k HkD') Hnz) as [bsk Hbsk].
        destruct (decide (j = FS_MAXFILE)) as [-> | HjD].
        + rewrite fn_slot_ind. rewrite fn_slot_ind in Heq.
          assert (Hinz : fn_indb n <> 0) by (rewrite -Heq; exact Hnz).
          iExists bsk, (ind_bytes (fn_ent n)).
          iSplitR; [iPureIntro; exact Hnv |].
          iSplitL "Hblk".
          * rewrite (big_sepM_lookup _ _ k bsk Hbsk). iExact "Hblk".
          * rewrite /ind_owned_q (decide_False _ _ Hinz). iExact "Hind".
        + assert (HjD' : (j < FS_MAXFILE)%nat) by lia.
          rewrite (fn_slot_data n j HjD').
          rewrite (fn_slot_data n j HjD') in Heq.
          assert (Hjnz : fn_naddr n j <> 0) by (rewrite -Heq; exact Hnz).
          destruct (proj2 (inl_blk_dom Hloc j HjD') Hjnz) as [bsj Hbsj].
          iExists bsk, bsj.
          iSplitR; [iPureIntro; exact Hnv |].
          rewrite (big_sepM_delete _ (fn_blk n) k bsk Hbsk).
          iDestruct "Hblk" as "[Hk Hrest]".
          assert (Hbsj' : delete k (fn_blk n) !! j = Some bsj)
            by (rewrite lookup_delete_ne; [exact Hbsj | exact Hne]).
          rewrite (big_sepM_lookup _ _ j bsj Hbsj').
          iSplitL "Hk"; [iExact "Hk" | iExact "Hrest"]. }
    rewrite Heq.
    iApply (blk_owned_q_excl (fs_gamma_L γfs) (fs_gamma_L_excl γfs) dq dq
              (fn_slot n j) bs1 bs2 (dfrac_nvalid_pair dq dq Hnv Hnv)
              with "H1 H2").
  Qed.

  (* ==================================================================== *)
  (*  4.  THE FULL-FRACTION OWNERS: the three metadata roles               *)
  (* ==================================================================== *)

  (* the region's [bi]-th block, whole, off the records *)
  Lemma col_recs_blk γfs γi (ist : Z) (nib bi : nat) (m : gmap Z dinode) :
    (bi < nib)%nat ->
    col_recs γfs γi ist nib m -∗
    ∃ ds : list dinode,
      ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝ ∗
      blk_owned (fs_gamma_L γfs) (ist + Z.of_nat bi) (diblk_bytes ds).
  Proof.
    intros Hbi. iIntros "[_ Hl]".
    assert (Hlk : seq 0 nib !! bi = Some bi) by (apply lookup_seq; lia).
    rewrite (big_sepL_lookup _ _ bi bi Hlk).
    iDestruct "Hl" as (ds Hwf Hcp) "Hr".
    iExists ds. iSplitR; [iPureIntro; exact Hwf |].
    iSplitR; [iPureIntro; exact Hcp |].
    iDestruct (ireg_recs_to_blk γfs ist bi ds Hwf with "Hr") as "Hb".
    rewrite -gamma_blk_owned. iExact "Hb".
  Qed.

  (* ==================================================================== *)
  (*  5.  THE PURE CLAUSES, ONE AT A TIME                                  *)
  (* ==================================================================== *)

  (* ---- 5a. a block whose bytes anybody holds is IN USE ---------------- *)

  Lemma col_used_of_blk γfs Lb C home (sb : fs_sb) (used : gset Z)
      (ist : Z) (nib : nat) (dq : dfrac) (b : Z) (bs : list (bv 8)) :
    col_geom sb ist nib home ->
    col_auth γfs Lb C home -∗
    free_pool (fs_gamma_L γfs) (sb_size sb) used -∗
    blk_owned_q (fs_gamma_L γfs) dq b bs -∗ ⌜b ∈ used⌝.
  Proof.
    intros Hg. iIntros "Hau Hpool Hb".
    iDestruct (col_blk with "Hau Hb") as %[Hhome _].
    iApply (free_pool_used_q (fs_gamma_L γfs) (fs_gamma_L_excl γfs) dq
              (sb_size sb) used b bs (cg_size Hg b Hhome) with "Hpool Hb").
  Qed.

End Collect.
