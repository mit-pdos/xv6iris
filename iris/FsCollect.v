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
(*                                                                        *)
(* ====================================================================== *)
(*  WHO SUPPLIES [col_hand], AND THE FOUR THAT DO NOT YET                  *)
(*                                                                        *)
(*  Every conjunct of [col_hand] is meant to come off ONE opening of the   *)
(*  era's invariants at the commit's ghost step (plan section 4):          *)
(*                                                                        *)
(*    col_auth   -- [FsBlocks.fs_bytes_inv] at [logN], opened, beside the  *)
(*                  cache authority [LogInv.log_state] already carries;    *)
(*    col_recs   -- [InodeRegion.ireg_body] at [iregN] ([ireg_blk] IS      *)
(*                  [col_recs]'s row, [ireg_couple] and all);              *)
(*    free_bitmap_at -- [BitmapInv.bitmap_body] at [bitmapN];              *)
(*    the bundles -- the fifty [IcacheEscrow.ic_escrow]s at [icEscN .@ k]  *)
(*                  through [ic_escrow_body_cover] (alternative (c) IS     *)
(*                  [col_bundle], share condition and all) plus            *)
(*                  [ipool_inv_acc]'s ordinary rows;                       *)
(*    the dom row + snap_local -- [ftop_inv] at [ftopN] through            *)
(*                  [IregClean.ireg_snap_local_acc];                       *)
(*    col_geom   -- the boot configuration ([FsCollectImg.img_col_geom]).  *)
(*                                                                        *)
(*  ALL FOUR ARE NOW SUPPLIED -- (A) by C-3b and C-4, (B) by B''-tx5,      *)
(*  (C) by C-3a, (D) by C-3c -- and their entries below record where.      *)
(*  WHAT THE ASSEMBLY STILL LACKS IS TWO WINDOWS NOBODY HAD NAMED, (E)     *)
(*  and (F) at the end of this list.  Both are inside ONE transaction and  *)
(*  therefore unreachable at a commit; neither is PROVED so, because       *)
(*  neither parks a share of its transaction's [ln_tx] element the way     *)
(*  [IcacheEscrow.ic_pin_tx] and [IcacheEscrow.ipool_transit] do.          *)
(*                                                                        *)
(*  (A) THE PARTITION -- SUPPLIED (durable-disk lane C-3b), AND IT HAS      *)
(*      THREE PARTS.  [IcacheEscrow]'s section 5c: [ipool_body] gains [cn]  *)
(*      and [nib] and carries                                              *)
(*                                                                        *)
(*        region_inums nib = O union X union ic_live_inums ids             *)
(*                                                                        *)
(*      beside a QUARTER of every slot's [ic_id] ([ic_ids cn ids]), which  *)
(*      is what makes the row speak about the ESCROWS -- the arm holds a   *)
(*      half of the same cell, so a reader with both open reads ONE        *)
(*      identity ([ic_ids_pin]).  The collection's door is                 *)
(*      [ipool_inv_acc] with the pure reading [ipool_cover_inum], and      *)
(*      [ipool_partition_cached] is the exercise at the real shape.        *)
(*                                                                        *)
(*      B''-join's TWO-WAY row is FALSE in this kernel, for one reason     *)
(*      with two faces -- an inum a WALK is carrying.  iput's free path    *)
(*      deposits an AWAIT row, which cannot live in an invariant at all    *)
(*      ([EscrowInode.escA_inv] is an [inv]), so it stays under the itable *)
(*      lock and holds NO [FsStateEra.inode_owned_era]; and an eviction's  *)
(*      identity flip and its deposit are two ghost steps (the bundle's    *)
(*      three ledger columns do not exist until the refcount store has     *)
(*      fired).  Both are the third part [X], PINNED by [icfg_pext] whose  *)
(*      other half is a conjunct of [ipool], so it cannot swallow the      *)
(*      region; at boot it is empty.                                       *)
(*                                                                        *)
(*      THE THIRD PART IS TWO THINGS, AND THEY ARE UNLIKE (B''-tx4's       *)
(*      finding).  C-4 SPLIT THEM.  The inum a walk is CARRYING between an *)
(*      eviction's identity flip and its deposit gets its own key and its  *)
(*      own parked share ([IcacheEscrow.ipool_tkey] /                      *)
(*      [IcacheEscrow.ipool_transit] at the ambient [IcacheRef.icfg_ptrn], *)
(*      grown by [ipool_evict_lend] and shrunk by [ipool_put]), so it is   *)
(*      REFUTED at a commit ([IcacheEscrow.ipool_transit_no_ops]) and the  *)
(*      commit's door is [IcacheEscrow.ipool_quiesce_acc], which hands out *)
(*      B''-join's own three-part row.  What is left in [X] is the         *)
(*      pending/await rows, which stand across arbitrarily many            *)
(*      transactions and can park nothing -- see (F).                      *)
(*                                                                        *)
(*  (B) ALTERNATIVE (d) OF [ic_escrow_body_cover] -- SUPPLIED              *)
(*      (durable-disk B''-tx5).  [ic_slot_cover] has THREE alternatives:   *)
(*      iput's three windows each park a positive share of their           *)
(*      transaction's [ln_tx] element, so an empty authority refutes all   *)
(*      three and no live slot can be bundleless.                          *)
(*                                                                        *)
(*  (C) BLOCK 1 IS OWNED -- SUPPLIED (durable-disk lane C-3a).             *)
(*      [col_hand] wants [FsState.sb_owned]: the superblock's block at     *)
(*      FULL fraction plus its parse.  It is [SbPark.sb_park], a conjunct  *)
(*      of [LogInv.log_ctx] ([sb_parked]), read at this file's own         *)
(*      vocabulary by [FsCollectImg.log_ctx_sb_owned_acc].  The share is   *)
(*      1 and not [DfracDiscarded] on purpose: [sk_own_used] refutes a     *)
(*      node owning block 1 through [blk_owned_ne_full], and a discarded   *)
(*      share does not refute 3/4 ([DfracDiscarded ⋅ DfracOwn (3/4)] is    *)
(*      valid) -- [FsCollectImg.log_ctx_sb_not_owned] is that refutation   *)
(*      at the real park.  [FsCollectImg.img_sb_home] is the geometry      *)
(*      half: block 1 is a home block, so [sk_sb] is satisfied by taking   *)
(*      [fss_sbb S] to be the view's own value there.                      *)
(*      WHAT THE LAW STILL OWES: [log_ctx] has no room for the config's    *)
(*      numbers, so its conjunct closes over the record and a holder of    *)
(*      [log_ctx] alone cannot say the record IS the boot configuration's. *)
(*      The law is assembled where the concrete [sb_park γfs sb] is in     *)
(*      hand (fsinit/initlog, which hold every other invariant too), so    *)
(*      the closure fixes it there; [sb_bmapstart sb] and [sb_size sb]     *)
(*      against the config are the two ties that identification needs.     *)
(*                                                                        *)
(*  (D) A FREE INUM'S ABSTRACT NODE -- SUPPLIED (durable-disk lane C-3c).  *)
(*      The era's [FsState.top_frag] used to ride the pool's MARKER arm    *)
(*      ([IcacheEscrow.ipool_shape_np]) UNTIED, and the region held that   *)
(*      inum's record separately, so at a free inum the commit could prove *)
(*      neither [sk_rec] nor [sk_links].  The fragment now parks WITH the  *)
(*      record, in [InodeRegion.ireg_top_park] -- a conjunct of            *)
(*      [ireg_slot]'s IN arm and of its PENDING arm, i.e. of exactly the   *)
(*      two arms that hold [z |->[γi] d].                                  *)
(*                                                                        *)
(*      THE TIE IS GUARDED BY THE TYPE, and that is what makes it free at  *)
(*      every mover.  At a TYPE-0 record the node is [InodeRegion.         *)
(*      free_node d] outright -- the record is bare, so [FsStateInode.     *)
(*      fn_bare] leaves the entry array and the block map no freedom       *)
(*      ([free_node_of_bare]) -- and at a claim box the fragment rides     *)
(*      UNTIED exactly as it did in the pool.  So [ireg_claim_au], which   *)
(*      retags the record 0 -> [fresh_shape], carries it across with NO    *)
(*      resource move and no [ftopN] open, and [ireg_withdraw] hands it to *)
(*      the fill in the same shape the marker arm used to, leaving         *)
(*      ProofIlock's [ireg_top_retag] untouched.                          *)
(*                                                                        *)
(*      HOW IT GETS BACK TO THE REGION, which was the whole difficulty:    *)
(*      the fragment a free inum needs is the one iput's payload carried,  *)
(*      and the walk gives the pool entry up at +0x94 -- twenty            *)
(*      instructions before the off-lock deposit that writes the type-0    *)
(*      record.  The deposit cannot reach the pool (the itable lock is     *)
(*      long gone) and the +0x94 park cannot reach the deposit; the ONE    *)
(*      thing both open is the per-inum ESCROW.  So the fragment travels   *)
(*      the road the standing freeze already travels -- in at              *)
(*      [EscrowInode.escA_alloc], parked in the EMPTY arm of               *)
(*      [escA_body] (which gains [γfs] for it), out at                     *)
(*      [escA_deposit_acc] -- and [EscrowDeposit.ireg_free_deposit_au]     *)
(*      retags it at the corpse's bare record and parks it region-side.    *)
(*      That mover's two new premises are [↑ftopN] (the retag) and         *)
(*      [InodeRegion.ireg_bare dn'], the latter free at iput because       *)
(*      itrunc has already zeroed the size and the addresses.              *)
(*                                                                        *)
(*      THE ACCESSOR IS [col_free_slot_acc] (section 5 below): the pool's  *)
(*      ordinary row is on its marker arm, which carries                   *)
(*      [InodeRegion.imark], so the region's own marked arm is refuted     *)
(*      ([imark_excl]) and the slot is on the IN arm or the PENDING one -- *)
(*      both of which hold the record fragment AND the park.  It LENDS a   *)
(*      whole [FsStateEra.inode_owned_era] at [free_node d] and takes it   *)
(*      back, because every conclusion this file draws is pure.            *)
(*      [col_bundle_free] is the same reading at [col_bundle]'s own shape. *)
(*      NON-VACUITY AT THE REAL INSTANCE (plan section 7):                 *)
(*      [FsCollectImg.img_col_bundle_free] -- at the mkfs image the bundle *)
(*      comes out at [FsCfgBoot.img_node], the very value                  *)
(*      [InodeRegion.ftop_inv]'s map holds at boot, off conjunct (14)      *)
(*      [FsImg.fs_region_bare] and nothing else.  It is not a corner case: *)
(*      boot stocks EVERY free inum's slot that way ([IcacheBoot.          *)
(*      ireg_alloc], whose image premise family gains [image_bare] and     *)
(*      [image_rec_at]), so the first commit meets it at nearly every inum *)
(*      of the region.                                                     *)
(*                                                                        *)
(*  (E) THE CLAIM BOX -- NOT SUPPLIED (durable-disk C-4's first finding).  *)
(*      ialloc's [InodeRegion.ireg_claim_au] retags a FREE record to a     *)
(*      [InodeRegion.fresh_shape] one, which is a NONZERO type, and the    *)
(*      pool row for that inum stays on its MARKER arm until the iget      *)
(*      inside ialloc takes it.  In that window the region slot is on the  *)
(*      IN arm, so [col_free_slot_acc]'s [di_type d = 0] premise fails and *)
(*      [InodeRegion.ireg_top_park] is on its VACUOUS side: the fragment   *)
(*      it carries is at an ARBITRARY node ([col_claim_box_untied] in      *)
(*      section 5b below is that statement, machine-checked), so neither   *)
(*      [FsDurSnap.sk_rec] nor [sk_links] can be read at the inum.  This   *)
(*      is (D)'s residue at a record type (D) does not reach, and it is    *)
(*      NOT covered by (A): the inum is an ORDINARY pool row, in [O].      *)
(*                                                                        *)
(*  (F) THE CORPSE BEFORE ITS DEPOSIT -- NOT SUPPLIED (durable-disk C-4's  *)
(*      second finding, and it CORRECTS B''-tx5's REMAINS).  "Every [X]    *)
(*      inum's region slot is on [ireg_slot]'s PENDING arm" is true only   *)
(*      AFTER iput's off-lock deposit ([EscrowDeposit.ireg_free_deposit_au *)
(*      ]).  The pool's pending/await row is parked at +0x94 (and the      *)
(*      await row at the free path's eviction), both BEFORE that deposit,  *)
(*      and until it fires the region slot is still on the MARKED sub-arm  *)
(*      -- which holds [InodeRegion.imark] and NO record fragment          *)
(*      ([InodeRegion.ireg_marked_ok] forces a nonzero type there), while  *)
(*      the fragment itself is in the WALK's hand.  So such an inum has no *)
(*      bundle anywhere, exactly as C-3b's [X] residue said, and C-3c's    *)
(*      accessor does not reach it.  The window is inside one transaction  *)
(*      (iput's tail holds a share, durable-disk B''-tx5), so the fix is   *)
(*      B''-tx5's ABI increment once more -- at the MARKED arm's freeze    *)
(*      column, which is ON for exactly that window.                       *)
(*                                                                        *)
(*  NONE of these is visible from inside this file, which is the point of  *)
(*  stating [col_hand] as a named predicate: the collection is CLOSED      *)
(*  (see [col_snap_ok]), and what remains is exactly its suppliers.        *)
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
Require Import EscrowDefs.    (* [reg_full] / [reg_half] / [region_pending] *)
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

  (* the two SPECIFIC readings [sk_blk] and [sk_ind] want, at the very byte
     lists the node's map and entry array name *)
  Lemma col_bundle_data γfs γi (i : Z) (n : fs_node) (k : nat)
      (bs : list (bv 8)) :
    fn_blk n !! k = Some bs ->
    col_bundle γfs γi i n -∗
    ∃ dq : dfrac, blk_owned_q (fs_gamma_L γfs) dq (fn_naddr n k) bs.
  Proof.
    intros Hbs. iIntros "H". iDestruct "H" as (dq inum Hbv Hnv) "H".
    rewrite /inode_owned_era_q.
    iDestruct "H" as "(_ & Hblk & _ & _ & _)".
    iExists dq. rewrite (big_sepM_lookup _ _ k bs Hbs). iExact "Hblk".
  Qed.

  Lemma col_bundle_ind γfs γi (i : Z) (n : fs_node) :
    fn_indb n <> 0 ->
    col_bundle γfs γi i n -∗
    ∃ dq : dfrac,
      blk_owned_q (fs_gamma_L γfs) dq (fn_indb n) (ind_bytes (fn_ent n)).
  Proof.
    intros Hnz. iIntros "H". iDestruct "H" as (dq inum Hbv Hnv) "H".
    rewrite /inode_owned_era_q.
    iDestruct "H" as "(_ & _ & Hind & _ & _)".
    iExists dq. rewrite /ind_owned_q (decide_False _ _ Hnz). iExact "Hind".
  Qed.

  (* ---- 5b. the pure rows of the byte invariant, and [sk_bsz] ---------- *)

  Lemma col_auth_pure γfs Lb C home :
    col_auth γfs Lb C home -∗
    ⌜dom C = home
     /\ (forall b bs, C !! b = Some bs -> length bs = BSIZE)⌝.
  Proof.
    iIntros "(_ & %Hdom & %Hlens & _ & _)". iPureIntro. split; assumption.
  Qed.

  (* every block of the committed view is a whole block: it IS one of [C]'s,
     and the log's own row (b) says those are block-sized *)
  Lemma col_view_len (C : gmap Z (list (bv 8))) (home : gset Z) :
    dom C = home ->
    (forall b bs, C !! b = Some bs -> length bs = BSIZE) ->
    forall b bs, col_view C home !! b = Some bs -> length bs = BSIZE.
  Proof.
    intros Hdom Hlens b bs Hb.
    apply fs_restrict_lookup_Some in Hb as [Hin ->].
    assert (Hc : is_Some (C !! b)) by (apply elem_of_dom; rewrite Hdom; exact Hin).
    destruct Hc as [bs' Hbs']. rewrite /dv_of_D Hbs' /=.
    exact (Hlens b bs' Hbs').
  Qed.

  (* ---- 5c. the free pool covers every clear bit ----------------------- *)

  Lemma col_pool_dom γfs Lb C home (nb : Z) (u : gset Z) :
    col_auth γfs Lb C home -∗
    free_pool (fs_gamma_L γfs) nb u -∗
    ⌜forall b : Z, 0 <= b < nb -> b ∉ u ->
       is_Some (col_view C home !! b)⌝.
  Proof.
    iIntros "Hau Hpool".
    rewrite bi.pure_forall. iIntros (b).
    rewrite bi.pure_impl. iIntros (Hb).
    rewrite bi.pure_impl. iIntros (Hnu).
    assert (Hb' : Z.of_nat (Z.to_nat b) = b) by lia.
    rewrite (free_pool_split (fs_gamma_L γfs) nb u (Z.to_nat b)); [| lia].
    rewrite Hb' {1}/pool_elt (bool_decide_eq_false_2 _ Hnu).
    iDestruct "Hpool" as "[Helt _]". iDestruct "Helt" as (bsx) "Helt".
    iDestruct (col_blk_full with "Hau Helt") as %[_ Hv].
    iPureIntro. exists bsx. exact Hv.
  Qed.

  (* ---- 5d. what a bundle says about ONE inode ------------------------- *)

  Lemma col_bundles_local γfs γi (I : gmap Z fs_node) :
    ([∗ map] i ↦ n ∈ I, col_bundle γfs γi i n) -∗
    ⌜forall i n, I !! i = Some n -> inode_local i n⌝.
  Proof.
    iIntros "Hb".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_impl. iIntros (Hin).
    rewrite (big_sepM_lookup _ _ i n Hin).
    iApply (col_bundle_local with "Hb").
  Qed.

  Lemma col_bundles_slot γfs γi (I : gmap Z fs_node) :
    ([∗ map] i ↦ n ∈ I, col_bundle γfs γi i n) -∗
    ⌜forall i n, I !! i = Some n -> fn_slot_inj n⌝.
  Proof.
    iIntros "Hb".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_impl. iIntros (Hin).
    rewrite (big_sepM_lookup _ _ i n Hin).
    iApply (col_bundle_slot with "Hb").
  Qed.

  Lemma col_bundles_blk γfs Lb C home γi (I : gmap Z fs_node) :
    col_auth γfs Lb C home -∗
    ([∗ map] i ↦ n ∈ I, col_bundle γfs γi i n) -∗
    ⌜forall i n k bs, I !! i = Some n -> fn_blk n !! k = Some bs ->
       col_view C home !! fn_naddr n k = Some bs⌝.
  Proof.
    iIntros "Hau Hb".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_forall. iIntros (k).
    rewrite bi.pure_forall. iIntros (bs).
    rewrite bi.pure_impl. iIntros (Hin).
    rewrite bi.pure_impl. iIntros (Hbs).
    rewrite (big_sepM_lookup _ _ i n Hin).
    iDestruct (col_bundle_data γfs γi i n k bs Hbs with "Hb") as (dq) "Hblk".
    iDestruct (col_blk with "Hau Hblk") as %[_ Hv].
    iPureIntro. exact Hv.
  Qed.

  Lemma col_bundles_ind γfs Lb C home γi (I : gmap Z fs_node) :
    col_auth γfs Lb C home -∗
    ([∗ map] i ↦ n ∈ I, col_bundle γfs γi i n) -∗
    ⌜forall i n, I !! i = Some n -> fn_indb n <> 0 ->
       col_view C home !! fn_indb n = Some (ind_bytes (fn_ent n))⌝.
  Proof.
    iIntros "Hau Hb".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_impl. iIntros (Hin).
    rewrite bi.pure_impl. iIntros (Hnz).
    rewrite (big_sepM_lookup _ _ i n Hin).
    iDestruct (col_bundle_ind γfs γi i n Hnz with "Hb") as (dq) "Hblk".
    iDestruct (col_blk with "Hau Hblk") as %[_ Hv].
    iPureIntro. exact Hv.
  Qed.

  (* ---- 5e. NO TWO NODES SHARE A BLOCK, off the [∗] -------------------- *)

  Lemma col_bundles_disj γfs γi (I : gmap Z fs_node) :
    ([∗ map] i ↦ n ∈ I, col_bundle γfs γi i n) -∗
    ⌜forall i n j n2 b, I !! i = Some n -> I !! j = Some n2 ->
       fn_owns n b -> fn_owns n2 b -> i = j⌝.
  Proof.
    iIntros "Hb".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_forall. iIntros (j).
    rewrite bi.pure_forall. iIntros (n2).
    rewrite bi.pure_forall. iIntros (b).
    rewrite bi.pure_impl. iIntros (Hi).
    rewrite bi.pure_impl. iIntros (Hj).
    rewrite bi.pure_impl. iIntros (Hon).
    rewrite bi.pure_impl. iIntros (Hon2).
    destruct (decide (i = j)) as [-> | Hne]; [by iPureIntro |].
    iExFalso.
    rewrite (big_sepM_delete _ I i n Hi).
    iDestruct "Hb" as "[Hi Hrest]".
    assert (Hj' : delete i I !! j = Some n2)
      by (rewrite lookup_delete_ne; [exact Hj | exact Hne]).
    rewrite (big_sepM_lookup _ _ j n2 Hj').
    iDestruct (col_bundle_owns γfs γi i b n Hon with "Hi")
      as (dq1 bs1 Hnv1) "H1".
    iDestruct (col_bundle_owns γfs γi j b n2 Hon2 with "Hrest")
      as (dq2 bs2 Hnv2) "H2".
    iApply (blk_owned_q_excl (fs_gamma_L γfs) (fs_gamma_L_excl γfs) dq1 dq2
              b bs1 bs2 (dfrac_nvalid_pair dq1 dq2 Hnv1 Hnv2) with "H1 H2").
  Qed.

  (* ---- 5f. a node's own blocks are IN USE and are NOT metadata -------- *)

  Lemma col_bundles_used γfs Lb C home γi (I : gmap Z fs_node)
      (sb : fs_sb) (ist : Z) (nib : nat) (used : gset Z) :
    col_geom sb ist nib home ->
    col_auth γfs Lb C home -∗
    free_pool (fs_gamma_L γfs) (sb_size sb) used -∗
    ([∗ map] i ↦ n ∈ I, col_bundle γfs γi i n) -∗
    ⌜forall i n b, I !! i = Some n -> fn_owns n b -> b ∈ used⌝.
  Proof.
    intros Hg. iIntros "Hau Hpool Hb".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_forall. iIntros (b).
    rewrite bi.pure_impl. iIntros (Hi).
    rewrite bi.pure_impl. iIntros (Hon).
    rewrite (big_sepM_lookup _ _ i n Hi).
    iDestruct (col_bundle_owns γfs γi i b n Hon with "Hb")
      as (dq bs Hnv) "Hblk".
    iApply (col_used_of_blk γfs Lb C home sb used ist nib dq b bs Hg
              with "Hau Hpool Hblk").
  Qed.

  (* THE THREE METADATA ROLES ARE FULL-FRACTION OWNERS, so a node's block --
     held at a share whose double is invalid, hence at more than nothing --
     is none of them.  This is [snap_meta] refuted by the [∗], exactly as
     [sk_disj] is. *)
  Lemma col_bundles_not_meta γfs γi (I : gmap Z fs_node) (m : gmap Z dinode)
      (sb : fs_sb) (sbb : list (bv 8)) (ist : Z) (nib : nat)
      (used : gset Z) (home : gset Z) :
    col_geom sb ist nib home ->
    (forall i : Z, i ∈ dom I <-> 0 <= i < 16 * Z.of_nat nib) ->
    blk_owned (fs_gamma_L γfs) SB_BNO sbb -∗
    blk_owned (fs_gamma_L γfs) (sb_bmapstart sb) (bm_bytes BSIZE used) -∗
    col_recs γfs γi ist nib m -∗
    ([∗ map] i ↦ n ∈ I, col_bundle γfs γi i n) -∗
    ⌜forall i n b, I !! i = Some n -> fn_owns n b ->
       ~ snap_meta (col_state sb sbb I used) b⌝.
  Proof.
    intros Hg Hdi. iIntros "Hsbb Hbmb Hrec Hb".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_forall. iIntros (b).
    rewrite bi.pure_impl. iIntros (Hi).
    rewrite bi.pure_impl. iIntros (Hon).
    rewrite bi.pure_impl. iIntros (Hmeta).
    rewrite (big_sepM_lookup _ _ i n Hi).
    iDestruct (col_bundle_owns γfs γi i b n Hon with "Hb")
      as (dq bs Hnv) "Hblk".
    rewrite /col_state /snap_meta /= in Hmeta.
    destruct Hmeta as [-> | [-> | (z & Hz & ->)]].
    - rewrite blk_owned_1.
      iApply (blk_owned_q_excl (fs_gamma_L γfs) (fs_gamma_L_excl γfs)
                (DfracOwn 1) dq SB_BNO sbb bs (dfrac_full_nvalid dq)
                with "Hsbb Hblk").
    - rewrite blk_owned_1.
      iApply (blk_owned_q_excl (fs_gamma_L γfs) (fs_gamma_L_excl γfs)
                (DfracOwn 1) dq (sb_bmapstart sb) (bm_bytes BSIZE used) bs
                (dfrac_full_nvalid dq) with "Hbmb Hblk").
    - (* a REGION block: the records own it whole *)
      assert (Hzr : 0 <= z < 16 * Z.of_nat nib)
        by (apply Hdi; apply elem_of_dom; exact Hz).
      assert (Hd0 : 0 <= z `div` 16) by (apply Z.div_pos; lia).
      assert (Hdlt : z `div` 16 < Z.of_nat nib)
        by (apply Z.div_lt_upper_bound; lia).
      set (bi := Z.to_nat (z `div` 16)).
      assert (Hbi : (bi < nib)%nat) by (unfold bi; lia).
      assert (Hbiz : Z.of_nat bi = z `div` 16) by (unfold bi; lia).
      iDestruct (col_recs_blk γfs γi ist nib bi m Hbi with "Hrec")
        as (ds Hwf Hcp) "Hrblk".
      rewrite Hbiz (cg_ist Hg) blk_owned_1.
      iApply (blk_owned_q_excl (fs_gamma_L γfs) (fs_gamma_L_excl γfs)
                (DfracOwn 1) dq (ist + z `div` 16) (diblk_bytes ds) bs
                (dfrac_full_nvalid dq) with "Hrblk Hblk").
  Qed.

  (* ...and the same three, IN USE: a clear bit would put a SECOND owner of
     the block into the free pool. *)
  Lemma col_meta_used γfs Lb C home γi (I : gmap Z fs_node)
      (m : gmap Z dinode) (sb : fs_sb) (sbb : list (bv 8))
      (ist : Z) (nib : nat) (used : gset Z) :
    col_geom sb ist nib home ->
    (forall i : Z, i ∈ dom I <-> 0 <= i < 16 * Z.of_nat nib) ->
    col_auth γfs Lb C home -∗
    blk_owned (fs_gamma_L γfs) SB_BNO sbb -∗
    blk_owned (fs_gamma_L γfs) (sb_bmapstart sb) (bm_bytes BSIZE used) -∗
    free_pool (fs_gamma_L γfs) (sb_size sb) used -∗
    col_recs γfs γi ist nib m -∗
    ⌜forall b : Z, snap_meta (col_state sb sbb I used) b -> b ∈ used⌝.
  Proof.
    intros Hg Hdi. iIntros "Hau Hsbb Hbmb Hpool Hrec".
    rewrite bi.pure_forall. iIntros (b).
    rewrite bi.pure_impl. iIntros (Hmeta).
    rewrite /col_state /snap_meta /= in Hmeta.
    destruct Hmeta as [-> | [-> | (z & Hz & ->)]].
    - rewrite blk_owned_1.
      iApply (col_used_of_blk γfs Lb C home sb used ist nib (DfracOwn 1)
                SB_BNO sbb Hg with "Hau Hpool Hsbb").
    - rewrite blk_owned_1.
      iApply (col_used_of_blk γfs Lb C home sb used ist nib (DfracOwn 1)
                (sb_bmapstart sb) (bm_bytes BSIZE used) Hg
                with "Hau Hpool Hbmb").
    - assert (Hzr : 0 <= z < 16 * Z.of_nat nib)
        by (apply Hdi; apply elem_of_dom; exact Hz).
      assert (Hd0 : 0 <= z `div` 16) by (apply Z.div_pos; lia).
      assert (Hdlt : z `div` 16 < Z.of_nat nib)
        by (apply Z.div_lt_upper_bound; lia).
      set (bi := Z.to_nat (z `div` 16)).
      assert (Hbi : (bi < nib)%nat) by (unfold bi; lia).
      assert (Hbiz : Z.of_nat bi = z `div` 16) by (unfold bi; lia).
      iDestruct (col_recs_blk γfs γi ist nib bi m Hbi with "Hrec")
        as (ds Hwf Hcp) "Hrblk".
      rewrite Hbiz (cg_ist Hg) blk_owned_1.
      iApply (col_used_of_blk γfs Lb C home sb used ist nib (DfracOwn 1)
                (ist + z `div` 16) (diblk_bytes ds) Hg
                with "Hau Hpool Hrblk").
  Qed.

  (* ---- 5g. a record sits where the region put it ---------------------- *)

  Lemma col_rec_tie γfs Lb C home γi (I : gmap Z fs_node) (m : gmap Z dinode)
      (sb : fs_sb) (ist : Z) (nib : nat) :
    col_geom sb ist nib home ->
    (forall i : Z, i ∈ dom I <-> 0 <= i < 16 * Z.of_nat nib) ->
    col_auth γfs Lb C home -∗
    col_recs γfs γi ist nib m -∗
    ([∗ map] i ↦ n ∈ I, col_bundle γfs γi i n) -∗
    (* the offsets are spelled at [%Z]: inside a [⌜ ⌝] the ambient scope is
       [type_scope], where [a + b] parses as [sum] (durable-notes.md, the
       scope-stack trap) *)
    ⌜forall i n, I !! i = Some n ->
       exists bs,
         col_view C home !! (sb_inodestart sb + i `div` 16)%Z = Some bs
         /\ rec_in_blk bs (64 * (i `mod` 16))%Z (fn_rec n)⌝.
  Proof.
    intros Hg Hdi. iIntros "Hau Hrec Hb".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_impl. iIntros (Hi).
    (* the record proxy pins the region's value at this inum *)
    iDestruct "Hrec" as "[Hma Hrows]".
    rewrite (big_sepM_lookup _ _ i n Hi).
    iDestruct (col_bundle_rec γfs γi i n m with "Hma Hb") as %Hmi.
    assert (Hir : 0 <= i < 16 * Z.of_nat nib)
      by (apply Hdi; apply elem_of_dom; exists n; exact Hi).
    assert (Hd0 : 0 <= i `div` 16) by (apply Z.div_pos; lia).
    assert (Hdlt : i `div` 16 < Z.of_nat nib)
      by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as [Hm0 Hm1].
    set (bi := Z.to_nat (i `div` 16)).
    assert (Hbi : (bi < nib)%nat) by (unfold bi; lia).
    assert (Hbiz : Z.of_nat bi = i `div` 16) by (unfold bi; lia).
    set (sl := Z.to_nat (i `mod` 16)).
    assert (Hsl : (sl < 16)%nat) by (unfold sl; lia).
    assert (Hslz : Z.of_nat sl = i `mod` 16) by (unfold sl; lia).
    iDestruct (col_recs_blk γfs γi ist nib bi m Hbi with "[Hma Hrows]")
      as (ds Hwf Hcp) "Hrblk".
    { rewrite /col_recs. iSplitL "Hma"; [iExact "Hma" | iExact "Hrows"]. }
    iDestruct (col_blk_full with "Hau Hrblk") as %[_ Hv].
    iPureIntro.
    (* the sixteen records of that block, and this inum's is the [sl]-th *)
    destruct Hwf as [Hlen16 Hall].
    assert (Hkey : (16 * Z.of_nat bi + Z.of_nat sl)%Z = i)
      by (rewrite Hbiz Hslz; pose proof (Z.div_mod i 16 ltac:(lia)); lia).
    pose proof (Hcp sl Hsl) as Hds. rewrite Hkey Hmi in Hds.
    assert (Hrec : ds !!! sl = fn_rec n) by (injection Hds; auto).
    destruct (col_diblk_split ds sl Hall ltac:(lia)) as (pre & post & Heq & Hlp).
    exists (diblk_bytes ds). split.
    - rewrite (cg_ist Hg) -Hbiz. exact Hv.
    - rewrite /rec_in_blk. exists pre, post. split.
      + rewrite Heq Hrec. reflexivity.
      + rewrite Hlp. rewrite -Hslz. lia.
  Qed.

  (* ==================================================================== *)
  (*  6.  THE COLLECTION, AND WHAT THE ALLOCATOR TAKES                     *)
  (* ==================================================================== *)

  Lemma col_snap_bytes γfs γi (ist : Z) (nib : nat) (sb : fs_sb)
      (sbb : list (bv 8)) (used : gset Z) (I : gmap Z fs_node)
      (m : gmap Z dinode) (Lb : gmap Z (bv 8))
      (C : gmap Z (list (bv 8))) (home : gset Z) :
    col_hand γfs γi ist nib sb sbb used I m Lb C home -∗
    ⌜snap_bytes (col_state sb sbb I used) (col_view C home)⌝.
  Proof.
    iIntros "(%Hg & %Hdi & Hau & Hsb & Hbm & Hrec & Hb & Hlk)".
    rewrite /sb_owned. iDestruct "Hsb" as "[Hsbb %Hparse]".
    rewrite /free_bitmap_at. iDestruct "Hbm" as "[Hbmb Hpool]".
    (* ---- the byte agreements ---- *)
    iDestruct (col_auth_pure with "Hau") as %[HdomC Hlens].
    iDestruct (col_blk_full with "Hau Hsbb") as %[_ Hsbv].
    iDestruct (col_blk_full with "Hau Hbmb") as %[_ Hbmv].
    iDestruct (col_pool_dom γfs Lb C home (sb_size sb) used
                 with "Hau Hpool") as %Hpoolv.
    iDestruct (col_rec_tie γfs Lb C home γi I m sb ist nib Hg Hdi
                 with "Hau Hrec Hb") as %Hrecv.
    iDestruct (col_bundles_blk with "Hau Hb") as %Hblkv.
    iDestruct (col_bundles_ind with "Hau Hb") as %Hindv.
    (* ---- the local clauses and the two footprint refutations ---- *)
    iDestruct (col_bundles_local with "Hb") as %Hloc.
    iDestruct (col_bundles_slot with "Hb") as %Hslot.
    iDestruct (col_bundles_disj with "Hb") as %Hdisj.
    iDestruct (col_bundles_used γfs Lb C home γi I sb ist nib used Hg
                 with "Hau Hpool Hb") as %Hused.
    iDestruct (col_bundles_not_meta γfs γi I m sb sbb ist nib used home
                 Hg Hdi with "Hsbb Hbmb Hrec Hb") as %Hnotmeta.
    iDestruct (col_meta_used γfs Lb C home γi I m sb sbb ist nib used
                 Hg Hdi with "Hau Hsbb Hbmb Hpool Hrec") as %Hmetau.
    (* ---- the link family's own validity ---- *)
    iDestruct (fs_links_valid with "Hlk") as %Hlinks.
    iPureIntro.
    split; rewrite /col_state /=.
    - exact (col_view_len C home HdomC Hlens).
    - exact Hsbv.
    - exact Hparse.
    - exact Hbmv.
    - exact Hpoolv.
    - intros i n Hi.
      assert (Hir : 0 <= i < 16 * Z.of_nat nib)
        by (apply Hdi; apply elem_of_dom; exists n; exact Hi).
      pose proof (cg_wide Hg). lia.
    - intros i n Hi. exact (inode_repr_of_local i n (Hloc i n Hi)).
    - exact Hrecv.
    - exact Hblkv.
    - exact Hindv.
    - intros i Hi. apply elem_of_dom. apply Hdi.
      pose proof (cg_nin Hg). lia.
    - exact Hlinks.
    - exact Hmetau.
    - intros i n b Hi Hon.
      split; [exact (Hused i n b Hi Hon) | exact (Hnotmeta i n b Hi Hon)].
    - exact Hdisj.
    - exact (cg_sbok Hg).
    - intros i n Hi.
      assert (Hir : 0 <= i < 16 * Z.of_nat nib)
        by (apply Hdi; apply elem_of_dom; exists n; exact Hi).
      assert (Hdlt : i `div` 16 < Z.of_nat nib)
        by (apply Z.div_lt_upper_bound; lia).
      pose proof (cg_reg Hg). pose proof (cg_ist Hg). lia.
    - exact Hslot.
  Qed.

  (* THE WHOLE OF WHAT [FsDurSnap.fs_snap_alloc] TAKES, and it is the pure
     fact plan section 4 says the commit RECONSTRUCTS.  It moves nothing:
     the caller keeps every piece of [col_hand] and hands it straight back
     to the invariants it borrowed them from. *)
  Lemma col_snap_ok γfs γi (ist : Z) (nib : nat) (sb : fs_sb)
      (sbb : list (bv 8)) (used : gset Z) (I : gmap Z fs_node)
      (m : gmap Z dinode) (Lb : gmap Z (bv 8))
      (C : gmap Z (list (bv 8))) (home : gset Z) :
    col_hand γfs γi ist nib sb sbb used I m Lb C home -∗
    ⌜snap_ok (col_state sb sbb I used) (col_view C home)⌝.
  Proof.
    iIntros "H".
    iDestruct (col_snap_bytes with "H") as %Hbytes.
    iDestruct "H" as "(_ & _ & _ & _ & _ & _ & Hb & _)".
    iDestruct (col_bundles_local with "Hb") as %Hloc.
    iPureIntro. apply snap_ok_intro; [exact Hbytes |].
    rewrite /snap_local /col_state /=. exact Hloc.
  Qed.

  (* ...and the form the commit's law is stated at: the state is not named
     at the call site, only its existence. *)
  Lemma col_snap_ok_ex γfs γi (ist : Z) (nib : nat) (sb : fs_sb)
      (sbb : list (bv 8)) (used : gset Z) (I : gmap Z fs_node)
      (m : gmap Z dinode) (Lb : gmap Z (bv 8))
      (C : gmap Z (list (bv 8))) (home : gset Z) :
    col_hand γfs γi ist nib sb sbb used I m Lb C home -∗
    ⌜exists S : fs_state_rec, snap_ok S (col_view C home)⌝.
  Proof.
    iIntros "H". iDestruct (col_snap_ok with "H") as %Hok.
    iPureIntro. exists (col_state sb sbb I used). exact Hok.
  Qed.

  (* ==================================================================== *)
  (*  5.  A FREE INUM'S BUNDLE -- SUPPLIER (D) (durable-disk lane C-3c)    *)
  (* ==================================================================== *)

  (* THE READING THAT CLOSES (D).  A FREE inum owns no block and no indirect
     block, so [FsStateEra.inode_owned_era]'s two byte legs are [emp]; what
     is left is the record fragment -- which the REGION holds at a free
     record ([InodeRegion.ireg_slot]'s IN arm) -- and the era's abstract
     value, which the region now parks BESIDE it and TIED
     ([InodeRegion.ireg_top_park]).  The tie is the whole content of the
     supplier: without it the fragment is at an unknown node and neither
     [FsDurSnap.sk_rec] nor [sk_links] can be read at a free inum.

     THE SHARE IS 1, which is what [col_bundle]'s [~ ✓ (dq ⋅ dq)] wants: a
     free inum is never locked, so nothing splits its bundle. *)
  Lemma dfrac_full_nvalid : ~ ✓ (DfracOwn 1 ⋅ DfracOwn 1).
  Proof.
    intros Hv. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hv).
  Qed.

  Lemma inode_owned_era_free γfs (γi : gname) (inum : bv 32) (d : dinode) :
    ireg_bare d ->
    bv_unsigned (di_nlink d) = 0 ->
    bv_unsigned (di_type d) = 0 ->
    dinode_at γi inum d -∗
    top_frag (fs_gamma_L γfs) (bv_unsigned inum) (free_node d) -∗
    inode_owned_era γfs γi inum (free_node d).
  Proof.
    intros Hb Hnl Ht0. iIntros "Hdn Htop".
    rewrite /inode_owned_era /free_node /=.
    iSplitL "Hdn"; [iExact "Hdn" |].
    rewrite big_sepM_empty.
    iSplitR; [done |].
    rewrite /ind_owned decide_True; last first.
    { rewrite /fn_indb /= (proj2 Hb) lookup_total_replicate_2;
        [by change (bv_unsigned (bv_0 32)) with 0 | rewrite /FS_NDIRECT; lia]. }
    iSplitR; [done |].
    iSplitL "Htop"; [iExact "Htop" |].
    iPureIntro. exact (inode_local_free_node (bv_unsigned inum) d Hb Hnl Ht0).
  Qed.

  (* ...AND THE COLLECTION'S OWN SHAPE, which is what [col_hand]'s big-op
     wants at every inum of the abstract map. *)
  Lemma col_bundle_free γfs (γi : gname) (inum : bv 32) (d : dinode) :
    ireg_bare d ->
    bv_unsigned (di_nlink d) = 0 ->
    bv_unsigned (di_type d) = 0 ->
    dinode_at γi inum d -∗
    ireg_top_park γfs (bv_unsigned inum) d -∗
    col_bundle γfs γi (bv_unsigned inum) (free_node d).
  Proof.
    intros Hb Hnl Ht0. iIntros "Hdn Hpk".
    iDestruct (ireg_top_park_open γfs (bv_unsigned inum) d Ht0 with "Hpk")
      as "[_ Htop]".
    iExists (DfracOwn 1), inum.
    iSplitR; [done |]. iSplitR; [iPureIntro; exact dfrac_full_nvalid |].
    rewrite -inode_owned_era_1.
    iApply (inode_owned_era_free γfs γi inum d Hb Hnl Ht0 with "Hdn Htop").
  Qed.

  (* THE FREE INUM'S OWN [sk_links] LEG, read off the same two pieces: the
     region's link authority stands at [ireg_nl d], and a free record's count
     is zero ([InodeRegion.ireg_link_ok]'s (L3)), which is exactly
     [fn_nlink (free_node d)]. *)
  Lemma free_node_nlink (d : dinode) :
    bv_unsigned (di_nlink d) = 0 -> fn_nlink (free_node d) = 0%nat.
  Proof. intros Hnl. rewrite /fn_nlink /free_node /= Hnl //. Qed.

  (* ==================================================================== *)
  (*  THE ACCESSOR SUPPLIER (D) IS: one region slot, lent and taken back   *)
  (* ==================================================================== *)

  (* WHAT THE COMMIT HOLDS AT A FREE INUM, and where each half is.  The
     pool's ORDINARY row is on its MARKER arm ([IcacheEscrow.ipool_shape_np]'s
     second alternative), which carries [InodeRegion.imark]; the region's
     slot for that inum therefore cannot be on its own marked arm
     ([InodeRegion.imark_excl]), so it is on the IN arm or the PENDING one --
     and BOTH hold the record fragment and the park.  That is the whole
     supplier: at a type-0 record the two are one [inode_owned_era].

     IT IS AN ACCESSOR AND NOT A MOVE, for this file's own reason: every
     conclusion the collection draws is PURE, so the slot goes back verbatim
     and the region invariant closes with the body it was opened with.  The
     [imark] is only READ (it refutes the marked arm) and comes straight
     back.

     THE SLOT, NOT THE INVARIANT: [InodeRegion.ireg_blks_acc_upd] and
     [ireg_slots_acc_upd] are what open [iregN] down to one slot, and they
     are the commit's business; this lemma is the last step, so [FsCollect]
     stays a LEAF and the [icEscN]/[ipoolN] side never enters its cone. *)
  (* A NESTED SECTION, and it costs the file nothing: [InodeRegion.ireg_slot]
     is stated over the ambient region configuration, so naming it needs
     [IcacheRef.icfg] -- a class the outer section deliberately does not have
     (the arithmetic above is configuration-free).  A nested section puts the
     parameter on these two lemmas alone. *)
  Section FreeSlot.
  Context `{ICFG : icfg}.

  (* ==================================================================== *)
  (*  THE DOOR: ONE REGION SLOT, AT A QUIESCENT TRANSACTION LEDGER         *)
  (*  (durable-disk C-5, and it is what closes residue (E))                *)
  (*                                                                      *)
  (*  [ireg_slot]'s arm says where the inum's RECORD is.  On the MARKED    *)
  (*  sub-arm it is checked out -- to a cache escrow, to the pool's        *)
  (*  allocated bundle, or to a lock holder -- and the collection finds    *)
  (*  the bundle there.  On the IN arm and on the PENDING one the region   *)
  (*  itself holds it, and THIS is the bundle: a free record owns no       *)
  (*  block, so [FsStateEra.inode_owned_era] at [free_node d] is the       *)
  (*  fragment together with [InodeRegion.ireg_top_park]'s tied node.      *)
  (*                                                                      *)
  (*  WHAT THE EMPTY [ln_tx] AUTHORITY BUYS, and it is the whole of        *)
  (*  residue (E): the IN arm ALSO admits a CLAIM BOX -- ialloc's          *)
  (*  [fresh_shape] record, a nonzero type at which the park's tie is on   *)
  (*  its vacuous side ([col_claim_box_untied] below).  A claim box parks  *)
  (*  a positive share of its transaction's element in the slot            *)
  (*  ([InodeRegion.ireg_cpin]), so at a commit the c column reads [None]  *)
  (*  ([InodeRegion.ireg_cpin_no_ops]) and the arm's own clause collapses  *)
  (*  to [di_type d = 0] ([InodeRegion.ireg_in_quiesce]).  So the type is  *)
  (*  a CONCLUSION here, not a premise.                                    *)
  (*                                                                      *)
  (*  The authority is BORROWED and comes straight back, like every other  *)
  (*  reading in this file, and so does the slot: both branches carry      *)
  (*  their own closing wand.                                              *)
  Lemma col_region_slot_acc γfs (γi : gname) (inum : bv 32) (d : dinode) :
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ireg_slot γfs γi (bv_unsigned inum) d -∗
      ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
      ∗ ((imark γi (bv_unsigned inum)
          ∗ (imark γi (bv_unsigned inum)
             -∗ ireg_slot γfs γi (bv_unsigned inum) d))
         ∨ (⌜bv_unsigned (di_type d) = 0⌝
            ∗ inode_owned_era γfs γi inum (free_node d)
            ∗ (inode_owned_era γfs γi inum (free_node d)
               -∗ ireg_slot γfs γi (bv_unsigned inum) d))).
  Proof.
    iIntros "Hauth Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz &
                            %cn & Hla & %Hlok & %Hdir & %Hwl0 & %Hpar &
                            #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp &
                            Harm) [Hep Hlnk]]".
    (* NO CLAIM IS STANDING (durable-disk C-5): a claim box parks a share
       of its transaction's element, and there is no transaction. *)
    iDestruct (ireg_shp_split with "Hfdisj") as "[Hfsh Hcpin]".
    iDestruct (ireg_cpin_no_ops cl fz d Hclm with "Hauth Hcpin") as %Hc0.
    iDestruct (ireg_shp_intro cl fz with "Hfsh Hcpin") as "Hfdisj".
    iFrame "Hauth".
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]".
    - iDestruct "Harm" as "[[%Hin1 [Hfr Hpk]] | [%Ht2 Hmk]]".
      + (* THE IN ARM, unclaimed: a FREE record, and its bundle is here *)
        assert (Ht0 : bv_unsigned (di_type d) = 0)
          by exact (ireg_in_quiesce cl d Hc0 Hin1).
        assert (Hnl : bv_unsigned (di_nlink d) = 0)
          by exact (proj1 (proj2 Hlok) Ht0).
        iDestruct (ireg_top_park_open γfs (bv_unsigned inum) d Ht0 with "Hpk")
          as "[%Hb Htop]".
        iRight. iSplitR; [iPureIntro; exact Ht0 |].
        iSplitL "Hfr Htop".
        { iApply (inode_owned_era_free γfs γi inum d Hb Hnl Ht0
                    with "Hfr Htop"). }
        iIntros "Hown".
        iDestruct "Hown" as "(Hfr & _ & _ & Htop & _)".
        iDestruct (ireg_top_park_free γfs (bv_unsigned inum) d Hb with "Htop")
          as "Hpk".
        iApply (ireg_slot_intro γfs γi (bv_unsigned inum) d wl wdu wdt gl cl
                  rl pl fz cn Hlok Hdir Hwl0 Hpar Hclm Hfrz
                  with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp [Hfr Hpk Hrf]").
        iLeft. iSplitR "Hrf"; [| iExact "Hrf"].
        iLeft. iSplitR; [iPureIntro; exact Hin1 |]. iFrame "Hfr Hpk".
      + (* THE MARKED ARM: the record is checked out, and the collection
           reads this inum's bundle wherever the checkout parked it *)
        iLeft. iFrame "Hmk". iIntros "Hmk".
        iApply (ireg_slot_intro γfs γi (bv_unsigned inum) d wl wdu wdt gl cl
                  rl pl fz cn Hlok Hdir Hwl0 Hpar Hclm Hfrz
                  with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp [Hmk Hrf]").
        iLeft. iSplitR "Hrf"; [| iExact "Hrf"].
        iRight. iSplitR; [iPureIntro; exact Ht2 |]. iExact "Hmk".
    - (* THE PENDING ARM: a freed-but-unrecycled inum, type 0 by its own
         clause, and its bundle is here for (D)'s reason verbatim *)
      iDestruct "Hpend" as "(%Htp & Hfr & Hrh & Hrp & Hpk)".
      assert (Hnl : bv_unsigned (di_nlink d) = 0)
        by exact (proj1 (proj2 Hlok) Htp).
      iDestruct (ireg_top_park_open γfs (bv_unsigned inum) d Htp with "Hpk")
        as "[%Hb Htop]".
      iRight. iSplitR; [iPureIntro; exact Htp |].
      iSplitL "Hfr Htop".
      { iApply (inode_owned_era_free γfs γi inum d Hb Hnl Htp with "Hfr Htop"). }
      iIntros "Hown".
      iDestruct "Hown" as "(Hfr & _ & _ & Htop & _)".
      iDestruct (ireg_top_park_free γfs (bv_unsigned inum) d Hb with "Htop")
        as "Hpk".
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) d wl wdu wdt gl cl
                rl pl fz cn Hlok Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp [Hfr Hrh Hrp Hpk]").
      iRight. iSplitR; [iPureIntro; exact Htp |]. iFrame "Hfr Hrh Hrp Hpk".
  Qed.

  (* ...AND THE MARKER-ARM READING, which is how supplier (D) reaches it:
     the pool's ordinary row carries [InodeRegion.imark], so the region's
     own marked arm is refuted ([imark_excl]) and what is left is the free
     bundle.  THE TYPE PREMISE IS GONE (durable-disk C-5): at a quiescent
     ledger the type is a conclusion, so the caller does not have to know
     in advance that the record it is about to read is free. *)
  Lemma col_free_slot_acc γfs (γi : gname) (inum : bv 32) (d : dinode) :
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    imark γi (bv_unsigned inum) -∗
    ireg_slot γfs γi (bv_unsigned inum) d -∗
      ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
      ∗ ⌜bv_unsigned (di_type d) = 0⌝
      ∗ imark γi (bv_unsigned inum)
      ∗ inode_owned_era γfs γi inum (free_node d)
      ∗ (inode_owned_era γfs γi inum (free_node d) -∗
           ireg_slot γfs γi (bv_unsigned inum) d).
  Proof.
    iIntros "Hauth Hmk Hslot".
    iDestruct (col_region_slot_acc γfs γi inum d with "Hauth Hslot")
      as "[Hauth Harm]".
    iFrame "Hauth".
    iDestruct "Harm" as "[[Hmk' _] | (%Ht0 & Hown & Hback)]".
    { iExFalso. iApply (imark_excl with "Hmk Hmk'"). }
    iSplitR; [iPureIntro; exact Ht0 |]. iFrame "Hmk Hown Hback".
  Qed.

  End FreeSlot.

  (* ...and the collection's own view of what came out.  [col_hand]'s big-op
     wants a [col_bundle] at every inum of the abstract map; at a free one
     this is it, at share 1. *)
  Lemma col_bundle_of_owned γfs (γi : gname) (inum : bv 32) (n : fs_node) :
    inode_owned_era γfs γi inum n -∗ col_bundle γfs γi (bv_unsigned inum) n.
  Proof.
    iIntros "H". iExists (DfracOwn 1), inum.
    iSplitR; [done |]. iSplitR; [iPureIntro; exact dfrac_full_nvalid |].
    rewrite -inode_owned_era_1. iExact "H".
  Qed.

  (* ==================================================================== *)
  (*  5b.  THE CLAIM BOX -- WHY THE TYPE IS A CONCLUSION AND NOT A PREMISE *)
  (*       (durable-disk C-4's residue (E), CLOSED by C-5)                 *)
  (*                                                                      *)
  (*  [col_region_slot_acc] reads a bundle off the region's IN arm at a    *)
  (*  TYPE-0 record.  The IN arm admits one other shape: a CLAIM BOX --    *)
  (*  the [InodeRegion.fresh_shape] record ialloc's [ireg_claim_au] writes *)
  (*  over a free one, which is a NONZERO type by definition.  There the   *)
  (*  park's tie is on its VACUOUS side, so the fragment it carries is at  *)
  (*  an ARBITRARY node and neither [FsDurSnap.sk_rec] nor [sk_links] can  *)
  (*  be read at the inum.  [col_claim_box_untied] is that statement,      *)
  (*  machine-checked, and it is why the window had to be refuted rather   *)
  (*  than reasoned around.                                                *)
  (*                                                                      *)
  (*  IT IS REFUTED AT A COMMIT, and that is C-5's increment.  The claim   *)
  (*  parks a POSITIVE share of its own transaction's [ln_tx] element in   *)
  (*  the slot ([InodeRegion.ireg_cpin], keyed by the c column so the      *)
  (*  claimant's [IcacheRef.iclaim] re-identifies it at the fill), exactly *)
  (*  as [IcacheEscrow.ic_pin_tx] and [ipool_transit] do at the escrow and *)
  (*  the pool.  At an empty authority the column is [None]                *)
  (*  ([InodeRegion.ireg_cpin_no_ops]) and the arm's own clause collapses  *)
  (*  to [di_type d = 0] ([ireg_in_quiesce]).                              *)
  (*  [col_claim_box_no_ops] is the residue closed, end to end.            *)
  (* ==================================================================== *)

  Section ClaimBox.
  Context `{ICFG : icfg}.

  Lemma col_claim_box_untied γfs (z : Z) (d : dinode) (n : fs_node) :
    fresh_shape d ->
    top_frag (fs_gamma_L γfs) z n -∗ ireg_top_park γfs z d.
  Proof.
    intros (Hnz & _ & _ & _). iIntros "Hf".
    iApply (ireg_top_park_nz γfs z d n Hnz with "Hf").
  Qed.

  (* ...AND THE WINDOW ITSELF, REFUTED.  A slot the pool's marker arm
     reaches -- which is every ordinary free row, claim boxes included --
     cannot have a nonzero-typed record while no transaction is open.  This
     is the whole of residue (E): the type premise [col_free_slot_acc] used
     to carry is now its CONCLUSION, so the assembly does not have to know
     in advance which of the region's inums are free. *)
  Lemma col_claim_box_no_ops γfs (γi : gname) (inum : bv 32) (d : dinode) :
    bv_unsigned (di_type d) <> 0 ->
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    imark γi (bv_unsigned inum) -∗
    ireg_slot γfs γi (bv_unsigned inum) d -∗ False.
  Proof.
    intros Hnz. iIntros "Hauth Hmk Hslot".
    iDestruct (col_free_slot_acc γfs γi inum d with "Hauth Hmk Hslot")
      as "(_ & %Ht0 & _)".
    iPureIntro. exact (Hnz Ht0).
  Qed.

  End ClaimBox.

End Collect.
