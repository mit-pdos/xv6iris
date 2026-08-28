(* ====================================================================== *)
(*  FsDurAlloc.v -- THE VALUE-FIRST SNAPSHOT ALLOCATOR, WHICH IS ERA 0'S   *)
(*  AND NOBODY ELSE'S (durable-disk lane H5;                               *)
(*  claude-notes/design/durable-fs-plan.md sections 2, 4 and 5)            *)
(*                                                                        *)
(*  A snapshot is normally MINTED off readings -- the runs' shape, their   *)
(*  pairwise disjointness, the place of their union inside the committed   *)
(*  view -- all of them read off a SOURCE INSTANCE's own resources         *)
(*  ([FsDurXfer.fs_state_xfer_tok]).  Era 0 has no                        *)
(*  source instance: the first file system exists only as BYTES on the     *)
(*  mkfs image.  So exactly one producer in the tree still has to take a   *)
(*  byte MAP and CARVE an [FsState.fs_state] out of it by pure             *)
(*  disjointness facts, and this file is that producer's core.             *)
(*                                                                        *)
(*  THE CARVE IS AN ARTIFACT OF THE INPUT TYPE (plan section 4): a byte    *)
(*  map is ONE linear resource and a file system is a [∗] of many, so      *)
(*  splitting it needs a pure fact saying where the objects are -- which   *)
(*  is why [FsDurSnap.snap_bytes] still carries its used-set coupling      *)
(*  ([sk_own_used], [sk_meta_used], [sk_disj]) and its three cut clauses   *)
(*  ([sk_sbok], [sk_reg], [sk_slot]).  NOTHING ELSE IN THE TREE READS      *)
(*  THEM: at a commit the epoch is minted off the era's own [∗]            *)
(*  ([FsCollectAll.col_bodies_acc]), and at a boot the era's configuration *)
(*  is distributed off the snapshot's own readings.                        *)
(*                                                                        *)
(*  WHAT IS HERE, bottom up:                                               *)
(*    1.  [fp_slot] -- [fs_state]'s pieces NAMED by an index, so a linear  *)
(*        ledger can hand them all out in one step ([fp_disj] is the       *)
(*        pairwise disjointness the cut runs on).                          *)
(*    2.  [blk_ledger] / [ledger_carve] / [blk_ledger_cut] -- the cut      *)
(*        itself, and [fs_state_of_ledger], the Gamma-generic core.        *)
(*    3.  [fs_snap_alloc] / [P_dur_alloc] -- the registry's value-first    *)
(*        entry points.  [fs_snap_alloc] is [P_dur_alloc]'s own step, and  *)
(*        [P_dur_alloc]'s ONE caller is [FsDurImg.img_P_dur_alloc].        *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap numbers dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import BioDefs.
Require Import DiskImg.       (* [diskImgG] -- the byte map's capacity class;
                                 IMPORTED, since [Import] is not transitive
                                 and a backtick binder for a class that is
                                 not in scope silently invents a VARIABLE
                                 (durable-notes.md, typeclass-sweep trap 1) *)
Require Import BitmapEnc.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.
Require Import InodeDefs.
Require Import RiscvModelBytes.
Require Import FsImg.
Require Import LogDefs.       (* [fs_dbytes] -- the byte flattening       *)
Require Import Xv6Cameras.
Require Import FsDurBytes.    (* [fs_dbytes_blocks] -- Gamma-generically;
                                 [snap_gamma] -- the durable family's record.
                                 The TRANSPORT is not required here: this
                                 file names none of it *)
Require Import FsDurRead.     (* [snap_auth] -- the epoch's IDENTITY       *)
Require Import RiscvPtsto.
Require Import FsBlocks.
Require Import FsBytesGamma.
Require Import FsDurSnap.     (* [snap_ok], [fs_snap], [P_dur] -- the
                                 registry this file is the value-first
                                 entry point at *)
(* LAST, so [FsState]'s [fs_view] / [byte_range] / [blk_owned] / [link_auth]
   win over the block layer's twins that arrive transitively through
   [FsDurBytes] -> [RiscvPtsto]; durable-notes.md, AND WHERE THAT IMPORT
   COLLIDES, PUT IT EARLY. *)
Require Export FsState.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  2.  THE FOOTPRINT, SLOT BY SLOT                                       *)
(*                                                                        *)
(*  [FsState.fs_state]'s pieces, NAMED by an index, so that a LINEAR      *)
(*  ledger can hand them all out in one step and the resulting big-op can *)
(*  then be regrouped into the predicate's own shape.  Every slot is ONE  *)
(*  run of bytes; a slot that owns nothing -- a node with no indirect     *)
(*  block, a block whose bit reads allocated -- is the EMPTY run, which   *)
(*  keeps the family total and makes its obligations vacuous there.       *)
(* ===================================================================== *)

Inductive fp_slot :=
| FpSb                        (* the superblock's block                   *)
| FpBmap                      (* the bitmap block                         *)
| FpRec (i : Z)               (* inum [i]'s 64-byte record slot           *)
| FpBlk (i : Z) (k : nat)     (* inode [i]'s data block at slot [k]       *)
| FpInd (i : Z)               (* inode [i]'s indirect block               *)
| FpPool (b : Z).             (* block [b], while its bit reads FREE      *)

(* the byte-address map of the run [bs] at offset [off] of block [b]:
   [FsStateDefs.byte_range]'s flat reading, and the unit the cut works in *)
Definition fp_run (b off : Z) (bs : list (bv 8)) : gmap Z (bv 8) :=
  map_seqZ (b * BSIZE_z + off) bs.

Definition fp_blk (S : fs_state_rec) (x : fp_slot) : Z :=
  match x with
  | FpSb => SB_BNO
  | FpBmap => sb_bmapstart (fss_sb S)
  | FpRec i => sb_inodestart (fss_sb S) + i `div` 16
  | FpBlk i k => fn_naddr (fss_inodes S !!! i) k
  | FpInd i => fn_indb (fss_inodes S !!! i)
  | FpPool b => b
  end.

Definition fp_off (x : fp_slot) : Z :=
  match x with FpRec i => 64 * (i `mod` 16) | _ => 0 end.

Definition fp_bs (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (x : fp_slot) : list (bv 8) :=
  match x with
  | FpSb => fss_sbb S
  | FpBmap => bm_bytes BSIZE (fss_used S)
  | FpRec i => dinode_bytes (fn_rec (fss_inodes S !!! i))
  | FpBlk i k => default [] (fn_blk (fss_inodes S !!! i) !! k)
  | FpInd i => if decide (fn_indb (fss_inodes S !!! i) = 0) then []
               else ind_bytes (fn_ent (fss_inodes S !!! i))
  | FpPool b => if decide (b ∈ fss_used S) then [] else default [] (D !! b)
  end.

Definition fp_map (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (x : fp_slot) : gmap Z (bv 8) :=
  fp_run (fp_blk S x) (fp_off x) (fp_bs S D x).

(* the six slots' three components, READ OUT.  Every one of them is a
   [reflexivity] or one [lookup_total_correct]; they exist so that the
   assembly below rewrites a HYPOTHESIS by a named equation rather than by
   an iota step the proofmode cannot see. *)
Lemma fp_sb_blk (S : fs_state_rec) : fp_blk S FpSb = SB_BNO.
Proof. reflexivity. Qed.
Lemma fp_sb_off : fp_off FpSb = 0.
Proof. reflexivity. Qed.
Lemma fp_sb_bs (S : fs_state_rec) (D : gmap Z (list (bv 8))) :
  fp_bs S D FpSb = fss_sbb S.
Proof. reflexivity. Qed.

Lemma fp_bmap_blk (S : fs_state_rec) :
  fp_blk S FpBmap = sb_bmapstart (fss_sb S).
Proof. reflexivity. Qed.
Lemma fp_bmap_off : fp_off FpBmap = 0.
Proof. reflexivity. Qed.
Lemma fp_bmap_bs (S : fs_state_rec) (D : gmap Z (list (bv 8))) :
  fp_bs S D FpBmap = bm_bytes BSIZE (fss_used S).
Proof. reflexivity. Qed.

Lemma fp_rec_blk (S : fs_state_rec) (i : Z) :
  fp_blk S (FpRec i) = sb_inodestart (fss_sb S) + i `div` 16.
Proof. reflexivity. Qed.
Lemma fp_rec_off (i : Z) : fp_off (FpRec i) = 64 * (i `mod` 16).
Proof. reflexivity. Qed.
Lemma fp_rec_bs (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) :
  fss_inodes S !! i = Some n -> fp_bs S D (FpRec i) = dinode_bytes (fn_rec n).
Proof. intros Hi. rewrite /fp_bs (lookup_total_correct _ _ _ Hi) //. Qed.

Lemma fp_dat_blk (S : fs_state_rec) (i : Z) (n : fs_node) (k : nat) :
  fss_inodes S !! i = Some n -> fp_blk S (FpBlk i k) = fn_naddr n k.
Proof. intros Hi. rewrite /fp_blk (lookup_total_correct _ _ _ Hi) //. Qed.
Lemma fp_dat_off (i : Z) (k : nat) : fp_off (FpBlk i k) = 0.
Proof. reflexivity. Qed.
Lemma fp_dat_bs (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) (k : nat) (bs : list (bv 8)) :
  fss_inodes S !! i = Some n -> fn_blk n !! k = Some bs ->
  fp_bs S D (FpBlk i k) = bs.
Proof.
  intros Hi Hk. rewrite /fp_bs (lookup_total_correct _ _ _ Hi) Hk //.
Qed.

Lemma fp_indb_blk (S : fs_state_rec) (i : Z) (n : fs_node) :
  fss_inodes S !! i = Some n -> fp_blk S (FpInd i) = fn_indb n.
Proof. intros Hi. rewrite /fp_blk (lookup_total_correct _ _ _ Hi) //. Qed.
Lemma fp_indb_off (i : Z) : fp_off (FpInd i) = 0.
Proof. reflexivity. Qed.
Lemma fp_indb_bs (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) :
  fss_inodes S !! i = Some n -> fn_indb n <> 0 ->
  fp_bs S D (FpInd i) = ind_bytes (fn_ent n).
Proof.
  intros Hi Hnz. rewrite /fp_bs (lookup_total_correct _ _ _ Hi).
  destruct (decide (fn_indb n = 0)); [done | reflexivity].
Qed.

Lemma fp_pool_blk (S : fs_state_rec) (b : Z) : fp_blk S (FpPool b) = b.
Proof. reflexivity. Qed.
Lemma fp_pool_off (b : Z) : fp_off (FpPool b) = 0.
Proof. reflexivity. Qed.
Lemma fp_pool_bs_used (S : fs_state_rec) (D : gmap Z (list (bv 8))) (b : Z) :
  b ∈ fss_used S -> fp_bs S D (FpPool b) = [].
Proof.
  intros Hu. rewrite /fp_bs. destruct (decide (b ∈ fss_used S)); [done | tauto].
Qed.
Lemma fp_pool_bs_free (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (b : Z) (bs : list (bv 8)) :
  b ∉ fss_used S -> D !! b = Some bs -> fp_bs S D (FpPool b) = bs.
Proof.
  intros Hu Hb. rewrite /fp_bs.
  destruct (decide (b ∈ fss_used S)); [tauto | rewrite Hb //].
Qed.

(* the index is in range: the only thing the family's members owe *)
Definition fp_valid (S : fs_state_rec) (x : fp_slot) : Prop :=
  match x with
  | FpSb | FpBmap => True
  | FpRec i | FpInd i => is_Some (fss_inodes S !! i)
  | FpBlk i k => is_Some (fss_inodes S !! i)
                 /\ is_Some (fn_blk (fss_inodes S !!! i) !! k)
  | FpPool b => 0 <= b < sb_size (fss_sb S)
  end.

(* ---- 2a.  THE TWO PURE FACTS ABOUT A RUN, and there are only these --- *)

(* a run that IS a slice of a block of [D] is a sub-map of the flattening,
   and it sits inside its own block *)
Lemma fp_run_of_slice (D : gmap Z (list (bv 8))) (b off : Z)
    (bs pre sub post : list (bv 8)) :
  (forall c cs, D !! c = Some cs -> length cs = BSIZE) ->
  D !! b = Some bs -> bs = (pre ++ sub ++ post)%list ->
  Z.of_nat (length pre) = off ->
  fp_run b off sub ⊆ fs_dbytes D
  /\ 0 <= off /\ off + Z.of_nat (length sub) <= BSIZE_z.
Proof.
  intros Hlen Hb Hbs Hoff.
  assert (Hok : dbytes_ok D) by exact (dbytes_ok_full D Hlen).
  assert (Hbl : length bs = BSIZE) by exact (Hlen b bs Hb).
  rewrite Hbs !length_app in Hbl.
  assert (Hst : Z.of_nat BSIZE = BSIZE_z) by reflexivity.
  split; [| split; [lia |]].
  - apply map_subseteq_spec. intros a v Ha.
    rewrite /fp_run in Ha.
    apply lookup_map_seqZ_Some in Ha as [Hge Ha].
    set (j := Z.to_nat (a - (b * BSIZE_z + off))).
    assert (Hj : Z.of_nat j = a - (b * BSIZE_z + off)) by (rewrite /j; lia).
    assert (Hjs : sub !! j = Some v) by exact Ha.
    assert (Hjl : (j < length sub)%nat) by (apply lookup_lt_Some in Hjs; lia).
    assert (Hbsj : bs !! (length pre + j)%nat = Some v).
    { rewrite Hbs lookup_app_r; [| lia].
      replace (length pre + j - length pre)%nat with j by lia.
      rewrite lookup_app_l; [exact Hjs | lia]. }
    pose proof (fs_dbytes_lookup D b bs (length pre + j)%nat v Hok Hb Hbsj) as Hd.
    replace (b * Z.of_nat BSIZE + Z.of_nat (length pre + j)%nat) with a in Hd;
      [exact Hd |].
    rewrite Nat2Z.inj_add. lia.
  - rewrite -Hoff in Hbl *. lia.
Qed.

Lemma fp_run_of_block (D : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8)) :
  (forall c cs, D !! c = Some cs -> length cs = BSIZE) ->
  D !! b = Some bs ->
  fp_run b 0 bs ⊆ fs_dbytes D /\ 0 <= 0 /\ 0 + Z.of_nat (length bs) <= BSIZE_z.
Proof.
  intros Hlen Hb.
  apply (fp_run_of_slice D b 0 bs [] bs []);
    [exact Hlen | exact Hb | rewrite /= app_nil_r // | reflexivity].
Qed.

(* TWO RUNS ARE DISJOINT when they sit in different blocks, or in the same
   block at offsets that do not overlap.  Everything the cut has to know
   about geometry funnels through this one arithmetic step. *)
Lemma fp_run_disj (b1 off1 : Z) (s1 : list (bv 8)) (b2 off2 : Z)
    (s2 : list (bv 8)) :
  0 <= off1 -> off1 + Z.of_nat (length s1) <= BSIZE_z ->
  0 <= off2 -> off2 + Z.of_nat (length s2) <= BSIZE_z ->
  (b1 <> b2 \/ off1 + Z.of_nat (length s1) <= off2
             \/ off2 + Z.of_nat (length s2) <= off1) ->
  fp_run b1 off1 s1 ##ₘ fp_run b2 off2 s2.
Proof.
  intros H1 H2 H3 H4 Hsep. rewrite /fp_run. apply map_seqZ_disjoint.
  change BSIZE_z with 1024 in *.
  destruct Hsep as [Hne | [Hs | Hs]]; [| lia | lia].
  destruct (Z.lt_trichotomy b1 b2) as [Hlt | [Heq | Hlt]].
  - left. assert (1024 <= (b2 - b1) * 1024) by nia. lia.
  - exfalso. exact (Hne Heq).
  - right; left. assert (1024 <= (b1 - b2) * 1024) by nia. lia.
Qed.

(* ---- 2b.  EVERY SLOT IS A GENUINE SLICE ----------------------------- *)

Lemma fp_ok (S : fs_state_rec) (D : gmap Z (list (bv 8))) (x : fp_slot) :
  snap_bytes S D -> fp_valid S x ->
  fp_map S D x ⊆ fs_dbytes D
  /\ 0 <= fp_off x
  /\ fp_off x + Z.of_nat (length (fp_bs S D x)) <= BSIZE_z.
Proof.
  intros Hb Hv.
  assert (Hlen : forall c cs, D !! c = Some cs -> length cs = BSIZE)
    by exact (sk_bsz Hb).
  (* the empty run is a sub-map of anything and occupies nothing *)
  assert (Hnil : forall c : Z, fp_run c 0 [] ⊆ fs_dbytes D
                   /\ 0 <= 0 /\ 0 + Z.of_nat (length (@nil (bv 8))) <= BSIZE_z).
  { intros c. rewrite /fp_run /=. split; [apply map_empty_subseteq |].
    rewrite /BSIZE_z. lia. }
  destruct x as [| | i | i k | i | b]; rewrite /fp_map /fp_bs /fp_blk /fp_off.
  - exact (fp_run_of_block D SB_BNO (fss_sbb S) Hlen (sk_sb Hb)).
  - exact (fp_run_of_block D _ _ Hlen (sk_bmap Hb)).
  - destruct Hv as [n Hn]. rewrite (lookup_total_correct _ _ _ Hn).
    destruct (sk_rec Hb i n Hn) as (bs & Hbs & pre & post & Hsp & Hoff).
    exact (fp_run_of_slice D _ _ bs pre _ post Hlen Hbs Hsp Hoff).
  - destruct Hv as [[n Hn] Hk]. rewrite (lookup_total_correct _ _ _ Hn) in Hk *.
    destruct Hk as [bs Hbs]. rewrite Hbs /=.
    exact (fp_run_of_block D _ bs Hlen (sk_blk Hb i n k bs Hn Hbs)).
  - destruct Hv as [n Hn]. rewrite (lookup_total_correct _ _ _ Hn).
    destruct (decide (fn_indb n = 0)) as [Hz | Hnz]; [exact (Hnil _) |].
    exact (fp_run_of_block D _ _ Hlen (sk_ind Hb i n Hn Hnz)).
  - destruct (decide (b ∈ fss_used S)) as [Hu | Hu]; [exact (Hnil _) |].
    destruct (sk_pool Hb b Hv Hu) as [bs Hbs]. rewrite Hbs /=.
    exact (fp_run_of_block D b bs Hlen Hbs).
Qed.

(* ---- 2c.  ...AND TWO SLOTS ARE DISJOINT ----------------------------- *)

(* the class of a slot: which of the three coupling clauses speaks about
   the block it sits at *)
Definition fp_meta_cls (x : fp_slot) : bool :=
  match x with FpSb | FpBmap | FpRec _ => true | _ => false end.

Lemma fp_meta_of (S : fs_state_rec) (x : fp_slot) :
  fp_valid S x -> fp_meta_cls x = true -> snap_meta S (fp_blk S x).
Proof.
  destruct x as [| | i | i k | i | b]; intros Hv Hc; try discriminate.
  - by left.
  - right. by left.
  - right. right. exists i. split; [exact Hv | reflexivity].
Qed.

Lemma fp_owns_of (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) (k : nat) :
  fss_inodes S !! i = Some n -> is_Some (fn_blk n !! k) ->
  fn_owns n (fp_blk S (FpBlk i k)).
Proof.
  intros Hn Hk. rewrite /fp_blk (lookup_total_correct _ _ _ Hn).
  left. exists k. split; [exact Hk | reflexivity].
Qed.

Lemma fp_owns_ind (S : fs_state_rec) (i : Z) (n : fs_node) :
  fss_inodes S !! i = Some n -> fn_indb n <> 0 ->
  fn_owns n (fp_blk S (FpInd i)).
Proof.
  intros Hn Hnz. rewrite /fp_blk (lookup_total_correct _ _ _ Hn).
  right. split; [exact Hnz | reflexivity].
Qed.

(* a slot the node OWNS is below [FS_MAXFILE] and names a nonzero block:
   the two readings of [inode_repr] a within-node comparison needs *)
Lemma fp_slot_range (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) (k : nat) :
  snap_bytes S D -> fss_inodes S !! i = Some n -> is_Some (fn_blk n !! k) ->
  (k < FS_MAXFILE)%nat /\ fn_naddr n k <> 0.
Proof.
  intros Hb Hn Hk.
  pose proof (sk_repr Hb i n Hn) as Hr.
  assert (Hlt : (k < FS_MAXFILE)%nat).
  { destruct (decide (k < FS_MAXFILE)%nat) as [Hy | Hge]; [exact Hy |].
    destruct Hk as [bs Hbs].
    rewrite (inr_blk_top Hr k ltac:(lia)) in Hbs. discriminate. }
  split; [exact Hlt |]. exact (proj1 (inr_blk_dom Hr k Hlt) Hk).
Qed.

(* a slot that is not a metadata role either belongs to a NODE -- and then
   its block is that node's own -- or is a free-pool slot, and then its
   block's bit reads CLEAR.  Those two arms are what the coupling
   separates from each other and from the metadata roles. *)
Lemma fp_node_of (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (x : fp_slot) :
  fp_valid S x -> fp_bs S D x <> [] ->
  (exists k, x = FpBlk i k) \/ x = FpInd i ->
  exists n, fss_inodes S !! i = Some n /\ fn_owns n (fp_blk S x).
Proof.
  intros Hv H0 [[k ->] | ->].
  - destruct Hv as [[n Hn] Hk]. rewrite (lookup_total_correct _ _ _ Hn) in Hk.
    exists n. split; [exact Hn | exact (fp_owns_of S D i n k Hn Hk)].
  - destruct Hv as [n Hn].
    rewrite /fp_bs (lookup_total_correct _ _ _ Hn) in H0.
    destruct (decide (fn_indb n = 0)) as [Hz | Hnz]; [done |].
    exists n. split; [exact Hn | exact (fp_owns_ind S i n Hn Hnz)].
Qed.

Lemma fp_pool_free (S : fs_state_rec) (D : gmap Z (list (bv 8))) (b : Z) :
  fp_bs S D (FpPool b) <> [] -> b ∉ fss_used S.
Proof.
  rewrite /fp_bs. intros H0.
  destruct (decide (b ∈ fss_used S)) as [Hu | Hu]; [done | exact Hu].
Qed.

(* THE BLOCKS OF TWO DIFFERENT SLOTS DIFFER -- except for two records of
   ONE inode block, which differ by their OFFSET.  This is where every
   coupling clause is spent, and it is the whole content of the cut. *)
Lemma fp_sep (S : fs_state_rec) (D : gmap Z (list (bv 8))) (x y : fp_slot) :
  snap_bytes S D -> fp_valid S x -> fp_valid S y -> x <> y ->
  fp_bs S D x <> [] -> fp_bs S D y <> [] ->
  fp_blk S x <> fp_blk S y
  \/ fp_off x + Z.of_nat (length (fp_bs S D x)) <= fp_off y
  \/ fp_off y + Z.of_nat (length (fp_bs S D y)) <= fp_off x.
Proof.
  intros Hb Hx Hy Hne Hx0 Hy0.
  destruct (fp_meta_cls x) eqn:Hcx; destruct (fp_meta_cls y) eqn:Hcy.
  - (* ================ metadata vs metadata ================ *)
    destruct x as [| | i | | |]; try discriminate;
      destruct y as [| | j | | |]; try discriminate.
    + exfalso. exact (Hne eq_refl).
    + left. exact (snap_sb_bmap_ne S (sk_sbok Hb)).
    + left. destruct Hy as [n Hn]. exact (proj1 (snap_reg_blk S D j n Hb Hn)).
    + left. exact (not_eq_sym (snap_sb_bmap_ne S (sk_sbok Hb))).
    + exfalso. exact (Hne eq_refl).
    + left. destruct Hy as [n Hn]. exact (proj2 (snap_reg_blk S D j n Hb Hn)).
    + left. destruct Hx as [n Hn].
      exact (not_eq_sym (proj1 (snap_reg_blk S D i n Hb Hn))).
    + left. destruct Hx as [n Hn].
      exact (not_eq_sym (proj2 (snap_reg_blk S D i n Hb Hn))).
    + (* TWO RECORDS.  A different inode block, or the same block at two
         of its sixteen slots -- and a record is 64 bytes wide. *)
      destruct Hx as [n Hn]. destruct Hy as [m Hm].
      destruct (decide (i `div` 16 = j `div` 16)) as [Hq | Hq]; last first.
      { left. rewrite /fp_blk. intros Heq. apply Hq. lia. }
      assert (Hmod : i `mod` 16 <> j `mod` 16).
      { intros Hm16. apply Hne. f_equal.
        pose proof (Z.div_mod i 16 ltac:(lia)).
        pose proof (Z.div_mod j 16 ltac:(lia)). lia. }
      rewrite /fp_off /fp_bs.
      rewrite (lookup_total_correct _ _ _ Hn) (lookup_total_correct _ _ _ Hm).
      rewrite (dinode_bytes_length _ (inr_rec_wf (sk_repr Hb i n Hn)))
              (dinode_bytes_length _ (inr_rec_wf (sk_repr Hb j m Hm))).
      pose proof (Z.mod_pos_bound i 16 ltac:(lia)).
      pose proof (Z.mod_pos_bound j 16 ltac:(lia)).
      destruct (Z.lt_trichotomy (i `mod` 16) (j `mod` 16)) as [Hlt | [He | Hlt]].
      * right; left. lia.
      * exfalso. exact (Hmod He).
      * right; right. lia.
  - (* ======== a metadata role vs a node's block or the pool ======== *)
    left. intros Heq.
    pose proof (fp_meta_of S x Hx Hcx) as Hmeta. rewrite Heq in Hmeta.
    destruct y as [| | | j ky | j | c]; try discriminate.
    + destruct (fp_node_of S D j _ Hy Hy0 ltac:(left; by eexists))
        as (m & Hm & Hom).
      exact (proj2 (sk_own_used Hb j m _ Hm Hom) Hmeta).
    + destruct (fp_node_of S D j _ Hy Hy0 ltac:(by right)) as (m & Hm & Hom).
      exact (proj2 (sk_own_used Hb j m _ Hm Hom) Hmeta).
    + exact (fp_pool_free S D c Hy0 (sk_meta_used Hb _ Hmeta)).
  - (* ======== the mirror image ======== *)
    left. intros Heq.
    pose proof (fp_meta_of S y Hy Hcy) as Hmeta. rewrite -Heq in Hmeta.
    destruct x as [| | | j kx | j | c]; try discriminate.
    + destruct (fp_node_of S D j _ Hx Hx0 ltac:(left; by eexists))
        as (m & Hm & Hom).
      exact (proj2 (sk_own_used Hb j m _ Hm Hom) Hmeta).
    + destruct (fp_node_of S D j _ Hx Hx0 ltac:(by right)) as (m & Hm & Hom).
      exact (proj2 (sk_own_used Hb j m _ Hm Hom) Hmeta).
    + exact (fp_pool_free S D c Hx0 (sk_meta_used Hb _ Hmeta)).
  - (* ======== two node/pool slots ======== *)
    left. intros Heq.
    (* the free pool never meets a node's block: [sk_own_used] marks the
       one in use and the other's bit reads clear *)
    assert (Hnp : forall i z c, fp_valid S z -> fp_bs S D z <> [] ->
              ((exists k, z = FpBlk i k) \/ z = FpInd i) ->
              fp_blk S z = c -> c ∉ fss_used S -> False).
    { intros i z c Hv H0 Hs Hc Hu.
      destruct (fp_node_of S D i z Hv H0 Hs) as (n & Hn & Ho).
      rewrite Hc in Ho.
      exact (Hu (proj1 (sk_own_used Hb i n c Hn Ho))). }
    destruct x as [| | | ix kx | ix | bx]; try discriminate;
      destruct y as [| | | iy ky | iy | by0]; try discriminate.
    + (* two data slots *)
      destruct (fp_node_of S D ix _ Hx Hx0 ltac:(left; by eexists))
        as (n & Hn & Hon).
      destruct (fp_node_of S D iy _ Hy Hy0 ltac:(left; by eexists))
        as (m & Hm & Hom).
      rewrite Heq in Hon.
      assert (Hij : ix = iy) by exact (sk_disj Hb ix n iy m _ Hn Hm Hon Hom).
      subst iy. assert (Hnm : m = n) by congruence. subst m.
      destruct Hx as [_ Hkx]. destruct Hy as [_ Hky].
      rewrite (lookup_total_correct _ _ _ Hn) in Hkx.
      rewrite (lookup_total_correct _ _ _ Hn) in Hky.
      destruct (fp_slot_range S D ix n kx Hb Hn Hkx) as [Hrx Hnzx].
      destruct (fp_slot_range S D ix n ky Hb Hn Hky) as [Hry _].
      rewrite /fp_blk !(lookup_total_correct _ _ _ Hn) in Heq.
      exact (fn_slot_data_ne n kx ky (sk_slot Hb ix n Hn) Hrx Hry Hnzx
               ltac:(intros ->; exact (Hne eq_refl)) Heq).
    + (* a data slot and an indirect block *)
      destruct (fp_node_of S D ix _ Hx Hx0 ltac:(left; by eexists))
        as (n & Hn & Hon).
      destruct (fp_node_of S D iy _ Hy Hy0 ltac:(by right)) as (m & Hm & Hom).
      rewrite Heq in Hon.
      assert (Hij : ix = iy) by exact (sk_disj Hb ix n iy m _ Hn Hm Hon Hom).
      subst iy. assert (Hnm : m = n) by congruence. subst m.
      destruct Hx as [_ Hkx]. rewrite (lookup_total_correct _ _ _ Hn) in Hkx.
      destruct (fp_slot_range S D ix n kx Hb Hn Hkx) as [Hrx _].
      rewrite /fp_bs (lookup_total_correct _ _ _ Hn) in Hy0.
      destruct (decide (fn_indb n = 0)) as [Hz | Hnz]; [done |].
      rewrite /fp_blk !(lookup_total_correct _ _ _ Hn) in Heq.
      exact (fn_slot_ind_ne n kx (sk_slot Hb ix n Hn) Hrx Hnz Heq).
    + exact (Hnp ix _ by0 Hx Hx0 ltac:(left; by eexists) Heq
               (fp_pool_free S D by0 Hy0)).
    + (* an indirect block and a data slot *)
      destruct (fp_node_of S D ix _ Hx Hx0 ltac:(by right)) as (n & Hn & Hon).
      destruct (fp_node_of S D iy _ Hy Hy0 ltac:(left; by eexists))
        as (m & Hm & Hom).
      rewrite Heq in Hon.
      assert (Hij : ix = iy) by exact (sk_disj Hb ix n iy m _ Hn Hm Hon Hom).
      subst iy. assert (Hnm : m = n) by congruence. subst m.
      destruct Hy as [_ Hky]. rewrite (lookup_total_correct _ _ _ Hn) in Hky.
      destruct (fp_slot_range S D ix n ky Hb Hn Hky) as [Hry _].
      rewrite /fp_bs (lookup_total_correct _ _ _ Hn) in Hx0.
      destruct (decide (fn_indb n = 0)) as [Hz | Hnz]; [done |].
      rewrite /fp_blk !(lookup_total_correct _ _ _ Hn) in Heq.
      exact (fn_slot_ind_ne n ky (sk_slot Hb ix n Hn) Hry Hnz (eq_sym Heq)).
    + (* one node's indirect block against itself *)
      destruct (fp_node_of S D ix _ Hx Hx0 ltac:(by right)) as (n & Hn & Hon).
      destruct (fp_node_of S D iy _ Hy Hy0 ltac:(by right)) as (m & Hm & Hom).
      rewrite Heq in Hon.
      assert (Hij : ix = iy) by exact (sk_disj Hb ix n iy m _ Hn Hm Hon Hom).
      subst iy. exact (Hne eq_refl).
    + exact (Hnp ix _ by0 Hx Hx0 ltac:(by right) Heq
               (fp_pool_free S D by0 Hy0)).
    + exact (Hnp iy _ bx Hy Hy0 ltac:(left; by eexists) (eq_sym Heq)
               (fp_pool_free S D bx Hx0)).
    + exact (Hnp iy _ bx Hy Hy0 ltac:(by right) (eq_sym Heq)
               (fp_pool_free S D bx Hx0)).
    + (* two pool slots: their block numbers ARE their indices *)
      rewrite /fp_blk in Heq. subst by0. exact (Hne eq_refl).
Qed.

Lemma fp_disj (S : fs_state_rec) (D : gmap Z (list (bv 8))) (x y : fp_slot) :
  snap_bytes S D -> fp_valid S x -> fp_valid S y -> x <> y ->
  fp_map S D x ##ₘ fp_map S D y.
Proof.
  intros Hb Hx Hy Hne.
  destruct (decide (fp_bs S D x = [])) as [Hx0 | Hx0].
  { rewrite /fp_map /fp_run Hx0 /=. apply map_disjoint_empty_l. }
  destruct (decide (fp_bs S D y = [])) as [Hy0 | Hy0].
  { rewrite /fp_map /fp_run Hy0 /=. apply map_disjoint_empty_r. }
  destruct (fp_ok S D x Hb Hx) as (_ & Hx1 & Hx2).
  destruct (fp_ok S D y Hb Hy) as (_ & Hy1 & Hy2).
  rewrite /fp_map. apply (fp_run_disj _ _ _ _ _ _ Hx1 Hx2 Hy1 Hy2).
  exact (fp_sep S D x y Hb Hx Hy Hne Hx0 Hy0).
Qed.

(* ---- 2d.  THE FAMILY, ENUMERATED ------------------------------------ *)

Definition fp_inums (S : fs_state_rec) : list Z :=
  elements (dom (fss_inodes S)).

Definition fp_recs (S : fs_state_rec) : list fp_slot :=
  FpRec <$> fp_inums S.

Definition fp_blks (S : fs_state_rec) : list fp_slot :=
  fp_inums S
    ≫= (fun i => FpBlk i <$> elements (dom (fn_blk (fss_inodes S !!! i)))).

Definition fp_inds (S : fs_state_rec) : list fp_slot :=
  FpInd <$> fp_inums S.

Definition fp_pools (S : fs_state_rec) : list fp_slot :=
  FpPool <$> seqZ 0 (sb_size (fss_sb S)).

Definition fp_list (S : fs_state_rec) : list fp_slot :=
  FpSb :: FpBmap
       :: (fp_recs S ++ fp_blks S ++ fp_inds S ++ fp_pools S).

Lemma fp_inums_elem (S : fs_state_rec) (i : Z) :
  i ∈ fp_inums S <-> is_Some (fss_inodes S !! i).
Proof. rewrite /fp_inums elem_of_elements elem_of_dom //. Qed.

Lemma fp_recs_elem (S : fs_state_rec) (x : fp_slot) :
  x ∈ fp_recs S -> exists i, x = FpRec i /\ is_Some (fss_inodes S !! i).
Proof.
  rewrite /fp_recs. intros (i & -> & Hi)%elem_of_list_fmap.
  exists i. split; [reflexivity | by apply fp_inums_elem].
Qed.

Lemma fp_inds_elem (S : fs_state_rec) (x : fp_slot) :
  x ∈ fp_inds S -> exists i, x = FpInd i /\ is_Some (fss_inodes S !! i).
Proof.
  rewrite /fp_inds. intros (i & -> & Hi)%elem_of_list_fmap.
  exists i. split; [reflexivity | by apply fp_inums_elem].
Qed.

Lemma fp_pools_elem (S : fs_state_rec) (x : fp_slot) :
  x ∈ fp_pools S -> exists b, x = FpPool b /\ 0 <= b < sb_size (fss_sb S).
Proof.
  rewrite /fp_pools. intros (b & -> & Hb)%elem_of_list_fmap.
  apply elem_of_seqZ in Hb. exists b. split; [reflexivity | lia].
Qed.

Lemma fp_blks_elem (S : fs_state_rec) (x : fp_slot) :
  x ∈ fp_blks S ->
  exists i k, x = FpBlk i k /\ is_Some (fss_inodes S !! i)
           /\ is_Some (fn_blk (fss_inodes S !!! i) !! k).
Proof.
  rewrite /fp_blks. intros (i & Hx & Hi)%elem_of_list_bind.
  apply elem_of_list_fmap in Hx as (k & -> & Hk).
  exists i, k. split; [reflexivity |].
  split; [by apply fp_inums_elem |].
  apply elem_of_elements, elem_of_dom in Hk. exact Hk.
Qed.

Lemma fp_list_valid (S : fs_state_rec) (x : fp_slot) :
  x ∈ fp_list S -> fp_valid S x.
Proof.
  rewrite /fp_list. intros Hx0.
  apply elem_of_cons in Hx0 as [-> | Hx0]; [done |].
  apply elem_of_cons in Hx0 as [-> | Hx]; [done |].
  apply elem_of_app in Hx as [Hx | Hx].
  { destruct (fp_recs_elem S x Hx) as (i & -> & Hi). exact Hi. }
  apply elem_of_app in Hx as [Hx | Hx].
  { destruct (fp_blks_elem S x Hx) as (i & k & -> & Hi & Hk). by split. }
  apply elem_of_app in Hx as [Hx | Hx].
  { destruct (fp_inds_elem S x Hx) as (i & -> & Hi). exact Hi. }
  destruct (fp_pools_elem S x Hx) as (b & -> & Hb). exact Hb.
Qed.

(* a fmap by an injective function keeps [NoDup].  Stdlib's own
   [NoDup_fmap_2_strong] leaves the list an EVAR when its [f] is a section
   variable, and the instance search for [elements] then fails on the wrong
   set type; taking [f] explicitly is one induction and no guessing. *)
Lemma NoDup_fmap_inj {A B : Type} (f : A -> B) (l : list A) :
  (forall x y : A, f x = f y -> x = y) -> base.NoDup l -> base.NoDup (f <$> l).
Proof.
  intros Hinj Hnd. induction Hnd as [| x l Hx Hnd IH]; [constructor |].
  rewrite fmap_cons. constructor; [| exact IH].
  intros Hin. apply elem_of_list_fmap in Hin as (y & Hy & Hyl).
  apply Hinj in Hy as ->. exact (Hx Hyl).
Qed.

Lemma fp_list_nodup (S : fs_state_rec) : base.NoDup (fp_list S).
Proof.
  assert (Hins : base.NoDup (fp_inums S)).
  { rewrite /fp_inums. apply (NoDup_elements (dom (fss_inodes S))). }
  assert (HR : base.NoDup (fp_recs S)).
  { rewrite /fp_recs.
    apply (NoDup_fmap_inj FpRec _ ltac:(intros a b H; congruence) Hins). }
  assert (HI : base.NoDup (fp_inds S)).
  { rewrite /fp_inds.
    apply (NoDup_fmap_inj FpInd _ ltac:(intros a b H; congruence) Hins). }
  assert (HP : base.NoDup (fp_pools S)).
  { rewrite /fp_pools.
    apply (NoDup_fmap_inj FpPool _ ltac:(intros a b H; congruence)).
    apply (NoDup_seqZ 0 (sb_size (fss_sb S))). }
  assert (HB : base.NoDup (fp_blks S)).
  { rewrite /fp_blks. apply NoDup_bind.
    - intros i1 i2 y _ _ Hy1 Hy2.
      apply elem_of_list_fmap in Hy1 as (k1 & -> & _).
      apply elem_of_list_fmap in Hy2 as (k2 & Hk & _). congruence.
    - intros i _.
      apply (NoDup_fmap_inj (FpBlk i) _ ltac:(intros a b H; congruence)).
      apply (NoDup_elements (dom (fn_blk (fss_inodes S !!! i)))).
    - exact Hins. }
  rewrite /fp_list. apply NoDup_cons_2.
  { intros Hx0. apply elem_of_cons in Hx0 as [Hx | Hx]; [discriminate |].
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_recs_elem S _ Hx) as (i & Hc & _). discriminate. }
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_blks_elem S _ Hx) as (i & k & Hc & _). discriminate. }
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_inds_elem S _ Hx) as (i & Hc & _). discriminate. }
    destruct (fp_pools_elem S _ Hx) as (b & Hc & _). discriminate. }
  apply NoDup_cons_2.
  { intros Hx.
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_recs_elem S _ Hx) as (i & Hc & _). discriminate. }
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_blks_elem S _ Hx) as (i & k & Hc & _). discriminate. }
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_inds_elem S _ Hx) as (i & Hc & _). discriminate. }
    destruct (fp_pools_elem S _ Hx) as (b & Hc & _). discriminate. }
  apply NoDup_app. split_and!; [exact HR | |].
  { intros x Hx.
    destruct (fp_recs_elem S x Hx) as (i & -> & _). intros Hy.
    apply elem_of_app in Hy as [Hy | Hy].
    { destruct (fp_blks_elem S _ Hy) as (j & k & Hc & _). discriminate. }
    apply elem_of_app in Hy as [Hy | Hy].
    { destruct (fp_inds_elem S _ Hy) as (j & Hc & _). discriminate. }
    destruct (fp_pools_elem S _ Hy) as (b & Hc & _). discriminate. }
  apply NoDup_app. split_and!; [exact HB | |].
  { intros x Hx.
    destruct (fp_blks_elem S x Hx) as (i & k & -> & _ & _). intros Hy.
    apply elem_of_app in Hy as [Hy | Hy].
    { destruct (fp_inds_elem S _ Hy) as (j & Hc & _). discriminate. }
    destruct (fp_pools_elem S _ Hy) as (b & Hc & _). discriminate. }
  apply NoDup_app. split_and!; [exact HI | | exact HP].
  intros x Hx.
  destruct (fp_inds_elem S x Hx) as (i & -> & _). intros Hy.
  destruct (fp_pools_elem S _ Hy) as (b & Hc & _). discriminate.
Qed.

(* ===================================================================== *)
(*  3.  THE BLOCK LEDGER, AND THE CUT                                     *)
(* ===================================================================== *)

Section Ledger.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types S : fs_state_rec.
  Implicit Types D : gmap Z (list (bv 8)).

  Definition blk_ledger Γ D : iProp Σ :=
    ([∗ map] b ↦ bs ∈ D, blk_owned Γ b bs)%I.

  Lemma blk_ledger_lookup Γ D b bs :
    D !! b = Some bs -> blk_ledger Γ D ⊢ blk_owned Γ b bs.
  Proof. intros Hb. rewrite /blk_ledger (big_sepM_lookup _ _ b bs Hb) //. Qed.

  (* a RECORD out of its block: [byte_range_app] twice, keeping the middle *)
  Lemma blk_owned_rec_in Γ b bs off dn :
    rec_in_blk bs off dn ->
    blk_owned Γ b bs ⊢ byte_range Γ b off (dinode_bytes dn).
  Proof.
    intros (pre & post & -> & Hlen).
    rewrite /blk_owned. iIntros "[_ H]".
    rewrite byte_range_app. iDestruct "H" as "[_ H]".
    rewrite Z.add_0_l Hlen.
    rewrite byte_range_app. iDestruct "H" as "[$ _]".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3a.  A RUN OF BYTES IS A SUB-MAP OF THE FLATTENING                 *)
  (* ------------------------------------------------------------------ *)

  Lemma byte_range_run Γ b off bs :
    byte_range Γ b off bs
    ⊣⊢ ([∗ map] a ↦ v ∈ fp_run b off bs, fsΦ Γ (DfracOwn 1) a v).
  Proof.
    rewrite /fp_run big_sepM_map_seqZ_gen /byte_range /byte_range_q //.
  Qed.

  Lemma blk_owned_run Γ b bs :
    length bs = BSIZE ->
    blk_owned Γ b bs
    ⊣⊢ ([∗ map] a ↦ v ∈ fp_run b 0 bs, fsΦ Γ (DfracOwn 1) a v).
  Proof.
    intros Hl. rewrite /blk_owned byte_range_run.
    iSplit.
    - iIntros "[_ H]". iExact "H".
    - iIntros "H". iSplitR; [by iPureIntro | iExact "H"].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3b.  THE CUT                                                       *)
  (*                                                                      *)
  (*  A family of PAIRWISE DISJOINT sub-maps of the byte map is handed     *)
  (*  out SIMULTANEOUSLY; what the family does not cover is dropped (the   *)
  (*  logic is affine, and a ledger may legitimately carry blocks the      *)
  (*  state does not name).  This is the whole of what the linear          *)
  (*  construction needs of the ledger.                                    *)
  (* ------------------------------------------------------------------ *)

  Lemma ledger_carve {A : Type} (Φ : Z -> bv 8 -> iProp Σ)
      (B : gmap Z (bv 8)) (l : list A) (f : A -> gmap Z (bv 8)) :
    base.NoDup l ->
    (forall x, x ∈ l -> f x ⊆ B) ->
    (forall x y, x ∈ l -> y ∈ l -> x <> y -> f x ##ₘ f y) ->
    ([∗ map] a ↦ v ∈ B, Φ a v)
    ⊢ [∗ list] x ∈ l, ([∗ map] a ↦ v ∈ f x, Φ a v).
  Proof.
    revert B. induction l as [| x l IH]; intros B Hnd Hsub Hdisj.
    { rewrite big_sepL_nil. iIntros "_". done. }
    apply NoDup_cons in Hnd as [Hx Hnd].
    assert (Hfx : f x ⊆ B) by (apply Hsub; apply elem_of_cons; by left).
    assert (HB : B = f x ∪ B ∖ f x)
      by (symmetry; exact (map_difference_union (f x) B Hfx)).
    rewrite {1}HB big_sepM_union;
      [| apply map_disjoint_difference_r; reflexivity].
    rewrite big_sepL_cons. iIntros "[$ Hrest]".
    iApply (IH (B ∖ f x) Hnd with "Hrest").
    - intros y Hy. apply map_subseteq_spec. intros a v Hav.
      apply lookup_difference_Some. split.
      + eapply map_subseteq_spec;
          [apply Hsub; apply elem_of_cons; by right | exact Hav].
      + eapply map_disjoint_Some_l; [| exact Hav].
        apply Hdisj; [apply elem_of_cons; by right | apply elem_of_cons; by left |].
        intros ->. exact (Hx Hy).
    - intros y z Hy Hz Hyz.
      apply Hdisj; [apply elem_of_cons; by right | apply elem_of_cons; by right
                   | exact Hyz].
  Qed.

  (* the family's own instance: the footprint's slots, at the flattening *)
  Lemma blk_ledger_cut Γ S D :
    snap_bytes S D ->
    blk_ledger Γ D
    ⊢ [∗ list] x ∈ fp_list S,
        byte_range Γ (fp_blk S x) (fp_off x) (fp_bs S D x).
  Proof.
    intros Hb.
    rewrite /blk_ledger -(fs_dbytes_blocks Γ D (sk_bsz Hb)).
    rewrite (ledger_carve (fsΦ Γ (DfracOwn 1)) (fs_dbytes D) (fp_list S)
               (fp_map S D)
               (fp_list_nodup S)
               (fun x Hx => proj1 (fp_ok S D x Hb (fp_list_valid S x Hx)))
               (fun x y Hx Hy Hne =>
                  fp_disj S D x y Hb (fp_list_valid S x Hx)
                          (fp_list_valid S y Hy) Hne)).
    apply big_sepL_mono. intros k x _. rewrite /fp_map byte_range_run //.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3c.  REGROUPING: a list over the inums IS a big-op over the map     *)
  (* ------------------------------------------------------------------ *)

  Lemma big_sepL_elements_dom {A : Type} (I : gmap Z A) (Ψ : Z -> iProp Σ) :
    ([∗ list] i ∈ elements (dom I), Ψ i) ⊣⊢ ([∗ map] i ↦ _ ∈ I, Ψ i).
  Proof. rewrite -big_sepS_elements -big_sepM_dom //. Qed.

  Lemma big_sepL_elements_dom_nat {A : Type} (m : gmap nat A) (Ψ : nat -> iProp Σ) :
    ([∗ list] k ∈ elements (dom m), Ψ k) ⊣⊢ ([∗ map] k ↦ _ ∈ m, Ψ k).
  Proof. rewrite -big_sepS_elements -big_sepM_dom //. Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE INSTANCE, FROM A LINEAR LEDGER AND THE PURE TIE             *)
  (*                                                                      *)
  (*  Gamma-GENERIC and SOURCE-AGNOSTIC: nothing here knows which          *)
  (*  points-to [fsΦ Γ] is, nor where the ledger came from -- and the      *)
  (*  ledger is SPENT, so the construction applies at an exclusive         *)
  (*  points-to.  That is what makes it serve both the commit's fresh      *)
  (*  snapshot and the boot mint onto the era's own ghosts                 *)
  (*  ([fs_state_of_ledger_era] is the check).                            *)
  (* ------------------------------------------------------------------ *)

  Lemma fs_state_of_ledger Γ S D :
    snap_ok S D ->
    blk_ledger Γ D -∗ fs_links (γlink Γ) (fss_inodes S) -∗
    fs_state Γ (DfracOwn 1) S.
  Proof.
    intros [Hok Hloc]. iIntros "Hled Hlinks".
    iDestruct (blk_ledger_cut Γ S D Hok with "Hled") as "H".
    iEval (rewrite /fp_list /fp_recs /fp_blks /fp_inds /fp_pools /fp_inums
                   !big_sepL_cons !big_sepL_app) in "H".
    iDestruct "H" as "(Hsb & Hbm & Hrec & Hdat & Hind & Hpool)".
    (* ---- the three inode-indexed groups, as big-ops over the map ---- *)
    iEval (rewrite big_sepL_fmap big_sepL_elements_dom) in "Hrec".
    iEval (rewrite big_sepL_bind big_sepL_elements_dom) in "Hdat".
    iEval (rewrite big_sepL_fmap big_sepL_elements_dom) in "Hind".
    iEval (rewrite big_sepL_fmap) in "Hpool".
    (* ---- assemble ---- *)
    rewrite fs_state_1. iSplitL "Hsb"; last iSplitR "Hbm Hpool".
    - (* the superblock *)
      rewrite /sb_owned. iSplitL; [| iPureIntro; exact (sk_parse Hok)].
      iEval (rewrite fp_sb_blk fp_sb_off (fp_sb_bs S D)) in "Hsb".
      rewrite (blk_owned_run Γ SB_BNO (fss_sbb S)
                 (sk_bsz Hok SB_BNO (fss_sbb S) (sk_sb Hok))).
      rewrite -byte_range_run. iExact "Hsb".
    - (* the inodes *)
      rewrite /fs_inodes /inode_owned /inode_phi /inode_ghost.
      iEval (rewrite /fs_links) in "Hlinks".
      iDestruct (big_sepM_sep_2 with "Hrec Hdat") as "Hp".
      iDestruct (big_sepM_sep_2 with "Hp Hind") as "Hp".
      iDestruct (big_sepM_sep_2 with "Hp Hlinks") as "Hp".
      iApply (big_sepM_impl with "Hp").
      iIntros "!#" (i n Hi) "(((Hr & Hd) & Hb) & Hl)".
      iSplitR "Hl".
      + iSplitL "Hr".
        * (* the record *)
          iEval (rewrite fp_rec_blk fp_rec_off (fp_rec_bs S D i n Hi)) in "Hr".
          rewrite (rec_owned_sb Γ (fss_sb S) i (fn_rec n) (sk_inum Hok i n Hi)).
          rewrite /rec_owned_at. iExact "Hr".
        * iSplitL "Hd".
          -- (* the data blocks *)
             iEval (rewrite (lookup_total_correct _ _ _ Hi)
                            big_sepL_fmap big_sepL_elements_dom_nat) in "Hd".
             iApply (big_sepM_impl with "Hd").
             iIntros "!#" (k bs Hk) "Hc".
             iEval (rewrite (fp_dat_blk S i n k Hi) (fp_dat_off i k)
                            (fp_dat_bs S D i n k bs Hi Hk)) in "Hc".
             rewrite (blk_owned_run Γ (fn_naddr n k) bs
                        (sk_bsz Hok _ bs (sk_blk Hok i n k bs Hi Hk))).
             rewrite -byte_range_run. iExact "Hc".
          -- (* the indirect block *)
             rewrite /ind_owned.
             destruct (decide (fn_indb n = 0)) as [Hz | Hnz]; [done |].
             iEval (rewrite (fp_indb_blk S i n Hi) (fp_indb_off i)
                            (fp_indb_bs S D i n Hi Hnz)) in "Hb".
             rewrite (blk_owned_run Γ (fn_indb n) (ind_bytes (fn_ent n))
                        (sk_bsz Hok _ _ (sk_ind Hok i n Hi Hnz))).
             rewrite -byte_range_run. iExact "Hb".
      + iDestruct "Hl" as (DD vv tyf) "[%Hokp Hl]".
        destruct Hokp as (Hv & Hdok & Hxx & Hentok).
        iDestruct (inode_link_scatter with "Hl") as "[Ha Ht]".
        rewrite /inode_ghost. iExists vv.
        iSplitR; [by iPureIntro |]. iFrame "Ha".
        iSplitL "Ht"; [| iPureIntro; exact (Hloc i n Hi)].
        iExists DD. iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iApply (ent_toks_of_at Γ i (fn_dd n) (fn_orphan n) DD
                  (dir_entries n) tyf Hentok with "Ht").
    - (* the bitmap block and the free pool -- and, last, the map's own
         GEOMETRY, which at the image is four projections of [snap_ok]
         ([FsDurSnap.fs_geom_of_ok]) *)
      iSplitL "Hbm Hpool";
        last (iPureIntro; exact (fs_geom_of_ok S D (conj Hok Hloc))).
      rewrite /free_bitmap /free_bitmap_at. iSplitL "Hbm".
      + iEval (rewrite fp_bmap_blk fp_bmap_off (fp_bmap_bs S D)) in "Hbm".
        rewrite (blk_owned_run Γ (sb_bmapstart (fss_sb S))
                   (bm_bytes BSIZE (fss_used S))
                   (sk_bsz Hok _ _ (sk_bmap Hok))).
        rewrite -byte_range_run. iExact "Hbm".
      + rewrite /free_pool.
        iApply (big_sepL_mono with "Hpool"). intros k b Hk.
        apply lookup_seqZ in Hk as [-> Hk].
        rewrite /pool_elt.
        destruct (decide (0 + Z.of_nat k ∈ fss_used S)) as [Hu | Hu].
        * rewrite (bool_decide_eq_true_2 _ Hu).
          rewrite (fp_pool_bs_used S D _ Hu) byte_range_nil //.
        * rewrite (bool_decide_eq_false_2 _ Hu).
          destruct (sk_pool Hok (0 + Z.of_nat k) ltac:(lia) Hu) as [bs Hbs].
          rewrite (fp_pool_blk S (0 + Z.of_nat k)) (fp_pool_off (0 + Z.of_nat k)).
          rewrite (fp_pool_bs_free S D _ bs Hu Hbs).
          iIntros "Hc". iExists bs. rewrite /blk_owned.
          iSplitR; [iPureIntro; exact (sk_bsz Hok _ bs Hbs) | iExact "Hc"].
  Qed.

End Ledger.
(* ===================================================================== *)
(*  4.  THE REGISTRY'S VALUE-FIRST ENTRY POINTS                           *)
(* ===================================================================== *)

Section AllocSnap.
  (* [diskImgG] is the tree's UNIQUE [ghost_mapG Σ Z (bv 8)]; the snapshot's
     byte map is a FRESH gname at that same class. *)
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types S : fs_state_rec.
  Implicit Types D : gmap Z (list (bv 8)).

  (* ------------------------------------------------------------------ *)
  (*  6.  THE ALLOCATOR = THE TRANSPORT                                   *)
  (*                                                                      *)
  (*  All three gname families in ONE update, returned EXISTENTIALLY:     *)
  (*  [own_alloc] cannot target a name, and the landed allocator family   *)
  (*  ([FsState.fs_boot_alloc_at]) already has this shape.  The byte map   *)
  (*  joins it here.                                                      *)
  (* ------------------------------------------------------------------ *)

  Lemma snap_ledger_of_elems g gl gt D :
    (forall b bs, D !! b = Some bs -> length bs = BSIZE) ->
    ([∗ map] a ↦ v ∈ fs_dbytes D, a ↪[g] v)
    ⊢ blk_ledger (snap_gamma g gl gt) D.
  Proof.
    intros Hlen.
    rewrite /blk_ledger -(fs_dbytes_blocks (snap_gamma g gl gt) D Hlen).
    iIntros "H". iExact "H".
  Qed.

  (* the byte map, freshly allocated: the elements come out EXCLUSIVE and
     are handed straight to the cut *)
  Lemma snap_bytes_alloc (B : gmap Z (bv 8)) :
    ⊢ |==> ∃ g : gname,
        ghost_map_auth g 1 B ∗ ([∗ map] a ↦ v ∈ B, a ↪[g] v).
  Proof.
    iMod (ghost_map_alloc B) as (g) "[Ha Hel]".
    iModIntro. iExists g. iFrame.
  Qed.
  (* ------------------------------------------------------------------ *)
  (*  6.  THE VALUE-FIRST ALLOCATOR, WHICH IS THE IMAGE PATH'S            *)
  (*                                                                      *)
  (*  It mints the byte map at [fs_dbytes D] and CARVES the instance out   *)
  (*  of it by [snap_ok]'s disjointness clauses; the identity is then      *)
  (*  [reflexivity].  A caller that HAS a source instance never wants this *)
  (*  -- it wants [P_dur_alloc_xfer], where nothing is carved -- so this   *)
  (*  entry is for the ONE producer with no source instance at all: era 0, *)
  (*  built from the mkfs image ([FsDurImg]).                              *)
  (* ------------------------------------------------------------------ *)
  Theorem fs_snap_alloc S D :
    snap_ok S D ->
    ⊢ |==> ∃ g gl gt : gname,
        fs_snap (snap_gamma g gl gt) g D S.
  Proof.
    intros Hok.
    iMod (snap_bytes_alloc (fs_dbytes D)) as (g) "[Hba Hbe]".
    destruct (sk_links (sk_bytes Hok)) as (fpar & kv & Hpok & Hpv).
    iMod (fs_boot_alloc_root_slack (fss_inodes S) fpar ROOTINO kv Hpok Hpv)
      as (gl gt) "(Hta & Htf & Hlinks & Hkeep)".
    iModIntro. iExists g, gl, gt.
    iDestruct (snap_ledger_of_elems g gl gt D (sk_bsz (sk_bytes Hok)) with "Hbe")
      as "Hled".
    rewrite /fs_snap /snap_auth /top_frag /snap_gamma /=.
    iFrame "Hta Htf".
    iSplitL "Hba";
      [iExists (fs_dbytes D); iFrame "Hba"; iPureIntro; reflexivity |].
    iSplitL "Hled Hlinks".
    { iApply (fs_state_of_ledger (snap_gamma g gl gt) S D Hok with "Hled").
      iExact "Hlinks". }
    iSplitL "Hkeep"; [by iExists kv |].
    iPureIntro. exact (snap_shape_of_ok S D Hok).
  Qed.

  Lemma P_dur_alloc S D : snap_ok S D -> ⊢ |==> P_dur D.
  Proof.
    intros Hok.
    iMod (fs_snap_alloc S D Hok) as (g gl gt) "Hsnap".
    iModIntro. iExists g, gl, gt, S. iExact "Hsnap".
  Qed.
End AllocSnap.
