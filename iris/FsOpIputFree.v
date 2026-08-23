(* FsOpIputFree.v -- durable-disk stage G2 (batch 3): iput's FREE arm, the
   one per-op composition that fileclose, kexit, sys_chdir, sys_unlink and
   ireclaim all invoke when they drop the last reference to an unlinked
   inode.

     void iput(struct inode *ip) {                       (kernel/fs.c)
       int last = (ip->ref == 1 && ip->valid && ip->nlink == 0);
       if (last) { acquiresleep(..); itrunc(ip); ip->valid = 0; .. }
       ip->ref--;
       if (last) ifree(dev, inum);      // dip->type = 0; log_write(bp);
     }

   TWO groups of log_writes reach the log on that arm, both inside ONE
   transaction (every iput() runs between begin_op and end_op): itrunc's
   net is [FsEffTrunc.eff_trunc] (the record zeroed, the inode's blocks'
   bitmap bits cleared) and ifree's is a SECOND re-encode of the same
   inode block with the type cleared.  So the transaction's net BYTE
   picture is the COMPOSITION [eff_iput_free] below, not the fused
   [FsEffFreeInode.eff_free_inode] -- and for a DIRECTORY orphan there is
   NO well-formed view in between (a typed dir of size 0 has lost its
   dots, so W8 fails), which is why the arm cannot be discharged one
   effect at a time.

   THE TWO THEOREMS THIS FILE EXISTS FOR.

   (1) THE FUSION, [eff_iput_free_fuse]: the composed view IS the fused
       one, as FUNCTIONS -- ifree's re-encode overwrites itrunc's record
       in the same block, and its bitmap write re-lays the very bytes
       itrunc left (the truncated record names no blocks, so the second
       clear is a no-op and [bm_bytes] round-trips through
       [fs_bmap_set]).  With it the dir arm needs no wf intermediate, and
       the [type <> T_DIR] side condition of [eff_trunc_wfv] -- which the
       dir arm could never discharge -- never has to be met.

   (2) THE ORPHAN CHARACTERISATION, [fs_orphan_char]: at a well-formed
       view a LIVE inode has [nlink = 0] exactly when it is UNREACHABLE.
       This is the precondition transport of the whole free side.
       [eff_free_inode_wfv] asks for UNREACHABILITY, which no xv6 code
       path ever computes; what the code tests is [ip->nlink == 0]
       (iput's [last], ireclaim's scan) and what an unlink arm carries
       forward is a DECREMENTED nlink.  W9 ([FsWf.fs_links_gen]) is what
       ties the two, in both directions:
         nlink = 0 -> unreachable   -- a reachable non-root inum has an
              in-edge from a reachable dir, whose record is a ticket, so
              its count -- hence its nlink -- is at least one;
         unreachable -> nlink = 0   -- [FsEffBase.rtick_unreachable], plus
              "the root is reachable" for the root's extra link.
       Both are stated at the view level, so every free-side arm can pass
       its OWN decode-level fact and get the other for free.

   Nothing here is Iris and nothing here mentions [log_state]: these are
   the standalone per-op lemmas of worklist item G2, batch (3).           *)

From Stdlib Require Import ZArith Lia List FunctionalExtensionality.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import BioDefs.
Require Import DinodeEnc.
Require Import BitmapEnc.
Require Import DirView.
Require Import FsTree.
Require Import FsImg.
Require Import FsWf.
Require Import FsEffBase.
Require Import FsEffTrunc.
Require Import FsEffFreeInode.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE BYTE-LEVEL PLUMBING THE FUSION RUNS ON                         *)
(* ====================================================================== *)

Lemma fs_upd_upd (P : Z -> list (bv 8)) (b : Z) (bs bs' : list (bv 8)) :
  fs_upd (fs_upd P b bs) b bs' = fs_upd P b bs'.
Proof.
  apply functional_extensionality. intros c. unfold fs_upd.
  destruct (decide (c = b)); reflexivity.
Qed.

(* the bitmap encoder's round trip, in the direction [fs_bmap_set] does
   not already have ([FsImg.bm_bytes_fs_bmap_set] is the other one): a
   SET the encoder laid down reads back as itself, provided it holds no
   bit outside the block. *)
Lemma fs_bmap_set_bm_bytes (n : nat) (S : gset Z) :
  (forall b : Z, b ∈ S -> 0 <= b < 8 * Z.of_nat n) ->
  fs_bmap_set n (bm_bytes n S) = S.
Proof.
  intros Hrng. apply set_eq. intros b. rewrite fs_bmap_set_elem. split.
  - intros [Hb Hbit]. rewrite (fs_bit_bm_bytes n S b Hb) in Hbit.
    apply bool_decide_eq_true_1 in Hbit. exact Hbit.
  - intros Hb. pose proof (Hrng b Hb) as Hr. split; [exact Hr |].
    rewrite (fs_bit_bm_bytes n S b Hr).
    apply bool_decide_eq_true_2. exact Hb.
Qed.

Lemma fs_bmap_set_diff_range (n : nat) (bs : list (bv 8)) (S : gset Z)
    (b : Z) :
  b ∈ fs_bmap_set n bs ∖ S -> 0 <= b < 8 * Z.of_nat n.
Proof.
  intros Hb. apply elem_of_difference in Hb as [Hb _].
  destruct (proj1 (fs_bmap_set_elem n bs b) Hb) as [Hr _]. exact Hr.
Qed.

(* every slot of [i]'s inode block lies in the region and shares [i]'s
   block -- the two side conditions each [fs_iblk] step asks for *)
Lemma iblk_slot_range (sb : fs_sb) (i : Z) (s : nat) :
  0 <= i < 16 * (sb_ninodes sb / 16 + 1) -> (s < 16)%nat ->
  0 <= 16 * (i / 16) + Z.of_nat s < 16 * (sb_ninodes sb / 16 + 1)
  /\ (16 * (i / 16) + Z.of_nat s) / 16 = i / 16.
Proof.
  intros Hi Hs.
  assert (Hd0 : 0 <= i / 16) by (apply Z.div_pos; lia).
  assert (Hd1 : i / 16 < sb_ninodes sb / 16 + 1)
    by (apply Z.div_lt_upper_bound; lia).
  split; [lia |].
  rewrite (Z.mul_comm 16 (i / 16)).
  rewrite Z.div_add_l by lia.
  rewrite (Z.div_small (Z.of_nat s) 16) by lia. lia.
Qed.

Lemma fs_iblk_upd (P : Z -> list (bv 8)) (sb : fs_sb) (i b : Z)
    (bs : list (bv 8)) :
  fs_sb_ok sb -> 0 <= i < 16 * (sb_ninodes sb / 16 + 1) ->
  b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
  fs_iblk (fs_upd P b bs) sb i = fs_iblk P sb i.
Proof.
  intros Hok Hi Hb. unfold fs_iblk.
  apply list_fmap_ext. intros q x Hx.
  apply elem_of_list_lookup_2, elem_of_seq in Hx.
  destruct (iblk_slot_range sb i x Hi ltac:(lia)) as (Hjr & Hjd).
  apply fs_dinode_ext.
  rewrite (proj2 (iblock_eq_iff sb Hok i (16 * (i / 16) + Z.of_nat x)
                    Hi Hjr) Hjd).
  apply fs_upd_ne. intros Hc. exact (Hb (eq_sym Hc)).
Qed.

(* THE RE-ENCODE, READ BACK: the block [eff_dinode] lays down decodes to
   the very list it encoded.  (The effect writes [diblk_bytes] of an
   insert; this says the sixteen records of the WRITTEN block are that
   insert.) *)
Lemma fs_iblk_eff_dinode (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (dn' : dinode) :
  fs_sb_ok sb -> 0 <= i < 16 * (sb_ninodes sb / 16 + 1) -> dinode_wf dn' ->
  fs_iblk (eff_dinode P sb i dn') sb i
  = <[islot (fs_inum_bv i) := dn']> (fs_iblk P sb i).
Proof.
  intros Hok Hi Hwf.
  assert (Hlen : length (fs_iblk P sb i) = 16%nat)
    by (unfold fs_iblk; rewrite length_fmap, length_seq; reflexivity).
  apply list_eq. intros s.
  destruct (Nat.lt_ge_cases s 16) as [Hs | Hs].
  - assert (HL : forall Q : Z -> list (bv 8),
              fs_iblk Q sb i !! s
              = Some (fs_dinode Q sb (16 * (i / 16) + Z.of_nat s))).
    { intros Q. unfold fs_iblk. rewrite list_lookup_fmap.
      rewrite lookup_seq_lt by exact Hs. reflexivity. }
    rewrite (HL (eff_dinode P sb i dn')).
    destruct (iblk_slot_range sb i s Hi Hs) as (Hjr & _).
    rewrite (eff_dinode_dec sb Hok P i dn' _ Hwf Hi Hjr).
    pose proof (Z.div_mod i 16 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as Hmb.
    rewrite (islot_of sb Hok i Hi).
    destruct (decide (16 * (i / 16) + Z.of_nat s = i)) as [Hji | Hji].
    + assert (Hse : s = Z.to_nat (i `mod` 16)) by lia.
      rewrite Hse, list_lookup_insert by lia. reflexivity.
    + rewrite list_lookup_insert_ne by lia. exact (eq_sym (HL P)).
  - rewrite lookup_ge_None_2
      by (unfold fs_iblk; rewrite length_fmap, length_seq; lia).
    rewrite lookup_ge_None_2 by (rewrite length_insert; lia). reflexivity.
Qed.

(* ====================================================================== *)
(*  2.  THE PREDECESSOR OF A REACHABLE NODE                                *)
(*                                                                         *)
(*  [FsEffBase.rch_no_in] is "no in-edge means unreachable"; this is its    *)
(*  converse, and it is what turns REACHABILITY into a TICKET.  The         *)
(*  predecessor is taken at the walk's FIRST ARRIVAL at [z], so it is       *)
(*  distinct from [z] -- which matters, because a directory's own "."       *)
(*  record bears no ticket.                                                 *)
(* ====================================================================== *)

Lemma rch_pred (t : fstree) (r z : Z) :
  rch t r z -> z <> r ->
  exists (j : Z) (f : fname),
    rch t r j /\ j <> z /\ tree_ent t j f = Some z.
Proof.
  intros (p & Hp) Hzr.
  assert (Hgen : forall (q : list fname) (s : Z),
            path_at t s q = Some z -> rch t r s -> s <> z ->
            exists (j : Z) (f : fname),
              rch t r j /\ j <> z /\ tree_ent t j f = Some z).
  { induction q as [| f q IH]; intros s Hq Hs Hsz.
    - rewrite path_at_nil in Hq. injection Hq as Hq.
      exfalso. exact (Hsz Hq).
    - rewrite path_at_cons in Hq.
      destruct (tree_ent t s f) as [m |] eqn:He; [| discriminate].
      destruct (decide (m = z)) as [-> | Hmz].
      + exists s, f. split; [exact Hs | split; [exact Hsz | exact He]].
      + apply (IH m Hq); [exact (rch_snoc t r s f m Hs He) | exact Hmz]. }
  exact (Hgen p r Hp (rch_refl t r) (fun Hc => Hzr (eq_sym Hc))).
Qed.

(* ====================================================================== *)
(*  3.  THE FUSION                                                         *)
(* ====================================================================== *)

(* the LITERAL net of iput's free arm: itrunc's writes, then ifree's *)
Definition eff_iput_free (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
  : Z -> list (bv 8) :=
  eff_free_inode (eff_trunc P sb i) sb i.

Lemma eff_iput_free_fuse (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_sb_ok sb -> 0 <= i < 16 * (sb_ninodes sb / 16 + 1) ->
  eff_iput_free P sb i = eff_free_inode P sb i.
Proof.
  intros Hok Hi.
  destruct (iblock_bounds sb Hok i Hi) as (Hib1 & _ & Hib3).
  set (IB := IBLOCK (fs_inum_bv i) (sb_inodestart sb)) in *.
  set (BM := sb_bmapstart sb) in *.
  assert (HIBM : IB <> BM) by lia.
  set (dn := fs_dinode P sb i).
  set (T := di_trunc_v dn).
  set (P1 := eff_trunc P sb i).
  assert (HTwf : dinode_wf T) by (apply di_trunc_v_wf).
  (* the intermediate view, block by block *)
  assert (HP1BM : P1 BM
                  = bm_bytes BSIZE
                      (fs_bmap_set BSIZE (P BM)
                       ∖ list_to_set (fs_inode_blocks P dn))).
  { unfold P1, eff_trunc. apply fs_upd_at. }
  assert (HP1out : forall c : Z, c <> BM -> P1 c = eff_dinode P sb i T c).
  { intros c Hc. unfold P1, eff_trunc. apply fs_upd_ne. exact Hc. }
  assert (Hdin1 : fs_dinode P1 sb i = T).
  { rewrite (fs_dinode_ext (eff_dinode P sb i T) P1 sb i
               (HP1out IB HIBM)).
    rewrite (eff_dinode_dec sb Hok P i T i HTwf Hi Hi).
    rewrite decide_True by reflexivity. reflexivity. }
  assert (Hiblk1 : fs_iblk P1 sb i
                   = <[islot (fs_inum_bv i) := T]> (fs_iblk P sb i)).
  { unfold P1, eff_trunc.
    rewrite (fs_iblk_upd (eff_dinode P sb i T) sb i BM _ Hok Hi
               ltac:(lia)).
    exact (fs_iblk_eff_dinode P sb i T Hok Hi HTwf). }
  assert (Hblk1 : fs_inode_blocks P1 (fs_dinode P1 sb i) = []).
  { rewrite Hdin1. unfold fs_inode_blocks. cbv zeta. reflexivity. }
  assert (Hbm1 : fs_bmap_set BSIZE (P1 BM)
                 = fs_bmap_set BSIZE (P BM)
                   ∖ list_to_set (fs_inode_blocks P dn)).
  { rewrite HP1BM. apply fs_bmap_set_bm_bytes.
    intros b Hb. exact (fs_bmap_set_diff_range BSIZE (P BM) _ b Hb). }
  assert (Hfree1 : di_free_v (fs_dinode P1 sb i) = di_free_v dn)
    by (rewrite Hdin1; reflexivity).
  apply functional_extensionality. intros c.
  unfold eff_iput_free, eff_free_inode. fold P1. fold BM. fold dn.
  destruct (decide (c = BM)) as [-> | HcBM].
  - rewrite !fs_upd_at. rewrite Hblk1, Hbm1.
    rewrite list_to_set_nil, difference_empty_L. reflexivity.
  - rewrite !fs_upd_ne by exact HcBM.
    rewrite Hfree1.
    destruct (decide (c = IB)) as [-> | HcIB].
    + unfold eff_dinode. rewrite !fs_upd_at.
      rewrite Hiblk1, list_insert_insert. reflexivity.
    + rewrite (eff_dinode_out sb P1 i (di_free_v dn) c HcIB).
      rewrite (eff_dinode_out sb P i (di_free_v dn) c HcIB).
      rewrite (HP1out c HcBM).
      exact (eff_dinode_out sb P i T c HcIB).
Qed.

(* ====================================================================== *)
(*  4.  THE ORPHAN CHARACTERISATION (in the sweeps' own context)           *)
(* ====================================================================== *)

Section Orphan.
  Context (P : Z -> list (bv 8)) (sb : fs_sb).
  Context (Hp : fs_parse_sb P = Some sb).
  Context (Hsb : fs_sb_wf sb = true).
  Context (HW3 : fs_inodes_dwf P sb = true).
  Context (u : gset Z) (Hu : fs_used_set P sb = Some u).
  Context (Hbm : fs_bitmap_wf P sb u = true).
  Context (HW7 : fs_root_wf P sb = true).
  Context (HW8 : fs_dots_all P sb = true).
  Context (nib : nat) (Hnibz : Z.of_nat nib = sb_ninodes sb / 16 + 1).
  Context (Hreg : fs_region_wf P sb nib = true).
  Context (rd : gset Z) (Hrd : fs_rdirs P sb rd).
  Context (Hdok : forall z : Z, z ∈ rd ->
              fs_dir_ok P sb z (fs_dinode P sb z)).
  Context (Hlkg : fs_links_gen P sb rd).
  Context (Horph : fs_orphans_empty P sb rd).

  Set Default Proof Using "All".

  Let t : fstree := tree_of_disk P sb.

  Local Notation rd_iff := (rd_iff P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation rtick_of_record := (rtick_of_record P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation rtick_unreachable := (rtick_unreachable P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation tree_ent_char := (tree_ent_char P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).

  (* the hard direction: W9 makes a reachable inum's [nlink] positive *)
  Lemma nlink0_unreachable (i : Z) :
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    bv_unsigned (di_nlink (fs_dinode P sb i)) = 0 ->
    ~ fs_reachable P sb i.
  Proof.
    intros Hi Hlive Hnl Hre.
    pose proof (Hlkg i Hi Hlive) as Hlk. cbv zeta in Hlk.
    destruct (decide (i = ROOTINO)) as [-> | Hir].
    - (* the root's own extra link is the contradiction *)
      pose proof (fs_root_wf_type P sb HW7) as Hrt.
      rewrite (bool_decide_eq_true_2
                 (bv_unsigned (di_type (fs_dinode P sb ROOTINO)) = T_DIR_z)
                 Hrt) in Hlk.
      rewrite (bool_decide_eq_true_2 (ROOTINO = ROOTINO) eq_refl) in Hlk.
      lia.
    - assert (Hrch : rch t ROOTINO i) by exact Hre.
      destruct (rch_pred t ROOTINO i Hrch Hir) as (j & f & Hj & Hji & Hedge).
      apply (tree_ent_char P j f i) in Hedge as (Hjr & Hjty & Hlook).
      assert (Hjrd : j ∈ rd)
        by (apply rd_iff; split; [exact Hjr | split; [exact Hjty | exact Hj]]).
      destruct (dir_view_lookup_rec _ _ f i Hlook) as (k & Hk & Hlv & _ & Hin).
      assert (Hself : bv_unsigned (dir_inum (fs_file_data P sb j) k) <> j)
        by (rewrite Hin; intros ->; exact (Hji eq_refl)).
      pose proof (rtick_of_record j k Hjrd Hk Hlv Hself) as Htick.
      rewrite Hin in Htick.
      destruct (bool_decide
                  (bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z));
        [destruct (bool_decide (i = ROOTINO)) |]; lia.
  Qed.

  (* the easy direction, and the one the effect files' [eff_free_inode]
     precondition is stated in *)
  Lemma unreachable_nlink0 (i : Z) :
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    ~ fs_reachable P sb i ->
    bv_unsigned (di_nlink (fs_dinode P sb i)) = 0.
  Proof.
    intros Hi Hlive Hun.
    pose proof (Hlkg i Hi Hlive) as Hlk. cbv zeta in Hlk.
    rewrite (rtick_unreachable i Hun) in Hlk.
    destruct (decide (i = ROOTINO)) as [-> | Hir].
    - exfalso. apply Hun. exists []. apply path_at_nil.
    - rewrite (bool_decide_eq_false_2 (i = ROOTINO) Hir) in Hlk.
      destruct (bool_decide
                  (bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z));
        cbn [fs_tick_count] in Hlk; lia.
  Qed.

End Orphan.

(* ====================================================================== *)
(*  5.  THE VIEW-LEVEL FAMILY -- WHAT A FREE-SIDE ARM CITES                *)
(* ====================================================================== *)

(* the projection every wrapper below opens with (the region bound is
   [FsEffBase.iblk_z_range], hypothesis-free) *)
Lemma fs_wf_view_sb_ok (P : Z -> list (bv 8)) (sb : fs_sb) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb -> fs_sb_ok sb.
Proof.
  intros (sb0 & Hp0 & Hsw) Hp.
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  exact (fs_sb_wf_ok sb (fdw_sb P sb Hsw)).
Qed.

(* ORPHAN <-> nlink 0, at the view.  This is the transport the whole free
   side runs on: xv6 tests [nlink == 0]; the effect files ask for
   unreachability. *)
Lemma fs_orphan_unreachable (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  bv_unsigned (di_nlink (fs_dinode P sb i)) = 0 ->
  ~ fs_reachable P sb i.
Proof.
  intros Hv Hp. intros.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  apply (nlink0_unreachable P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph); assumption.
Qed.

Lemma fs_orphan_nlink0 (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  ~ fs_reachable P sb i ->
  bv_unsigned (di_nlink (fs_dinode P sb i)) = 0.
Proof.
  intros Hv Hp. intros.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  apply (unreachable_nlink0 P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph); assumption.
Qed.

Lemma fs_orphan_char (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  (bv_unsigned (di_nlink (fs_dinode P sb i)) = 0 <-> ~ fs_reachable P sb i).
Proof.
  intros Hv Hp Hi Hlive. split.
  - exact (fs_orphan_unreachable P sb i Hv Hp Hi Hlive).
  - exact (fs_orphan_nlink0 P sb i Hv Hp Hi Hlive).
Qed.

(* ---- the free arm itself --------------------------------------------- *)

(* iput's FREE arm, at its literal two-group net.  The preconditions are
   exactly what the arm holds when it takes the branch: the inode is in
   the region, LIVE on disk, and its [nlink] is the zero the [last] test
   read. *)
Lemma op_iput_free_wfv (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  bv_unsigned (di_nlink (fs_dinode P sb i)) = 0 ->
  fs_durable_wf_view (eff_iput_free P sb i).
Proof.
  intros Hv Hp Hi Hlive Hnl.
  rewrite (eff_iput_free_fuse P sb i (fs_wf_view_sb_ok P sb Hv Hp)
             (iblk_z_range sb i Hi)).
  apply (eff_free_inode_wfv P sb i Hv Hp Hi Hlive).
  exact (fs_orphan_unreachable P sb i Hv Hp Hi Hlive Hnl).
Qed.

(* the same arm at the FUSED spelling, for a caller that has already
   collapsed the two log_write groups *)
Lemma op_iput_free_fused_wfv (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  bv_unsigned (di_nlink (fs_dinode P sb i)) = 0 ->
  fs_durable_wf_view (eff_free_inode P sb i).
Proof.
  intros Hv Hp Hi Hlive Hnl.
  apply (eff_free_inode_wfv P sb i Hv Hp Hi Hlive).
  exact (fs_orphan_unreachable P sb i Hv Hp Hi Hlive Hnl).
Qed.

(* THE NON-FREE ARMS OF iput ([ref > 1], or [!valid], or [nlink <> 0]) --
   and the whole of fileclose's / kexit's / sys_chdir's read-only paths --
   write NOTHING to the log, so their transaction's net is the identity on
   the committed view and the obligation is discharged by the invariant
   the arm already holds.  Stated so an arm can cite a name rather than
   leave a comment. *)
Lemma op_iput_keep_wfv (P : Z -> list (bv 8)) :
  fs_durable_wf_view P -> fs_durable_wf_view P.
Proof. exact (fun H => H). Qed.

(* ---- what the NEXT effect in a chain needs off this one --------------- *)

Lemma eff_free_inode_out (P : Z -> list (bv 8)) (sb : fs_sb) (i b : Z) :
  b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
  b <> sb_bmapstart sb ->
  eff_free_inode P sb i b = P b.
Proof.
  intros Hb1 Hb2. unfold eff_free_inode.
  rewrite fs_upd_ne by exact Hb2.
  apply (eff_dinode_out sb). exact Hb1.
Qed.

Lemma eff_free_inode_parse (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_sb_ok sb -> 0 <= i < 16 * (sb_ninodes sb / 16 + 1) ->
  fs_parse_sb P = Some sb ->
  fs_parse_sb (eff_free_inode P sb i) = Some sb.
Proof.
  intros Hok Hi Hp.
  destruct (iblock_bounds sb Hok i Hi) as (Hib1 & _ & Hib3).
  destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
  rewrite (fs_parse_sb_ext P (eff_free_inode P sb i))
    by (apply (eff_free_inode_out P sb i SB_BNO);
        unfold SB_BNO, fs_data_start in *; lia).
  exact Hp.
Qed.

Lemma eff_free_inode_dinode (P : Z -> list (bv 8)) (sb : fs_sb) (i j : Z) :
  fs_sb_ok sb -> 0 <= i < 16 * (sb_ninodes sb / 16 + 1) ->
  0 <= j < 16 * (sb_ninodes sb / 16 + 1) ->
  fs_dinode (eff_free_inode P sb i) sb j
  = if decide (j = i) then di_free_v (fs_dinode P sb i) else fs_dinode P sb j.
Proof.
  intros Hok Hi Hj.
  destruct (iblock_bounds sb Hok j Hj) as (_ & _ & Hjb3).
  assert (Hblk : eff_free_inode P sb i
                   (IBLOCK (fs_inum_bv j) (sb_inodestart sb))
                 = eff_dinode P sb i (di_free_v (fs_dinode P sb i))
                     (IBLOCK (fs_inum_bv j) (sb_inodestart sb)))
    by (unfold eff_free_inode; apply fs_upd_ne; lia).
  rewrite (fs_dinode_ext _ _ sb j Hblk).
  exact (eff_dinode_dec sb Hok P i _ j (di_free_v_wf _) Hi Hj).
Qed.
