(* ====================================================================== *)
(*  FsDurRead.v -- THE SNAPSHOT'S BYTE IDENTITY, AND WHAT IT READS         *)
(*  (durable-disk lane H3; claude-notes/design/durable-fs-plan.md          *)
(*  sections 2 and 4)                                                     *)
(*                                                                        *)
(*  A DURABLE SNAPSHOT'S BYTE AUTHORITY STANDS AT THE COMMITTED VIEW'S     *)
(*  BYTES.  [snap_auth g D] is the authority at the snapshot's own map   *)
(*  [B] together with ONE equation between two VALUES -- [B] is inside     *)
(*  [LogDefs.fs_dbytes D], the flattening of the WAL's committed block map *)
(*  -- and that equation is the whole of the snapshot's IDENTITY.  It is   *)
(*  not a consistency clause about the file system: it says nothing about  *)
(*  any inode, any block role or any bitmap bit.                           *)
(*                                                                        *)
(*  WHAT IT BUYS.  Every BYTE TIE of [FsDurSnap.snap_bytes] -- the         *)
(*  superblock's block, the bitmap block, a record's sixty-four bytes, a   *)
(*  data block, an indirect block, the free pool's coverage -- becomes a   *)
(*  READING off the snapshot's own resources: the instance's byte legs are *)
(*  elements of [g], the authority pins their values inside [fs_dbytes D], *)
(*  and [FsBlocks.map_seqZ_slice] turns a run inside a block into that     *)
(*  block's slice.  Nothing is carried and nothing is materialised.        *)
(*                                                                        *)
(*  WHAT IT DOES NOT BUY, and this file is where the boundary is drawn:    *)
(*  a fact about a block [D] holds and the snapshot's footprint does NOT   *)
(*  cover is not readable at all -- the authority may hold entries no      *)
(*  fragment names.  Those facts are the GEOMETRY                          *)
(*  ([FsDurSnap.snap_shape]), and they are the residue the snapshot still  *)
(*  carries.                                                              *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap numbers dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import BioDefs.
Require Import DiskImg.       (* [diskImgG] -- IMPORTED, not merely required:
                                 a capacity class named through a transitive
                                 Require is inert (durable-notes.md) *)
Require Import FsImg.         (* [BSIZE_z] *)
Require Import LogDefs.       (* [fs_dbytes] *)
Require Import FsDurBytes.    (* [dbytes_ok], [fs_dbytes_lookup], and
                                 [snap_gamma] -- the durable family's record.
                                 NOT [FsDurXfer]: the transport is not below
                                 the identity and nothing here uses it *)
Require Import FsBlocks.      (* [BSZ], [byte_range_q_lookup], [map_seqZ_slice] *)
Require Export FsState.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE BLOCK MAP'S OWN ROW: every block is a WHOLE block              *)
(* ====================================================================== *)

Definition dblk_full (D : gmap Z (list (bv 8))) : Prop :=
  forall (b : Z) (bs : list (bv 8)), D !! b = Some bs -> length bs = BSIZE.

Lemma dblk_full_ok (D : gmap Z (list (bv 8))) : dblk_full D -> dbytes_ok D.
Proof. exact (dbytes_ok_full D). Qed.

(* a whole block of [D] IS a run of its flattening *)
Lemma fs_dbytes_block_sub (D : gmap Z (list (bv 8))) (b : Z)
    (cs : list (bv 8)) :
  dblk_full D -> D !! b = Some cs ->
  (map_seqZ (b * BSZ) cs : gmap Z (bv 8)) ⊆ fs_dbytes D.
Proof.
  intros Hf Hb. apply map_subseteq_spec. intros a v Ha.
  apply lookup_map_seqZ_Some in Ha as [Hge Hk].
  pose proof (fs_dbytes_lookup D b cs (Z.to_nat (a - b * BSZ)) v
                (dblk_full_ok D Hf) Hb Hk) as Hd.
  assert (Heq : b * Z.of_nat BSIZE + Z.of_nat (Z.to_nat (a - b * BSZ)) = a).
  { rewrite BSZ_BSIZE. lia. }
  rewrite Heq in Hd. exact Hd.
Qed.

(* ...and the block a byte of the flattening belongs to is the one its
   address names.  This is the ONE arithmetic step, and it is a division:
   a block starts at a multiple of the stride and is no longer than it. *)
Lemma fs_dbytes_block_of (D : gmap Z (list (bv 8))) (b off : Z) (v : bv 8) :
  dblk_full D -> 0 <= off < BSZ ->
  fs_dbytes D !! (b * BSZ + off) = Some v ->
  exists cs, D !! b = Some cs /\ cs !! Z.to_nat off = Some v.
Proof.
  intros Hf Hoff Ha.
  apply (proj1 (fs_dbytes_lookup_Some D _ v (dblk_full_ok D Hf))) in Ha
    as (b' & cs & k & Hb' & Hk & Heq).
  assert (Hlen : length cs = BSIZE) by exact (Hf b' cs Hb').
  assert (Hklt : (k < BSIZE)%nat)
    by (rewrite -Hlen; exact (lookup_lt_Some _ _ _ Hk)).
  rewrite -BSZ_BSIZE in Heq.
  assert (Hkz : 0 <= Z.of_nat k < BSZ) by (rewrite -BSZ_BSIZE; lia).
  assert (Hbz : BSZ <> 0) by (unfold BSZ; lia).
  assert (Hb : b = b').
  { assert (H1 : (b * BSZ + off) `div` BSZ = b).
    { rewrite Z.div_add_l; [| exact Hbz].
      rewrite (Z.div_small off BSZ Hoff). lia. }
    assert (H2 : (b' * BSZ + Z.of_nat k) `div` BSZ = b').
    { rewrite Z.div_add_l; [| exact Hbz].
      rewrite (Z.div_small (Z.of_nat k) BSZ Hkz). lia. }
    rewrite -H1 -H2 Heq //. }
  subst b'. exists cs. split; [exact Hb' |].
  assert (Hoffk : Z.to_nat off = k) by lia.
  rewrite Hoffk. exact Hk.
Qed.

(* ====================================================================== *)
(*  2.  A RUN INSIDE A BLOCK IS THAT BLOCK'S SLICE                         *)
(*                                                                        *)
(*  The one reading every byte tie goes through.  At [off = 0] and a       *)
(*  block-wide run it is "the block IS these bytes" ([snap_blk_read]);     *)
(*  at a record's offset it is [FsDurSnap.rec_in_blk] verbatim.            *)
(* ====================================================================== *)

Lemma dbytes_run_read (D : gmap Z (list (bv 8))) (b off : Z)
    (bs : list (bv 8)) :
  dblk_full D -> 0 <= off -> off + Z.of_nat (length bs) <= BSZ ->
  (0 < length bs)%nat ->
  (map_seqZ (b * BSZ + off) bs : gmap Z (bv 8)) ⊆ fs_dbytes D ->
  exists cs, D !! b = Some cs /\ length cs = BSIZE
             /\ exists pre post,
                  cs = (pre ++ bs ++ post)%list
                  /\ Z.of_nat (length pre) = off.
Proof.
  intros Hf Hoff Hfit Hne Hsub.
  (* the run's FIRST byte names the block *)
  destruct (lookup_lt_is_Some_2 bs 0%nat Hne) as [v0 Hv0].
  assert (Hin : (map_seqZ (b * BSZ + off) bs : gmap Z (bv 8))
                  !! (b * BSZ + off) = Some v0).
  { assert (Hz : b * BSZ + off = b * BSZ + off + Z.of_nat 0%nat) by lia.
    rewrite {1}Hz. by apply lookup_map_seqZ_Some_inv. }
  pose proof (lookup_weaken _ _ _ _ Hin Hsub) as Hfd.
  assert (Hoffb : 0 <= off < BSZ) by lia.
  destruct (fs_dbytes_block_of D b off v0 Hf Hoffb Hfd) as (cs & Hb & _).
  assert (Hlen : length cs = BSIZE) by exact (Hf b cs Hb).
  (* ...and the run is that block's slice *)
  set (o := Z.to_nat off).
  assert (Hoz : Z.of_nat o = off) by (unfold o; lia).
  assert (Hle : (o + length bs <= length cs)%nat).
  { rewrite Hlen. rewrite -BSZ_BSIZE in Hfit. lia. }
  assert (Hcssub : (map_seqZ (b * BSZ) cs : gmap Z (bv 8)) ⊆ fs_dbytes D)
    by exact (fs_dbytes_block_sub D b cs Hf Hb).
  assert (Hsub' : (map_seqZ (b * BSZ + Z.of_nat o) bs : gmap Z (bv 8))
                    ⊆ fs_dbytes D) by (rewrite Hoz; exact Hsub).
  pose proof (map_seqZ_slice cs bs (b * BSZ) o (fs_dbytes D)
                Hle Hcssub Hsub') as Hslice.
  exists cs. split; [exact Hb |]. split; [exact Hlen |].
  exists (take o cs), (drop (o + length bs)%nat cs). split.
  - assert (Hd : drop o cs = (bs ++ drop (o + length bs)%nat cs)%list).
    { rewrite -(take_drop (length bs) (drop o cs)) -Hslice drop_drop //. }
    rewrite -Hd take_drop //.
  - rewrite length_take. rewrite -Hoz. lia.
Qed.

(* ====================================================================== *)
(*  2b.  TWO RUNS OF ONE BLOCK THAT MEET                                   *)
(*                                                                        *)
(*  [FsStateDefs.byte_range_q_excl] refutes two runs at the SAME offset;   *)
(*  the used-set coupling needs the cross-offset form, because a record's  *)
(*  sixty-four bytes and the whole region block that carries them start at *)
(*  different offsets and still overlap.  Exclusivity, one byte of it.     *)
(* ====================================================================== *)

Section Overlap.
  Context {Σ : gFunctors}.
  Implicit Types Γ : fs_view_names Σ.

  Lemma byte_range_q_overlap Γ (Hex : phi_excl Γ) (dq1 dq2 : dfrac)
      (b off1 off2 : Z) (bs1 bs2 : list (bv 8)) (k1 k2 : nat) :
    ~ ✓ (dq1 ⋅ dq2) -> (k1 < length bs1)%nat -> (k2 < length bs2)%nat ->
    off1 + Z.of_nat k1 = off2 + Z.of_nat k2 ->
    byte_range_q Γ dq1 b off1 bs1 -∗ byte_range_q Γ dq2 b off2 bs2 -∗ False.
  Proof.
    intros Hnv Hk1 Hk2 Heq. iIntros "H1 H2".
    destruct (lookup_lt_is_Some_2 bs1 k1 Hk1) as [v1 Hv1].
    destruct (lookup_lt_is_Some_2 bs2 k2 Hk2) as [v2 Hv2].
    rewrite /byte_range_q.
    iDestruct (big_sepL_lookup _ _ k1 v1 Hv1 with "H1") as "H1".
    iDestruct (big_sepL_lookup _ _ k2 v2 Hv2 with "H2") as "H2".
    assert (Ha : b * BSIZE_z + off2 + Z.of_nat k2
                 = b * BSIZE_z + off1 + Z.of_nat k1) by lia.
    rewrite Ha.
    iDestruct (Hex _ v1 v2 dq1 dq2 with "[$H1 $H2]") as %Hv.
    iPureIntro. exact (Hnv Hv).
  Qed.

  (* the shape both the metadata refutation and the free pool's use: a run
     INSIDE a whole block that somebody else owns *)
  Lemma blk_run_overlap Γ (Hex : phi_excl Γ) (dq1 dq2 : dfrac)
      (b off : Z) (bs cs : list (bv 8)) :
    ~ ✓ (dq1 ⋅ dq2) -> 0 <= off -> off + Z.of_nat (length bs) <= BSIZE_z ->
    (0 < length bs)%nat ->
    blk_owned_q Γ dq1 b cs -∗ byte_range_q Γ dq2 b off bs -∗ False.
  Proof.
    intros Hnv Hoff Hfit Hne. iIntros "H1 H2". rewrite /blk_owned_q.
    iDestruct "H1" as "[%Hlc H1]".
    iApply (byte_range_q_overlap Γ Hex dq1 dq2 b 0 off cs bs
              (Z.to_nat off) 0%nat Hnv
              ltac:(rewrite Hlc; unfold BSIZE_z, BSIZE in *; lia)
              Hne ltac:(lia) with "H1 H2").
  Qed.

  (* THE FREE POOL'S REFUTATION, AT A RUN.  [FsStateBitmap.free_pool_used]
     wants a WHOLE block; a record's sixty-four bytes are enough, and that
     is what the used-set coupling needs at a region block. *)
  Lemma free_pool_used_run Γ (Hex : phi_excl Γ) (nb : Z) (u : gset Z)
      (b off : Z) (bs : list (bv 8)) :
    0 <= b < nb -> 0 <= off -> off + Z.of_nat (length bs) <= BSIZE_z ->
    (0 < length bs)%nat ->
    free_pool Γ nb u -∗ byte_range Γ b off bs -∗ ⌜b ∈ u⌝.
  Proof.
    intros Hb Hoff Hfit Hne.
    destruct (decide (b ∈ u)) as [Hin | Hnot].
    { iIntros "_ _". iPureIntro. exact Hin. }
    assert (Hb' : Z.of_nat (Z.to_nat b) = b) by lia.
    rewrite (free_pool_split Γ nb u (Z.to_nat b)); [| lia].
    rewrite Hb' {1}/pool_elt (bool_decide_eq_false_2 _ Hnot).
    iIntros "[Helt _] Hr". iDestruct "Helt" as (bs') "Helt". iExFalso.
    rewrite blk_owned_1 byte_range_1.
    iApply (blk_run_overlap Γ Hex (DfracOwn 1) (DfracOwn 1) b off bs bs'
              (dfrac_full_nvalid _) Hoff Hfit Hne with "Helt Hr").
  Qed.

  (* ---- an inode's BLOCK legs, apart from its record's ---------------- *)

  (* [inode_phi] is [rec_owned ∗ (data ∗ indirect)]; the second factor is
     the only one the used-set coupling reads, and separating it by name is
     what lets ONE inode's record and ONE inode's block be taken out of the
     same [∗] (they are different conjuncts even at the same inum). *)
  Definition inode_dat Γ (n : fs_node) : iProp Σ :=
    (([∗ map] k ↦ bs ∈ fn_blk n, blk_owned Γ (fn_naddr n k) bs)
     ∗ ind_owned Γ n)%I.

  Lemma inode_phi_dat Γ (sb : fs_sb) (i : Z) (n : fs_node) :
    inode_phi Γ sb i n ⊣⊢ rec_owned Γ sb i (fn_rec n) ∗ inode_dat Γ n.
  Proof. rewrite /inode_phi /inode_dat //. Qed.

End Overlap.

(* ====================================================================== *)
(*  3.  THE SNAPSHOT'S IDENTITY, AND THE READINGS OFF IT                   *)
(* ====================================================================== *)

Section Read.
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.

  (* THE IDENTITY.  The snapshot's byte authority, and the equation that
     makes it the COMMITTED VIEW's: every byte the snapshot owns is a byte
     [D] holds, at the address [D] holds it.

     THE MAP ITSELF IS EXISTENTIAL.  Nothing above this definition ever
     reads [B]'s value -- every consumer goes through the equation, and
     [P_dur] bound it existentially anyway -- so binding it here rather
     than at every reader takes one argument off this predicate,
     [FsDurSnap.fs_snap] and their thirty-odd readings. *)
  Definition snap_auth (g : gname)
      (D : gmap Z (list (bv 8))) : iProp Σ :=
    (∃ B : gmap Z (bv 8), ghost_map_auth g 1 B ∗ ⌜B ⊆ fs_dbytes D⌝)%I.

  Global Instance snap_auth_timeless g D : Timeless (snap_auth g D).
  Proof. rewrite /snap_auth. apply _. Qed.

  (* SEALED: the identity is ONE hypothesis at every reader, and an
     [iIntros] pattern that descends into it would split the authority off
     the equation (durable-notes.md, the [Typeclasses Opaque] rule). *)
  Global Typeclasses Opaque snap_auth.

  (* the fresh family's byte legs ARE elements of [g] -- [snap_gamma]'s
     [fsΦ] is the ghost-map element on the nose -- so ONE [ghost_map_lookup]
     per byte pins the run inside the authority, and the identity carries it
     the rest of the way into [fs_dbytes D]. *)
  Lemma snap_run_sub (g gl gt : gname)
      (D : gmap Z (list (bv 8))) (dq : dfrac) (b off : Z)
      (bs : list (bv 8)) :
    snap_auth g D -∗
    byte_range_q (snap_gamma g gl gt) dq b off bs -∗
    ⌜(map_seqZ (b * BSZ + off) bs : gmap Z (bv 8)) ⊆ fs_dbytes D⌝.
  Proof.
    iIntros "Hau Hr". rewrite /snap_auth.
    iDestruct "Hau" as (B) "[Ha %Hsub]".
    iAssert (⌜forall (k : nat) (v : bv 8), bs !! k = Some v ->
               B !! (b * BSIZE_z + off + Z.of_nat k)%Z = Some v⌝)%I
      with "[Ha Hr]" as %Hpt.
    { rewrite bi.pure_forall. iIntros (k).
      rewrite bi.pure_forall. iIntros (v).
      rewrite bi.pure_impl. iIntros (Hk).
      rewrite /byte_range_q.
      iDestruct (big_sepL_lookup _ _ k v Hk with "Hr") as "Hk".
      rewrite /snap_gamma /=.
      iApply (ghost_map_lookup with "Ha Hk"). }
    iPureIntro. apply map_subseteq_spec. intros a v Ha.
    apply lookup_map_seqZ_Some in Ha as [Hge Hk].
    pose proof (Hpt _ v Hk) as HB.
    assert (Heq : b * BSIZE_z + off
                  + Z.of_nat (Z.to_nat (a - (b * BSZ + off))) = a)
      by (unfold BSIZE_z, BSZ in *; lia).
    rewrite Heq in HB.
    exact (lookup_weaken _ _ _ _ HB Hsub).
  Qed.

  (* A RECORD'S SIXTY-FOUR BYTES, at their slot: the block they sit in and
     the split that names them.  This IS [FsDurSnap.rec_in_blk]. *)
  Lemma snap_run_read (g gl gt : gname)
      (D : gmap Z (list (bv 8))) (dq : dfrac) (b off : Z)
      (bs : list (bv 8)) :
    dblk_full D -> 0 <= off -> off + Z.of_nat (length bs) <= BSZ ->
    (0 < length bs)%nat ->
    snap_auth g D -∗
    byte_range_q (snap_gamma g gl gt) dq b off bs -∗
    ⌜exists cs, D !! b = Some cs /\ length cs = BSIZE
                /\ exists pre post,
                     cs = (pre ++ bs ++ post)%list
                     /\ Z.of_nat (length pre) = off⌝.
  Proof.
    intros Hf Hoff Hfit Hne. iIntros "Ha Hr".
    iDestruct (snap_run_sub with "Ha Hr") as %Hsub.
    iPureIntro. exact (dbytes_run_read D b off bs Hf Hoff Hfit Hne Hsub).
  Qed.

  Lemma snap_run_read_full (g gl gt : gname)
      (D : gmap Z (list (bv 8))) (b off : Z) (bs : list (bv 8)) :
    dblk_full D -> 0 <= off -> off + Z.of_nat (length bs) <= BSZ ->
    (0 < length bs)%nat ->
    snap_auth g D -∗
    byte_range (snap_gamma g gl gt) b off bs -∗
    ⌜exists cs, D !! b = Some cs /\ length cs = BSIZE
                /\ exists pre post,
                     cs = (pre ++ bs ++ post)%list
                     /\ Z.of_nat (length pre) = off⌝.
  Proof.
    intros Hf Hoff Hfit Hne. rewrite byte_range_1.
    iApply (snap_run_read g gl gt D (DfracOwn 1) b off bs Hf Hoff Hfit Hne).
  Qed.

  (* A WHOLE BLOCK: the committed map holds exactly these bytes there. *)
  Lemma snap_blk_read (g gl gt : gname)
      (D : gmap Z (list (bv 8))) (dq : dfrac) (b : Z) (bs : list (bv 8)) :
    dblk_full D ->
    snap_auth g D -∗
    blk_owned_q (snap_gamma g gl gt) dq b bs -∗
    ⌜D !! b = Some bs⌝.
  Proof.
    (* [blk_owned_q] is sealed (a 1024-element big-op behind a definition is
       an [iFrame] hang), so the pair is opened by an explicit unfold *)
    intros Hf. iIntros "Ha Hb". rewrite /blk_owned_q.
    iDestruct "Hb" as "[%Hlb Hr]".
    iDestruct (snap_run_read g gl gt D dq b 0 bs Hf ltac:(lia)
                 ltac:(rewrite Hlb -BSZ_BSIZE; lia)
                 ltac:(rewrite Hlb; unfold BSIZE; lia) with "Ha Hr")
      as %(cs & Hb & Hlen & pre & post & Heq & Hpre).
    iPureIntro.
    assert (Hpl : length pre = 0%nat) by lia.
    assert (Hpe : pre = []) by (apply nil_length_inv; exact Hpl).
    assert (Hlens : (length pre + (length bs + length post) = BSIZE)%nat).
    { rewrite -Hlen Heq !length_app //. }
    assert (Hql : length post = 0%nat) by lia.
    assert (Hqe : post = []) by (apply nil_length_inv; exact Hql).
    rewrite Hb Heq Hpe Hqe app_nil_l app_nil_r //.
  Qed.

  Lemma snap_blk_read_full (g gl gt : gname)
      (D : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8)) :
    dblk_full D ->
    snap_auth g D -∗
    blk_owned (snap_gamma g gl gt) b bs -∗
    ⌜D !! b = Some bs⌝.
  Proof.
    intros Hf. rewrite blk_owned_1.
    iApply (snap_blk_read g gl gt D (DfracOwn 1) b bs Hf).
  Qed.

  (* ...and the DOMAIN reading a block whose bytes the snapshot owns at an
     unknown value needs: the committed map holds SOMETHING there.  This is
     the free pool's arm. *)
  Lemma snap_blk_dom (g gl gt : gname)
      (D : gmap Z (list (bv 8))) (dq : dfrac) (b : Z) (bs : list (bv 8)) :
    dblk_full D ->
    snap_auth g D -∗
    blk_owned_q (snap_gamma g gl gt) dq b bs -∗
    ⌜is_Some (D !! b)⌝.
  Proof.
    intros Hf. iIntros "Ha Hb".
    iDestruct (snap_blk_read with "Ha Hb") as %Hb; [exact Hf |].
    iPureIntro. by exists bs.
  Qed.

End Read.
