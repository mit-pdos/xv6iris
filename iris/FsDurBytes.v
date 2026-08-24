(* FsDurBytes.v -- THE THEORY OF [LogDefs.fs_dbytes], AND THE DURABLE VIEW
   RECORD [Gamma_D].

   Design of record: claude-notes/design/fs-state.md sections 1 and 4; this
   is durable-disk 2c-img, leaf 1.

   [LogDefs.fs_dbytes] flattens a BLOCK view [D : gmap Z (list (bv 8))] into
   the BYTE map [P_wf]'s authority is held at: block [b]'s [i]th byte lives
   at [b * BSIZE + i].  It had four use sites and no theory at all -- every
   one of them re-based the whole map with [fs_dview_rebase] and never
   looked inside.  Stage 2c's [P_wf] does look inside: it has to say that
   the byte elements at [fs_dbytes D] ARE the file system's per-block
   ownership, one [FsStateDefs.blk_owned] per entry of [D].  That is
   [fs_dbelems_dbytes] below, and everything above it in this file exists to
   get there.

   THE ONE PREMISE IS A LENGTH BOUND, and it is what makes the flattening
   injective: two blocks' byte ranges are disjoint exactly because a block
   contributes at most [BSIZE] bytes starting at a multiple of [BSIZE]
   ([dbytes_seq_disj]).  Without it [fs_dbytes] is still defined -- the fold
   just overwrites -- and says nothing, so no lemma below holds unguarded.
   [map_fold]'s own insert equation ([map_fold_insert_L]) needs the same
   fact, since its commutation premise is [map_union_comm]'s.

   [Gamma_D] IS [FsBytesGamma.fs_gamma_L]'s DURABLE TWIN.  Same record, same
   two properties consumers cannot prove of an abstract [fsΦ]
   ([FsStateDefs.phi_excl], [FsStateDefs.GTimeless]); what differs is which
   byte map's full element [fsΦ] is, and where the link/top gnames come
   from -- [RiscvPtsto.fs_dur_names], the fixed layer's bundle, rather than
   the era's [FsBlocks.fs_names].  Both gnames arrive as PARAMETERS (the
   standing rule), so this file binds no [riscvFixedGS] and a caller may
   spell the ambient instance [fs_gamma_D riscv_dview_name riscv_fsdur]
   itself. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop ghost_map.
Require Import BioDefs.        (* [BSIZE] -- the flattening's stride       *)
Require Import RiscvPtsto.     (* [fs_dur_names] -- Gamma_D's two gnames   *)
Require Import FsImg.          (* [BSIZE_z] -- [byte_range]'s own stride   *)
Require Import LogDefs.        (* [fs_dbytes] / [fs_dview]                 *)
(* LAST, so its [byte_range]/[blk_owned] win over the block layer's twins
   wherever a consumer imports both (durable-notes.md, AND WHERE THAT
   IMPORT COLLIDES PUT IT EARLY). *)
Require Export FsStateDefs.

(* the proofmode import re-opens [nat_scope] on top of the scope stack *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PURE THEORY OF [fs_dbytes]                                    *)
(* ===================================================================== *)

(* the flattening's stride, as a [Z] literal.  Every arithmetic side
   condition below is discharged at [1024]; [BSIZE] is a [nat] and
   [Z.of_nat BSIZE] is opaque to [lia]. *)
Lemma dbytes_stride : Z.of_nat BSIZE = 1024.
Proof. reflexivity. Qed.

(* THE GUARD.  Every block of [D] contributes at most a block's worth of
   bytes -- which is what makes distinct blocks' contributions disjoint. *)
Definition dbytes_ok (D : gmap Z (list (bv 8))) : Prop :=
  forall (b : Z) (bs : list (bv 8)), D !! b = Some bs -> (length bs <= BSIZE)%nat.

Lemma dbytes_ok_full (D : gmap Z (list (bv 8))) :
  (forall b bs, D !! b = Some bs -> length bs = BSIZE) -> dbytes_ok D.
Proof. intros H b bs Hb. rewrite (H b bs Hb). reflexivity. Qed.

(* the [D !! b = None] premise is REAL, not slack: without it the insert
   SHADOWS whatever [D] holds at [b], and that entry is unconstrained. *)
Lemma dbytes_ok_insert (D : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8)) :
  D !! b = None -> dbytes_ok (<[b := bs]> D) -> dbytes_ok D.
Proof.
  intros Hb Hok c cs Hc.
  destruct (decide (c = b)) as [-> | Hne].
  - rewrite Hb in Hc. discriminate.
  - apply (Hok c cs). rewrite lookup_insert_ne; [exact Hc |].
    intros ->. exact (Hne eq_refl).
Qed.

Lemma dbytes_ok_head (D : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8)) :
  dbytes_ok (<[b := bs]> D) -> (length bs <= BSIZE)%nat.
Proof. intros Hok. apply (Hok b bs). apply lookup_insert. Qed.

Lemma dbytes_ok_insert_2 (D : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8)) :
  dbytes_ok D -> (length bs <= BSIZE)%nat -> dbytes_ok (<[b := bs]> D).
Proof.
  intros Hok Hl c cs Hc.
  apply lookup_insert_Some in Hc as [[_ Heq] | [_ Hc]];
    [rewrite -Heq; exact Hl | exact (Hok c cs Hc)].
Qed.

(* TWO BLOCKS' BYTE RANGES ARE DISJOINT.  The whole content of the length
   premise: a block starts at a multiple of the stride and is no longer
   than it, so the ranges of [b1] and [b2 <> b1] cannot meet. *)
Lemma dbytes_seq_disj (b1 b2 : Z) (bs1 bs2 : list (bv 8)) :
  b1 <> b2 -> (length bs1 <= BSIZE)%nat -> (length bs2 <= BSIZE)%nat ->
  (map_seqZ (b1 * Z.of_nat BSIZE) bs1 : gmap Z (bv 8))
    ##ₘ (map_seqZ (b2 * Z.of_nat BSIZE) bs2 : gmap Z (bv 8)).
Proof.
  intros Hne H1 H2.
  assert (Hl1 : Z.of_nat (length bs1) <= 1024).
  { rewrite -dbytes_stride. apply Nat2Z.inj_le. exact H1. }
  assert (Hl2 : Z.of_nat (length bs2) <= 1024).
  { rewrite -dbytes_stride. apply Nat2Z.inj_le. exact H2. }
  apply map_seqZ_disjoint. rewrite dbytes_stride. lia.
Qed.

Lemma fs_dbytes_empty : fs_dbytes ∅ = ∅.
Proof. reflexivity. Qed.

(* THE INSERT EQUATION.  [map_fold_insert_L]'s commutation premise is
   restricted to the keys of the map, which is exactly where the length
   guard lives -- so [map_union_comm] discharges it. *)
Lemma fs_dbytes_insert (D : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8)) :
  dbytes_ok (<[b := bs]> D) -> D !! b = None ->
  fs_dbytes (<[b := bs]> D)
  = (map_seqZ (b * Z.of_nat BSIZE) bs : gmap Z (bv 8)) ∪ fs_dbytes D.
Proof.
  intros Hok Hb.
  assert (Hcomm :
    forall (j1 j2 : Z) (z1 z2 : list (bv 8)) (y : gmap Z (bv 8)),
      j1 <> j2 ->
      <[b := bs]> D !! j1 = Some z1 -> <[b := bs]> D !! j2 = Some z2 ->
      (map_seqZ (j1 * Z.of_nat BSIZE) z1 : gmap Z (bv 8))
        ∪ ((map_seqZ (j2 * Z.of_nat BSIZE) z2 : gmap Z (bv 8)) ∪ y)
      = (map_seqZ (j2 * Z.of_nat BSIZE) z2 : gmap Z (bv 8))
        ∪ ((map_seqZ (j1 * Z.of_nat BSIZE) z1 : gmap Z (bv 8)) ∪ y)).
  { intros j1 j2 z1 z2 y Hne Hj1 Hj2.
    rewrite !assoc_L. f_equal. apply map_union_comm.
    apply dbytes_seq_disj;
      [exact Hne | exact (Hok j1 z1 Hj1) | exact (Hok j2 z2 Hj2)]. }
  exact (map_fold_insert_L _ ∅ b bs D Hcomm Hb).
Qed.

(* ...and the disjointness the insert equation's two summands enjoy *)
Lemma fs_dbytes_disj_seq (D : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8)) :
  dbytes_ok D -> (length bs <= BSIZE)%nat -> D !! b = None ->
  (map_seqZ (b * Z.of_nat BSIZE) bs : gmap Z (bv 8)) ##ₘ fs_dbytes D.
Proof.
  revert b bs.
  induction D as [| b0 bs0 D Hb0 IH] using map_ind; intros b bs Hok Hlen Hb.
  - rewrite fs_dbytes_empty. apply map_disjoint_empty_r.
  - apply lookup_insert_None in Hb as [HbD Hne].
    assert (HokD : dbytes_ok D) by exact (dbytes_ok_insert D b0 bs0 Hb0 Hok).
    rewrite (fs_dbytes_insert D b0 bs0 Hok Hb0).
    apply map_disjoint_union_r. split.
    + apply dbytes_seq_disj;
        [ intros ->; exact (Hne eq_refl)
        | exact Hlen
        | exact (dbytes_ok_head D b0 bs0 Hok) ].
    + exact (IH b bs HokD Hlen HbD).
Qed.

(* THE LOOKUP LAW, both ways: a byte of the flattening is a byte of exactly
   one block of [D], at its own offset. *)
Lemma fs_dbytes_lookup_Some (D : gmap Z (list (bv 8))) (a : Z) (v : bv 8) :
  dbytes_ok D ->
  fs_dbytes D !! a = Some v
  <-> exists (b : Z) (bs : list (bv 8)) (k : nat),
        D !! b = Some bs /\ bs !! k = Some v
        /\ a = b * Z.of_nat BSIZE + Z.of_nat k.
Proof.
  revert a v.
  induction D as [| b0 bs0 D Hb0 IH] using map_ind; intros a v Hok.
  - rewrite fs_dbytes_empty lookup_empty. split; [discriminate |].
    intros (b & bs & k & Hb & _ & _). rewrite lookup_empty in Hb. discriminate.
  - assert (HokD : dbytes_ok D) by exact (dbytes_ok_insert D b0 bs0 Hb0 Hok).
    assert (Hlen0 : (length bs0 <= BSIZE)%nat)
      by exact (dbytes_ok_head D b0 bs0 Hok).
    rewrite (fs_dbytes_insert D b0 bs0 Hok Hb0).
    rewrite (lookup_union_Some _ _ _ _
               (fs_dbytes_disj_seq D b0 bs0 HokD Hlen0 Hb0)).
    rewrite lookup_map_seqZ_Some.
    split.
    + intros [[Hge Hk] | Hin].
      * exists b0, bs0, (Z.to_nat (a - b0 * Z.of_nat BSIZE)).
        split; [apply lookup_insert |].
        split; [exact Hk |].
        rewrite Z2Nat.id; lia.
      * apply (proj1 (IH a v HokD)) in Hin as (b & bs & k & Hb & Hk & ->).
        exists b, bs, k. split; [| split; [exact Hk | reflexivity]].
        rewrite lookup_insert_ne; [exact Hb |].
        intros ->. rewrite Hb0 in Hb. discriminate.
    + intros (b & bs & k & Hb & Hk & ->).
      apply lookup_insert_Some in Hb as [[Heq Hbs] | [Hne Hb]].
      * left. rewrite -Heq Hbs. split; [lia |].
        assert (Hz : b0 * Z.of_nat BSIZE + Z.of_nat k - b0 * Z.of_nat BSIZE
                     = Z.of_nat k) by lia.
        rewrite Hz Nat2Z.id. exact Hk.
      * right. apply (proj2 (IH _ v HokD)). by exists b, bs, k.
Qed.

Lemma fs_dbytes_lookup (D : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8))
    (k : nat) (v : bv 8) :
  dbytes_ok D -> D !! b = Some bs -> bs !! k = Some v ->
  fs_dbytes D !! (b * Z.of_nat BSIZE + Z.of_nat k) = Some v.
Proof.
  intros Hok Hb Hk. apply (proj2 (fs_dbytes_lookup_Some D _ v Hok)).
  by exists b, bs, k.
Qed.

(* THE DOMAIN, as the union of the blocks' byte RANGES.  Stated pointwise
   ([is_Some] of the lookup) rather than as a [dom] equation: a [dom] fact
   over a [gset Z] is reached by [elem_of_dom] and the lookup laws, never by
   [dom_union_L] and [set_solver] (durable-notes.md). *)
Lemma fs_dbytes_dom (D : gmap Z (list (bv 8))) (a : Z) :
  dbytes_ok D ->
  is_Some (fs_dbytes D !! a)
  <-> exists (b : Z) (bs : list (bv 8)),
        D !! b = Some bs
        /\ b * Z.of_nat BSIZE <= a < b * Z.of_nat BSIZE + Z.of_nat (length bs).
Proof.
  intros Hok. split.
  - intros [v Hv].
    apply (proj1 (fs_dbytes_lookup_Some D a v Hok))
      in Hv as (b & bs & k & Hb & Hk & ->).
    exists b, bs. split; [exact Hb |].
    apply lookup_lt_Some in Hk. lia.
  - intros (b & bs & Hb & Hlo & Hhi).
    assert (Hk : (Z.to_nat (a - b * Z.of_nat BSIZE) < length bs)%nat) by lia.
    destruct (lookup_lt_is_Some_2 bs _ Hk) as [v Hv].
    exists v. apply (fs_dbytes_lookup D b bs _ v Hok Hb) in Hv.
    rewrite Z2Nat.id in Hv; [| lia].
    assert (Hz : b * Z.of_nat BSIZE + (a - b * Z.of_nat BSIZE) = a) by lia.
    rewrite Hz in Hv. exact Hv.
Qed.

(* the residual split the tie needs: [D] cut in two is its flattening cut
   in two, and the two halves' byte maps are disjoint *)
Lemma fs_dbytes_union (D1 D2 : gmap Z (list (bv 8))) :
  dbytes_ok (D1 ∪ D2) -> D1 ##ₘ D2 ->
  fs_dbytes (D1 ∪ D2) = fs_dbytes D1 ∪ fs_dbytes D2.
Proof.
  revert D2.
  induction D1 as [| b bs D1 Hb IH] using map_ind; intros D2 Hok Hdisj.
  - rewrite left_id_L fs_dbytes_empty left_id_L //.
  - apply map_disjoint_insert_l in Hdisj as [Hb2 Hdisj].
    assert (Hbu : (D1 ∪ D2) !! b = None)
      by (rewrite lookup_union_None; split; [exact Hb | exact Hb2]).
    assert (Hoku : dbytes_ok (<[b := bs]> (D1 ∪ D2)))
      by (rewrite insert_union_l; exact Hok).
    assert (HokD : dbytes_ok (D1 ∪ D2))
      by exact (dbytes_ok_insert (D1 ∪ D2) b bs Hbu Hoku).
    assert (HokD1 : dbytes_ok D1).
    { intros c cs Hc. apply (HokD c cs). by apply lookup_union_Some_l. }
    assert (Hlb : (length bs <= BSIZE)%nat)
      by exact (dbytes_ok_head (D1 ∪ D2) b bs Hoku).
    rewrite -insert_union_l.
    rewrite (fs_dbytes_insert (D1 ∪ D2) b bs Hoku Hbu).
    rewrite (fs_dbytes_insert D1 b bs
               (dbytes_ok_insert_2 D1 b bs HokD1 Hlb) Hb).
    rewrite (IH D2 HokD Hdisj) assoc_L //.
Qed.

(* ===================================================================== *)
(*  2.  THE DURABLE VIEW RECORD, AND THE BYTE ELEMENTS                    *)
(* ===================================================================== *)

Section DurBytes.
  (* [diskImgG] is the tree's UNIQUE [ghost_mapG Σ Z (bv 8)] -- the class
     [LogDefs.fs_dview] itself is stated over, and the one [γD]'s authority
     lives at ([RiscvPtsto.riscv_dview_name]). *)
  Context `{!diskImgG Σ}.

  (* [LogDefs.fs_dview]'s BODY, named.  [fs_dview] is [Typeclasses Opaque]
     and rightly so; the theory below is about the body, and the two are
     one [rewrite] apart ([fs_dview_dbelems]). *)
  Definition fs_dbelems (g : gname) (B : gmap Z (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ v ∈ B, a ↪[g] v)%I.

  Lemma fs_dview_dbelems (g : gname) (B : gmap Z (bv 8)) :
    fs_dview g B ⊣⊢ fs_dbelems g B.
  Proof. rewrite /fs_dview /fs_dbelems //. Qed.

  Global Instance fs_dbelems_timeless g B : Timeless (fs_dbelems g B).
  Proof. rewrite /fs_dbelems. apply _. Qed.

  Lemma fs_dbelems_empty (g : gname) : fs_dbelems g ∅ ⊣⊢ emp.
  Proof. rewrite /fs_dbelems big_sepM_empty //. Qed.

  Lemma fs_dbelems_union (g : gname) (B1 B2 : gmap Z (bv 8)) :
    B1 ##ₘ B2 ->
    fs_dbelems g (B1 ∪ B2) ⊣⊢ fs_dbelems g B1 ∗ fs_dbelems g B2.
  Proof. intros Hd. rewrite /fs_dbelems big_sepM_union //. Qed.

  (* ------------------------------------------------------------------ *)
  (*  2a.  [Gamma_D]                                                     *)
  (* ------------------------------------------------------------------ *)

  (* [FsBytesGamma.fs_gamma_L]'s durable twin: the same record, at the
     durable byte map's full element and the fixed layer's two gnames. *)
  Definition fs_gamma_D (g : gname) (Γd : fs_dur_names) : fs_view_names Σ :=
    MkFsView (fun (a : Z) (v : bv 8) => (a ↪[g] v)%I)
             (fdn_link Γd) (fdn_top Γd).

  Lemma fs_gamma_D_phi (g : gname) (Γd : fs_dur_names) (a : Z) (v : bv 8) :
    fsΦ (fs_gamma_D g Γd) a v = (a ↪[g] v)%I.
  Proof. reflexivity. Qed.

  Lemma fs_gamma_D_link (g : gname) (Γd : fs_dur_names) :
    γlink (fs_gamma_D g Γd) = fdn_link Γd.
  Proof. reflexivity. Qed.

  Lemma fs_gamma_D_top (g : gname) (Γd : fs_dur_names) :
    γtop (fs_gamma_D g Γd) = fdn_top Γd.
  Proof. reflexivity. Qed.

  (* two owners of one byte is [False] -- the concrete instance of
     [FsStateDefs.phi_excl] at the durable view *)
  Lemma fs_gamma_D_excl (g : gname) (Γd : fs_dur_names) :
    phi_excl (fs_gamma_D g Γd).
  Proof.
    intros a v w. rewrite /fs_gamma_D /phi_excl /=.
    iIntros "[H1 H2]".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hv).
  Qed.

  Global Instance fs_gamma_D_timeless (g : gname) (Γd : fs_dur_names) :
    GTimeless (fs_gamma_D g Γd).
  Proof. intros a v. rewrite /fs_gamma_D /=. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b.  ONE BLOCK                                                     *)
  (* ------------------------------------------------------------------ *)

  (* A RANGE-INDEXED BIG-OP OVER A [map_seqZ] IS THE MAP'S.  This is
     [FsBlocks.big_sepM_map_seqZ] restated over a bare [Σ]: the block
     layer's copy is inside a section binding [riscvGS]/[diskGhostG]/
     [fsLogG], which a leaf about the DURABLE view has no business
     binding.  IT BELONGS IN [FsStateDefs.v] and should be relocated
     there, with [FsBlocks]' copy deleted in the same move. *)
  Lemma big_sepM_map_seqZ_gen (Phi : Z -> bv 8 -> iProp Σ) (start : Z)
      (xs : list (bv 8)) :
    ([∗ map] a ↦ v ∈ (map_seqZ start xs : gmap Z (bv 8)), Phi a v)
    ⊣⊢ ([∗ list] k ↦ v ∈ xs, Phi (start + Z.of_nat k) v).
  Proof.
    revert start. induction xs as [| x xs IH]; intros start.
    - simpl. rewrite big_sepM_empty //.
    - rewrite map_seqZ_cons big_sepM_insert; [| apply map_seqZ_cons_disjoint].
      rewrite IH big_sepL_cons.
      assert (Hz : start + Z.of_nat 0 = start) by lia. rewrite Hz.
      f_equiv. apply big_sepL_proper. intros k y _.
      assert (Hs : Z.succ start + Z.of_nat k = start + Z.of_nat (S k)) by lia.
      rewrite Hs //.
  Qed.

  (* ONE BLOCK'S ELEMENTS ARE ITS [blk_owned] *)
  Lemma blk_owned_dbelems (g : gname) (Γd : fs_dur_names) (b : Z)
      (bs : list (bv 8)) :
    length bs = BSIZE ->
    blk_owned (fs_gamma_D g Γd) b bs
    ⊣⊢ fs_dbelems g (map_seqZ (b * Z.of_nat BSIZE) bs).
  Proof.
    intros Hlen.
    rewrite /fs_dbelems big_sepM_map_seqZ_gen.
    rewrite /blk_owned /byte_range /fs_gamma_D.
    cbn [fsΦ].
    rewrite (big_sepL_proper
               (fun (k : nat) (v : bv 8) =>
                  ((b * BSIZE_z + 0 + Z.of_nat k) ↪[g] v)%I)
               (fun (k : nat) (v : bv 8) =>
                  ((b * Z.of_nat BSIZE + Z.of_nat k) ↪[g] v)%I) bs);
      last first.
    { intros k v _.
      assert (Hz : b * BSIZE_z + 0 + Z.of_nat k
                   = b * Z.of_nat BSIZE + Z.of_nat k).
      { rewrite dbytes_stride. change BSIZE_z with 1024. lia. }
      rewrite Hz //. }
    iSplit.
    - iIntros "[_ H]". iExact "H".
    - iIntros "H". iSplitR; [iPureIntro; exact Hlen | iExact "H"].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2c.  THE ONE LEMMA EVERYTHING NEEDS                                *)
  (* ------------------------------------------------------------------ *)

  (* THE TIE: the durable view's byte elements at [fs_dbytes D] ARE one
     [blk_owned] per block of [D].  This is what lets stage 2c's [P_wf]
     read [FsState.fs_state] off the flat blob [P_fs] fills [γD] with, and
     it is the only thing that ever looks inside [fs_dbytes]. *)
  Theorem fs_dbelems_dbytes (g : gname) (Γd : fs_dur_names)
      (D : gmap Z (list (bv 8))) :
    (forall b bs, D !! b = Some bs -> length bs = BSIZE) ->
    fs_dbelems g (fs_dbytes D)
    ⊣⊢ ([∗ map] b ↦ bs ∈ D, blk_owned (fs_gamma_D g Γd) b bs).
  Proof.
    induction D as [| b bs D Hb IH] using map_ind; intros Hlen.
    - rewrite fs_dbytes_empty fs_dbelems_empty big_sepM_empty //.
    - assert (Hok : dbytes_ok (<[b := bs]> D))
        by exact (dbytes_ok_full _ Hlen).
      assert (HokD : dbytes_ok D) by exact (dbytes_ok_insert D b bs Hb Hok).
      assert (Hlb : length bs = BSIZE)
        by exact (Hlen b bs (lookup_insert _ _ _)).
      assert (HlenD : forall c cs, D !! c = Some cs -> length cs = BSIZE).
      { intros c cs Hc. apply (Hlen c cs).
        rewrite lookup_insert_ne; [exact Hc |].
        intros ->. rewrite Hb in Hc. discriminate. }
      rewrite (fs_dbytes_insert D b bs Hok Hb).
      rewrite (fs_dbelems_union g _ _
                 (fs_dbytes_disj_seq D b bs HokD
                    ltac:(rewrite Hlb; reflexivity) Hb)).
      rewrite -(blk_owned_dbelems g Γd b bs Hlb).
      rewrite (IH HlenD).
      rewrite big_sepM_insert; [reflexivity | exact Hb].
  Qed.

  (* ...and the reading at [LogDefs.fs_dview], which is the shape [P_wf]'s
     body and [LogDefs.fs_dstep] are stated in *)
  Corollary fs_dview_dbytes (g : gname) (Γd : fs_dur_names)
      (D : gmap Z (list (bv 8))) :
    (forall b bs, D !! b = Some bs -> length bs = BSIZE) ->
    fs_dview g (fs_dbytes D)
    ⊣⊢ ([∗ map] b ↦ bs ∈ D, blk_owned (fs_gamma_D g Γd) b bs).
  Proof.
    intros Hlen. rewrite fs_dview_dbelems (fs_dbelems_dbytes g Γd D Hlen) //.
  Qed.

End DurBytes.

(* a big-op over a whole-disk byte map: [iFrame] must treat it as one atom
   (durable-notes.md, "a big-op behind a [Definition] is a hang") *)
Global Typeclasses Opaque fs_dbelems.
