(* ====================================================================== *)
(*  FsCollectAll.v -- THE ASSEMBLY (durable-disk lane C-8)                 *)
(*  (claude-notes/design/durable-fs-plan.md section 4, "collection at      *)
(*   quiescence"; FsCollect.v does the ARITHMETIC, this file finds the     *)
(*   pieces)                                                              *)
(*                                                                        *)
(*  [FsCollect.col_snap_ok_ex] reads [FsDurSnap.snap_ok] off               *)
(*  [FsCollect.col_hand] -- the era's pieces AS ALREADY COLLECTED.  This   *)
(*  file COLLECTS them, at ONE ghost step with the WAL's [LogDefs.ln_tx]   *)
(*  authority empty: the abstract map off [InodeRegion.ftop_inv], the      *)
(*  records off [InodeRegion.ireg_inv], the used set and the free blocks   *)
(*  off [BitmapInv.bitmap_inv], block 1 off [SbPark.sb_park], and one      *)
(*  bundle per region inum off the pool ([IcacheEscrow.ipool_quiesce_acc]) *)
(*  and the fifty slot escrows ([IcacheEscrow.ic_escrow_body_cover_all]).  *)
(*                                                                        *)
(*  THE CONCLUSION IS PURE, AND THAT IS WHAT MAKES THE ASSEMBLY POSSIBLE.  *)
(*  [pure_keep] below is the whole trick: an entailment [R |- <pure phi>]  *)
(*  yields [R |- <pure phi> * R], because a pure proposition is persistent *)
(*  and this logic is affine.  So the collection itself may be entirely    *)
(*  DESTRUCTIVE -- it may drop the overlap of two index sets, forget a     *)
(*  frame, existentially close a share -- and the caller still hands every *)
(*  invariant back untouched.  Without it every step below would owe a     *)
(*  closing wand, and the three index sets (the pool's ordinary rows, the  *)
(*  corpse ledger's markers, the fifty slots) are NOT provably disjoint:   *)
(*  the partition row is a UNION.                                         *)
(*                                                                        *)
(*  THE ONE NON-RESOURCE PREMISE is [FsCollect.col_geom] -- the boot       *)
(*  configuration's own arithmetic, witnessed at the real instance by      *)
(*  [FsCollectImg.img_col_geom].  Everything else comes off an invariant.  *)
(*                                                                        *)
(*  WHERE THE ABSTRACT STATE COMES FROM.  [InodeRegion.ftop_body] carries  *)
(*  no domain row, so "the map names exactly the region's inums" is not    *)
(*  available: the collection therefore states the snapshot at the map     *)
(*  RESTRICTED to the region ([col_reg_map]).  Every region inum is in the *)
(*  restriction (its bundle's [FsState.top_frag] says so) and nothing else *)
(*  is (by construction), which is exactly [col_hand]'s domain row; and    *)
(*  the restriction is invisible to every reader, since a reader names an  *)
(*  inum of the region.                                                    *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list sets coPset namespaces bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import invariants ghost_map.

Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types.
Require Import RiscvLang.       (* [GenId] *)
Require Import RiscvPtsto.
Require Import RiscvExtras.     (* [moi32_unsigned] *)
Require Import Xv6G.
Require Import BioDefs.
Require Import FsImg.
Require Import DinodeEnc.      (* [dinode], [diblk_wf] *)
Require Import BitmapEnc.
Require Import BlockWords.
Require Import DirView.        (* [T_DIR_z] *)
Require Import LogDefs.
Require Import FsWf.            (* [dv_of_D] *)
Require Import FsBlocks.
Require Import FsBytesGamma.
Require Import FsStateDefs.
Require Import FsStateInode.
Require Import FsStateBitmap.
Require Import FsState.
Require Import FsStateEra.
Require Import InodeRegion.
Require Import BitmapInv.
Require Import SbPark.
Require Import IcacheRef.
Require Import IcacheEscrow.
Require Import FsDurSnap.
Require Import FsCollect.
Require Import IregClean.
Require Import FsDurQuiesce.    (* [esc_ns_still_open] *)
Require Import LogSnapLaw.      (* [snap_law] -- what [log_ctx] parks *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  0.  A PURE CONCLUSION IS FREE                                          *)
(*                                                                        *)
(*  The lemma the whole file rests on: reading a PURE fact off a bundle    *)
(*  costs nothing, because [<pure phi>] is persistent and [iProp] is       *)
(*  affine.  Stated at the entailment level and not as a wand -- the wand  *)
(*  form is false, since applying it would spend the bundle.               *)
(* ====================================================================== *)

Lemma pure_keep {Σ : gFunctors} (R : iProp Σ) (φ : Prop) :
  (R ⊢ ⌜φ⌝) -> (R ⊢ ⌜φ⌝ ∗ R).
Proof.
  intros H. iIntros "R".
  iAssert (⌜φ⌝ ∧ R)%I with "[R]" as "[%Hphi HR]".
  { iSplit; [iApply (H with "R") | iExact "R"]. }
  iFrame "HR". iPureIntro. exact Hphi.
Qed.

(* ...and the wand form the proof mode applies, the entailment staying a
   COQ hypothesis: the iProp-level [(R -∗ ⌜φ⌝) -∗ R -∗ ⌜φ⌝ ∗ R] is FALSE,
   since applying the wand spends the bundle. *)
Lemma pure_keep_wand {Σ : gFunctors} (R : iProp Σ) (φ : Prop) :
  (R ⊢ ⌜φ⌝) -> R -∗ ⌜φ⌝ ∗ R.
Proof. intros H. iIntros "R". iApply (pure_keep R φ H with "R"). Qed.

(* ====================================================================== *)
(*  0a. BIG-OP PLUMBING, all in the DESTRUCTIVE direction                  *)
(* ====================================================================== *)

Section BigOps.
  Context {Σ : gFunctors}.

  (* a list's big-op covers its set: duplicates are simply dropped, which
     an affine logic allows and which is what makes the three overlapping
     index sets composable at all *)
  Lemma big_sepS_of_list `{Countable A} (l : list A) (Φ : A -> iProp Σ) :
    ([∗ list] x ∈ l, Φ x) ⊢ [∗ set] z ∈ (list_to_set l : gset A), Φ z.
  Proof.
    induction l as [| x l IH]; simpl.
    - iIntros "_". rewrite big_sepS_empty. done.
    - iIntros "[Hx Hl]". iDestruct (IH with "Hl") as "Hs".
      destruct (decide (x ∈ (list_to_set l : gset A))) as [Hin | Hnin].
      + assert (Heq : ({[x]} ∪ (list_to_set l : gset A)) = list_to_set l)
          by set_solver.
        rewrite Heq. iExact "Hs".
      + rewrite big_sepS_insert; [| exact Hnin]. iFrame "Hx Hs".
  Qed.

  (* ...and two sets' big-ops cover their union, the overlap being dropped *)
  Lemma big_sepS_union_weak `{Countable A} (X Y : gset A) (Φ : A -> iProp Σ) :
    ([∗ set] z ∈ X, Φ z) -∗ ([∗ set] z ∈ Y, Φ z) -∗ [∗ set] z ∈ X ∪ Y, Φ z.
  Proof.
    iIntros "HX HY".
    assert (Heq : X ∪ Y = X ∪ (Y ∖ X)).
    { apply set_eq. intros y. rewrite !elem_of_union elem_of_difference.
      destruct (decide (y ∈ X)); naive_solver. }
    assert (Hdj : X ## (Y ∖ X)).
    { intros y Hy1 Hy2. apply elem_of_difference in Hy2 as [_ Hn].
      exact (Hn Hy1). }
    rewrite Heq.
    rewrite (big_sepS_union Φ X (Y ∖ X) Hdj).
    iFrame "HX". iApply (big_sepS_subseteq with "HY"). set_solver.
  Qed.

End BigOps.

(* ====================================================================== *)
(*  0b. THE REGION'S INUMS, BLOCK BY BLOCK                                 *)
(*                                                                        *)
(*  [IcacheEscrow.region_inums] is a SET and [InodeRegion.ireg_body] is a  *)
(*  list of lists (sixteen slots per inode block).  These are the two      *)
(*  crossings, both in the destructive direction.                          *)
(* ====================================================================== *)

Definition blk_inums (bi : nat) : gset Z :=
  list_to_set ((fun i : nat => 16 * Z.of_nat bi + Z.of_nat i) <$> seq 0 16).

Lemma blk_inums_spec (bi : nat) (z : Z) :
  z ∈ blk_inums bi <-> 16 * Z.of_nat bi <= z < 16 * Z.of_nat bi + 16.
Proof.
  rewrite /blk_inums elem_of_list_to_set elem_of_list_fmap.
  split.
  - intros (i & -> & Hi). apply elem_of_seq in Hi. lia.
  - intros [Hlo Hhi]. exists (Z.to_nat (z - 16 * Z.of_nat bi)).
    split; [lia |]. apply elem_of_seq. lia.
Qed.

Lemma region_inums_S (n : nat) :
  region_inums (S n) = region_inums n ∪ blk_inums n.
Proof.
  apply set_eq. intros y.
  rewrite elem_of_union !region_inums_spec blk_inums_spec.
  rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma region_blk_disj (n : nat) : region_inums n ## blk_inums n.
Proof.
  intros y Hy1 Hy2.
  apply region_inums_spec in Hy1. apply blk_inums_spec in Hy2. lia.
Qed.

Section BigOpsRegion.
  Context {Σ : gFunctors}.

  Lemma nested_to_set (Ψ : Z -> iProp Σ) (nib : nat) :
    ([∗ list] bi ∈ seq 0%nat nib,
       [∗ list] i ∈ seq 0%nat 16%nat, Ψ (16 * Z.of_nat bi + Z.of_nat i))
    ⊢ [∗ set] z ∈ region_inums nib, Ψ z.
  Proof.
    induction nib as [| n IH].
    - iIntros "_". rewrite /region_inums /=. rewrite big_sepS_empty. done.
    - rewrite (seq_S n 0).
      rewrite (big_sepL_snoc
                 (fun (_ : nat) (bi : nat) =>
                    ([∗ list] i ∈ seq 0%nat 16%nat,
                       Ψ (16 * Z.of_nat bi + Z.of_nat i))%I)
                 (seq 0 n) (0 + n)%nat).
      iIntros "[Hpre Hlast]".
      iDestruct (IH with "Hpre") as "Hpre".
      rewrite region_inums_S.
      rewrite (big_sepS_union Ψ _ _ (region_blk_disj n)).
      iFrame "Hpre".
      rewrite /blk_inums.
      iApply big_sepS_of_list.
      rewrite big_sepL_fmap.
      replace (0 + n)%nat with n by lia.
      iExact "Hlast".
  Qed.

End BigOpsRegion.

(* ====================================================================== *)
(*  1.  THE THREE SUPPLIERS, EACH AS A [FsCollect.col_side]                *)
(*                                                                        *)
(*  At a quiescent [ln_tx] authority every region inum is an ORDINARY pool *)
(*  row, an [X] inum whose corpse ledger holds its marker, or the inum of  *)
(*  a LIVE slot -- [IcacheEscrow.ipool_quiesce_acc]'s partition.  Each of  *)
(*  the three yields [col_side]; the union is then [region_inums nib].     *)
(* ====================================================================== *)

Section CollectAll.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.

  (* the inum-as-a-number reading of the region's currency; the region and
     the abstract map speak [Z], the cache speaks [mword 32] *)
  Definition col_sidez (γfs : fs_names) (γi : gname) (z : Z) : iProp Σ :=
    col_side γfs γi (mword_of_int z : mword 32).

  Lemma moi_unsigned_z (z : Z) :
    0 <= z < 2 ^ 32 -> bv_unsigned (mword_of_int z : mword 32) = z.
  Proof.
    intros Hr. rewrite moi32_unsigned. apply bv_wrap_small. exact Hr.
  Qed.

  (* ---- the region's own half: records apart from slots --------------- *)

  Lemma ireg_blks_collect (γfs : fs_names) (γi : gname) (ist : Z)
      (m : gmap Z dinode) (nib : nat) :
    ([∗ list] bi ∈ seq 0%nat nib, ireg_blk γi γfs ist m bi)
    ⊢ ([∗ list] bi ∈ seq 0%nat nib,
         ∃ ds : list dinode,
           ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝ ∗ ireg_recs γfs ist bi ds)
      ∗ ([∗ set] z ∈ region_inums nib,
           ∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d).
  Proof.
    iIntros "H".
    iAssert ([∗ list] bi ∈ seq 0%nat nib,
               ((∃ ds : list dinode,
                   ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝
                   ∗ ireg_recs γfs ist bi ds)
                ∗ ([∗ list] i ∈ seq 0%nat 16%nat,
                     ∃ d : dinode,
                       ⌜m !! (16 * Z.of_nat bi + Z.of_nat i)%Z = Some d⌝
                       ∗ ireg_slot γfs γi (16 * Z.of_nat bi + Z.of_nat i) d)))%I
      with "[H]" as "H".
    { iApply (big_sepL_impl with "H"). iIntros "!>" (j bi Hj) "Hb".
      rewrite /ireg_blk.
      iDestruct "Hb" as (ds) "(%Hwf & %Hcpl & Hrecs & Hslots)".
      iSplitL "Hrecs".
      { iExists ds. iSplitR; [iPureIntro; exact Hwf |].
        iSplitR; [iPureIntro; exact Hcpl |]. iExact "Hrecs". }
      iApply (big_sepL_impl with "Hslots"). iIntros "!>" (p i Hp) "Hs".
      apply lookup_seq in Hp as [-> Hlt]. rewrite Nat.add_0_l.
      iExists (ds !!! p). iSplitR; [iPureIntro; exact (Hcpl p Hlt) |].
      iExact "Hs". }
    rewrite big_sepL_sep. iDestruct "H" as "[Hrecs Hslots]".
    iFrame "Hrecs". iApply nested_to_set. iExact "Hslots".
  Qed.

  (* ---- the pool's ordinary row, and the escrow's unloaded arm --------- *)

  Lemma ipool_shape_np_side (γfs : fs_names) (γi : gname) (cov : gset Z)
      (ls : Z) (w : mword 32) :
    ipool_shape_np γfs γi cov ls w ⊢ col_side γfs γi w.
  Proof.
    rewrite /ipool_shape_np /col_side.
    iIntros "[Halloc | (Hmk & _ & _)]".
    - rewrite /ipool_alloc.
      iDestruct "Halloc" as (dn0 bm0 data0)
        "(%Hok & %Hdok & %Hddix & %Hdoc & _ & Hdl & Hn & _ & _)".
      rewrite /dlinks. iDestruct "Hdl" as "[_ Hte]".
      iRight. iExists (era_node dn0 bm0 data0), (DfracOwn 1).
      iSplitR;
        [iPureIntro; exact (FsStateDefs.dfrac_full_nvalid (DfracOwn 1)) |].
      (* the pool row carries the three directory clauses already
         (durable-disk lane E-clauses); the node is [era_node] of its
         triple, so the transport is one lemma *)
      iSplitR.
      { iPureIntro.
        exact (FsStateEra.node_dir_local_of_ok (bv_unsigned w) cov ls
                 icfg_nib dn0 bm0 data0 Hok Hdok Hddix Hdoc). }
      rewrite -inode_owned_era_1. iFrame "Hn Hte".
    - iLeft. iExact "Hmk".
  Qed.

  Lemma ipool_ord_side (γfs : fs_names) (γi : gname) (cov : gset Z)
      (ls : Z) (w : mword 32) :
    ipool_ord γfs γi cov ls w ⊢ col_side γfs γi w.
  Proof.
    rewrite /ipool_ord. iIntros "(_ & _ & Hnp & _)".
    iApply (ipool_shape_np_side with "Hnp").
  Qed.

  Lemma ipool_rows_side (γfs : fs_names) (γi : gname) (cov : gset Z)
      (ls : Z) (O : gset Z) :
    ipool_rows γfs γi cov ls O ⊢ [∗ set] z ∈ O, col_sidez γfs γi z.
  Proof.
    rewrite /ipool_rows. iIntros "H".
    iApply (big_sepS_impl with "H"). iIntros "!>" (z Hz) "Hr".
    rewrite /col_sidez. iApply (ipool_ord_side with "Hr").
  Qed.

  (* ---- the corpse ledger's markers ----------------------------------- *)

  Lemma imarks_side (γfs : fs_names) (γi : gname) (X : gset Z) :
    (forall z : Z, z ∈ X -> 0 <= z < 2 ^ 32) ->
    ([∗ set] z ∈ X, imark γi z) ⊢ [∗ set] z ∈ X, col_sidez γfs γi z.
  Proof.
    intros Hr. iIntros "H".
    iApply (big_sepS_impl with "H"). iIntros "!>" (z Hz) "Hm".
    rewrite /col_sidez /col_side. iLeft.
    rewrite (moi_unsigned_z z (Hr z Hz)). iExact "Hm".
  Qed.


  (* ---- the fifty slot escrows --------------------------------------- *)

  (* ONE SLOT.  [IcacheEscrow.ic_slot_cover]'s three alternatives at a LIVE
     slot: the first is refuted by the pool's own quarter of the identity
     cell ([IcacheEscrow.ic_id_agree] -- the slot cannot be dead and live at
     once), and the other two ARE the two arms of [FsCollect.col_side].  The
     lend's frame and its closing wand are dropped: the collection is
     destructive and [pure_keep] gives the escrow back regardless. *)
  Lemma ic_slot_cover_side (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (ls : Z) (k : nat) (dev inum : mword 32) :
    ic_id cn k (1/4) true dev inum -∗
    ic_slot_cover cn γfs γi cov ls k -∗
    col_side γfs γi inum.
  Proof.
    iIntros "Hq Hc".
    iDestruct "Hc" as (dev' inum') "[Ha | [Hb | Hc]]".
    - rewrite /ic_lend. iDestruct "Ha" as "[Hid _]".
      iDestruct (ic_id_agree with "Hq Hid") as %(Hv & _ & _). discriminate.
    - rewrite /ic_lend. iDestruct "Hb" as "[[Hid Hnp] _]".
      iDestruct (ic_id_agree with "Hq Hid") as %(_ & _ & <-).
      iApply (ipool_shape_np_side with "Hnp").
    - iDestruct "Hc" as (dq n) "[%Hdq [%Hdl Hl]]".
      rewrite /ic_lend. iDestruct "Hl" as "[(Hid & Hn & Hte) _]".
      iDestruct (ic_id_agree with "Hq Hid") as %(_ & _ & <-).
      rewrite /col_side. iRight. iExists n, dq.
      iSplitR; [iPureIntro; exact Hdq |].
      iSplitR; [iPureIntro; exact Hdl |]. iFrame "Hn Hte".
  Qed.

  Lemma ic_live_inums_cons_true (dev inum : mword 32)
      (ids : list (bool * mword 32 * mword 32)) :
    ic_live_inums ((true, dev, inum) :: ids)
    = {[ bv_unsigned inum ]} ∪ ic_live_inums ids.
  Proof. rewrite /ic_live_inums /=. done. Qed.

  Lemma ic_live_inums_cons_false (dev inum : mword 32)
      (ids : list (bool * mword 32 * mword 32)) :
    ic_live_inums ((false, dev, inum) :: ids) = ic_live_inums ids.
  Proof. rewrite /ic_live_inums /=. done. Qed.

  (* ...AND OVER THE FIFTY, reindexed onto the INUMS the pool's partition
     names.  The offset [o] is generalized because the induction walks the
     identity list while the covers are indexed by slot. *)
  Lemma esc_covers_live (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (ls : Z) (o : nat)
      (ids : list (bool * mword 32 * mword 32)) :
    ([∗ list] k ↦ p ∈ ids,
       (ic_id cn (o + k) (1/4) p.1.1 p.1.2 p.2
        ∗ ic_slot_cover cn γfs γi cov ls (o + k)))
    ⊢ [∗ set] z ∈ ic_live_inums ids, col_sidez γfs γi z.
  Proof.
    revert o. induction ids as [| p ids IH]; intros o.
    - iIntros "_". rewrite /ic_live_inums /=. rewrite big_sepS_empty. done.
    - rewrite big_sepL_cons. iIntros "[Hhd Htl]".
      iAssert ([∗ set] z ∈ ic_live_inums ids, col_sidez γfs γi z)%I
        with "[Htl]" as "Hset".
      { iApply (IH (S o)). iApply (big_sepL_impl with "Htl").
        iIntros "!>" (j y Hj) "H".
        replace (S o + j)%nat with (o + S j)%nat by lia. iExact "H". }
      destruct p as [[v dev] inum].
      destruct v.
      + rewrite ic_live_inums_cons_true.
        destruct (decide (bv_unsigned inum ∈ ic_live_inums ids)) as [Hin | Hnin].
        * assert (Heq : {[ bv_unsigned inum ]} ∪ ic_live_inums ids
                        = ic_live_inums ids) by set_solver.
          rewrite Heq. iExact "Hset".
        * rewrite big_sepS_insert; [| exact Hnin].
          iFrame "Hset". rewrite /col_sidez ipl_moi_inum.
          iDestruct "Hhd" as "[Hid Hcov]". cbn [fst snd].
          rewrite Nat.add_0_r.
          iApply (ic_slot_cover_side with "Hid Hcov").
      + rewrite ic_live_inums_cons_false. iExact "Hset".
  Qed.


  (* the per-slot cover, threaded over a LIST of slots -- [ic_escrows] is a
     [big_sepL] and [IcacheEscrow.ic_escrow_body_cover_all] is stated over a
     [gset nat]; the [ln_tx] authority cannot be distributed over a big-op,
     so the threading is an induction either way *)
  Lemma ic_escrow_body_cover_list (l : list nat) (cn : ic_names)
      (γfs : fs_names) (γi : gname) (cov : gset Z) (ls : Z) :
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ([∗ list] k ∈ l, ic_escrow_body cn γfs γi cov ls k) -∗
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
    ∗ ([∗ list] k ∈ l, ic_slot_cover cn γfs γi cov ls k).
  Proof.
    induction l as [| k l IH].
    - iIntros "Ha _". iFrame "Ha". done.
    - iIntros "Ha Hl". rewrite !big_sepL_cons.
      iDestruct "Hl" as "[Hk Hrest]".
      iDestruct (ic_escrow_body_cover with "Ha Hk") as "[Ha Hck]".
      iDestruct (IH with "Ha Hrest") as "[Ha Hrest]".
      iFrame "Ha Hck Hrest".
  Qed.

  (* a [seq]-indexed big-op re-read at a list of the same length *)
  Lemma big_sepL_seq_of_list {A : Type} (l : list A) (P : nat -> iProp Σ)
      (o : nat) :
    ([∗ list] k ∈ seq o (length l), P k) ⊢ [∗ list] k ↦ _ ∈ l, P (o + k)%nat.
  Proof.
    revert o. induction l as [| x l IH]; intros o.
    - iIntros "_". done.
    - cbn [length seq].
      rewrite !big_sepL_cons.
      iIntros "[Hh Ht]". rewrite Nat.add_0_r. iFrame "Hh".
      iDestruct (IH (S o) with "Ht") as "Ht".
      iApply (big_sepL_impl with "Ht"). iIntros "!>" (j y Hj) "H".
      replace (o + S j)%nat with (S o + j)%nat by lia. iExact "H".
  Qed.

  (* ---- one inum's bundle, and the fifty-fold threading --------------- *)

  (* the door at an inum named as a NUMBER: the region and the abstract map
     are keyed by [Z], the cache by [mword 32], and the equation between
     them is what the collection carries ([moi_unsigned_z] at every region
     inum, by [FsCollect.cg_wide]). *)
  Lemma col_region_quiesce_take_z (γfs : fs_names) (γi : gname) (z : Z)
      (w : mword 32) (d : dinode) :
    bv_unsigned w = z ->
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    col_side γfs γi w -∗
    ireg_slot γfs γi z d -∗
      ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
      ∗ ireg_lnk γfs z d
      ∗ ∃ (n : fs_node) (dq : dfrac),
          ⌜~ ✓ (dq ⋅ dq)⌝
          ∗ ⌜node_dir_local z icfg_nib n⌝
          ∗ inode_owned_era_q γfs dq γi w n
          ∗ ent_toks_x (fs_gamma_L γfs) z n.
  Proof.
    intros <-. iIntros "Ht Hs Hr".
    iApply (col_region_quiesce_take with "Ht Hs Hr").
  Qed.

  Lemma col_sides_bundles (γfs : fs_names) (γi : gname)
      (m : gmap Z dinode) (I : gmap Z fs_node) (Rs : gset Z) :
    (forall z : Z, z ∈ Rs -> 0 <= z < 2 ^ 32) ->
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ghost_map_auth γi 1 m -∗
    ghost_map_auth (fs_top γfs) 1 I -∗
    ([∗ set] z ∈ Rs, (col_sidez γfs γi z
                      ∗ ∃ d : dinode, ⌜m !! z = Some d⌝
                                      ∗ ireg_slot γfs γi z d)) -∗
      ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
      ∗ ghost_map_auth γi 1 m
      ∗ ghost_map_auth (fs_top γfs) 1 I
      ∗ ([∗ set] z ∈ Rs,
           (∃ n : fs_node,
              ⌜I !! z = Some n⌝
              ∗ ⌜node_dir_local z icfg_nib n⌝
              ∗ col_bundle γfs γi z n
              ∗ fs_link_node (fs_link γfs) z n)
           (* the region's keep-alive token, [emp] everywhere but the root
              (durable-disk lane E-clauses).  [FsCollect.col_link_of] has
              always produced it; KEEPING it is what supplies
              [FsCollect.col_hand]'s last row, hence the SLACK in
              [FsDurSnap.sk_links].  It rides OUTSIDE the existential so
              that [big_sepS_sep] splits it off as its own column. *)
           ∗ ∃ kv : ity, ireg_keep γfs z kv).
  Proof.
    induction Rs as [| z Rs Hnz IH] using set_ind_L; intros Hr.
    - iIntros "Ht Hm Hi _". rewrite !big_sepS_empty.
      iFrame "Ht Hm Hi"; try done.
    - iIntros "Ht Hm Hi H".
      rewrite !big_sepS_insert; [| exact Hnz | exact Hnz].
      iDestruct "H" as "[[Hside (%d & %Hmd & Hslot)] Hrest]".
      iDestruct (IH with "Ht Hm Hi Hrest") as "(Ht & Hm & Hi & Hrest)".
      { intros y Hy. apply Hr. set_solver. }
      iFrame "Hrest".
      assert (Hzr : 0 <= z < 2 ^ 32) by (apply Hr; set_solver).
      pose proof (moi_unsigned_z z Hzr) as Hmoi.
      rewrite /col_sidez.
      iDestruct (col_region_quiesce_take_z γfs γi z (mword_of_int z) d Hmoi
                   with "Ht Hside Hslot") as
        "(Ht & Hlnk & %n & %dq & %Hdq & %Hdl & Hown & Hte)".
      iDestruct (col_bundle_of_side γfs γi (mword_of_int z : mword 32) n dq
                   Hdq with "Hown") as "Hb".
      rewrite Hmoi.
      (* the abstract map's value at this inum IS the bundle's node, and the
         record the bundle names IS the region's *)
      iDestruct (col_bundle_top with "Hi Hb") as %HIz.
      iDestruct (col_bundle_rec with "Hm Hb") as %Hmz.
      rewrite Hmd in Hmz. injection Hmz as Hrec.
      iFrame "Ht Hm Hi".
      iDestruct (col_link_of γfs z n d (eq_sym Hrec) with "Hlnk Hte")
        as "[Hle Hkp]".
      iSplitR "Hkp"; [| iExact "Hkp"].
      iExists n. iSplitR; [iPureIntro; exact HIz |].
      iSplitR; [iPureIntro; exact Hdl |]. iFrame "Hb Hle".
  Qed.

  (* ...and the ONE token that survives the collection: [ireg_keep] is [emp]
     at every inum but the root, so the column's whole content is the root's
     keep-alive fragment (durable-disk lane E-clauses). *)
  Lemma col_keeps_root (γfs : fs_names) (nib : nat) :
    ireg_root ∈ region_inums nib ->
    ([∗ set] z ∈ region_inums nib, ∃ kv : ity, ireg_keep γfs z kv) -∗
    ∃ kv : ity, ireg_keep γfs ireg_root kv.
  Proof.
    intros Hin. iIntros "H".
    rewrite (big_sepS_delete _ (region_inums nib) ireg_root Hin).
    iDestruct "H" as "[$ _]".
  Qed.


  (* THE ABSTRACT MAP, RESTRICTED TO THE REGION.  [InodeRegion.ftop_body]
     carries no domain row, so "the map names exactly the region's inums" is
     not available; the snapshot is therefore stated at the restriction,
     whose domain IS the region (every region inum's bundle carries that
     inum's [FsState.top_frag]) and which agrees with the map at every inum
     any reader can name. *)
  Definition col_reg_map (nib : nat) (I : gmap Z fs_node) : gmap Z fs_node :=
    base.filter (fun kv : Z * fs_node => kv.1 ∈ region_inums nib) I.

  Lemma col_reg_map_lookup (nib : nat) (I : gmap Z fs_node) (z : Z)
      (n : fs_node) :
    col_reg_map nib I !! z = Some n <->
    (I !! z = Some n /\ z ∈ region_inums nib).
  Proof. rewrite /col_reg_map map_lookup_filter_Some. done. Qed.

  Lemma col_reg_map_dom (nib : nat) (I : gmap Z fs_node) :
    region_inums nib ⊆ dom I ->
    dom (col_reg_map nib I) = region_inums nib.
  Proof.
    intros Hsub. apply set_eq. intros z. rewrite elem_of_dom.
    split.
    - intros [n Hn]. apply col_reg_map_lookup in Hn as [_ Hz]. exact Hz.
    - intros Hz. destruct (proj1 (elem_of_dom I z) (Hsub z Hz)) as [n Hn].
      exists n. apply col_reg_map_lookup. split; [exact Hn | exact Hz].
  Qed.

  (* ==================================================================== *)
  (*  2.  THE COLLECTION, DESTRUCTIVELY                                    *)
  (* ==================================================================== *)

  Lemma col_bundles_domsub γfs (γi : gname) (Rs : gset Z)
      (I : gmap Z fs_node) :
    ([∗ set] z ∈ Rs,
       ∃ n : fs_node,
         ⌜I !! z = Some n⌝ ∗ ⌜node_dir_local z icfg_nib n⌝
         ∗ col_bundle γfs γi z n
         ∗ fs_link_node (fs_link γfs) z n)
    ⊢ ⌜Rs ⊆ dom I⌝.
  Proof.
    induction Rs as [| z Rs Hnz IH] using set_ind_L.
    - iIntros "_". iPureIntro. set_solver.
    - rewrite big_sepS_insert; [| exact Hnz].
      iIntros "[(%n & %Hn & _) Hrest]".
      iDestruct (IH with "Hrest") as %Hsub.
      iPureIntro. intros y Hy.
      apply elem_of_union in Hy as [Hy | Hy].
      + apply elem_of_singleton in Hy as ->.
        apply elem_of_dom. by eexists.
      + exact (Hsub y Hy).
  Qed.

  (* ...and the same reading for the DIRECTORY clauses the sides brought
     out (durable-disk lane E-clauses): a whole-map pure row is what
     [FsCollect.col_hand]'s last conjunct wants, and the per-inum facts
     compose into it exactly as the domain row does. *)
  Lemma col_bundles_dirloc γfs (γi : gname) (Rs : gset Z)
      (I : gmap Z fs_node) :
    ([∗ set] z ∈ Rs,
       ∃ n : fs_node,
         ⌜I !! z = Some n⌝ ∗ ⌜node_dir_local z icfg_nib n⌝
         ∗ col_bundle γfs γi z n
         ∗ fs_link_node (fs_link γfs) z n)
    ⊢ ⌜forall (i : Z) (n : fs_node),
         i ∈ Rs -> I !! i = Some n -> node_dir_local i icfg_nib n⌝.
  Proof.
    induction Rs as [| z Rs Hnz IH] using set_ind_L.
    - iIntros "_". iPureIntro. intros i n Hi. set_solver.
    - rewrite big_sepS_insert; [| exact Hnz].
      iIntros "[(%n & %Hn & %Hdl & _) Hrest]".
      iDestruct (IH with "Hrest") as %Hall.
      iPureIntro. intros i x Hi Hix.
      apply elem_of_union in Hi as [Hi | Hi].
      + apply elem_of_singleton in Hi as ->.
        rewrite Hn in Hix. injection Hix as <-. exact Hdl.
      + exact (Hall i x Hi Hix).
  Qed.

  (* THE CORE.  Everything on the left is CONSUMED -- the caller gets it all
     back through [pure_keep], because what comes out is pure. *)
  Lemma col_bodies_snap_ok
      (cn : ic_names) (γfs : fs_names) (γi : gname) (cov : gset Z) (ls : Z)
      (nib : nat) (sb : fs_sb) (sbb : list (bv 8)) (used : gset Z)
      (m : gmap Z dinode) (I : gmap Z fs_node) (O X : gset Z)
      (ids : list (bool * mword 32 * mword 32))
      (Lb : gmap Z (bv 8)) (C : gmap Z (list (bv 8))) :
    col_geom sb (FsImg.sb_inodestart sb) nib (fs_home_set cov ls) ->
    region_inums nib = O ∪ X ∪ ic_live_inums ids ->
    length ids = NINODE ->
    fs_parse_sb (fun _ => sbb) = Some sb ->
    (ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
     ∗ col_auth γfs Lb C (fs_home_set cov ls)
     ∗ ghost_map_auth (fs_top γfs) 1 I
     ∗ ghost_map_auth γi 1 m
     ∗ ([∗ list] bi ∈ seq 0%nat nib, ireg_blk γi γfs (FsImg.sb_inodestart sb) m bi)
     ∗ bitmap_res γfs (FsImg.sb_bmapstart sb) (FsImg.sb_size sb) used
     ∗ fsblock (fs_bytes γfs) SB_BNO sbb
     ∗ ipool_rows γfs γi cov ls O
     ∗ ([∗ set] z ∈ X, imark γi z)
     ∗ ic_ids cn ids
     ∗ ([∗ list] k ∈ seq 0%nat NINODE, ic_escrow_body cn γfs γi cov ls k))
    ⊢ ⌜exists S : fs_state_rec,
         snap_ok S (col_view C (fs_home_set cov ls))⌝.
  Proof.
    intros Hgeom Hrow Hlen Hparse.
    assert (Hwide : forall z : Z, z ∈ region_inums nib -> 0 <= z < 2 ^ 32).
    { intros z Hz. apply region_inums_spec in Hz.
      pose proof (cg_wide Hgeom) as Hw. lia. }
    iIntros "(Htx & Hauth & Hi & Hm & Hblks & Hbm & Hsbb & Hpool & Hmks
              & Hids & Hesc)".
    iDestruct (ireg_blks_collect with "Hblks") as "[Hrecs Hslots]".
    (* ---- the three suppliers, each a [col_sidez] ---- *)
    iDestruct (ipool_rows_side with "Hpool") as "HO".
    iDestruct (imarks_side γfs γi X with "Hmks") as "HX".
    { intros z Hz. apply Hwide. rewrite Hrow. set_solver. }
    iDestruct (ic_escrow_body_cover_list with "Htx Hesc") as "[Htx Hcovs]".
    rewrite -Hlen.
    iDestruct (big_sepL_seq_of_list ids _ 0%nat with "Hcovs") as "Hcovs".
    iAssert ([∗ list] k ↦ p ∈ ids,
               (ic_id cn (0 + k)%nat (1/4) p.1.1 p.1.2 p.2
                ∗ ic_slot_cover cn γfs γi cov ls (0 + k)%nat))%I
      with "[Hids Hcovs]" as "Hzip".
    { rewrite big_sepL_sep. iSplitR "Hcovs"; [| iExact "Hcovs"].
      iApply (big_sepL_impl with "Hids"). iIntros "!>" (k p Hk) "H".
      rewrite Nat.add_0_l. iExact "H". }
    iDestruct (esc_covers_live cn γfs γi cov ls 0%nat ids with "Hzip") as "HL".
    (* ---- their union IS the region ---- *)
    iDestruct (big_sepS_union_weak with "HO HX") as "HOX".
    iDestruct (big_sepS_union_weak with "HOX HL") as "HR".
    rewrite -Hrow.
    (* ---- zip with the region's slots, and turn each pair into a bundle -- *)
    iAssert ([∗ set] z ∈ region_inums nib,
               (col_sidez γfs γi z
                ∗ ∃ d : dinode, ⌜m !! z = Some d⌝
                                ∗ ireg_slot γfs γi z d))%I
      with "[HR Hslots]" as "HR".
    { rewrite big_sepS_sep. iFrame "HR Hslots". }
    iDestruct (col_sides_bundles γfs γi m I (region_inums nib) Hwide
                 with "Htx Hm Hi HR") as "(Htx & Hm & Hi & HB)".
    (* ---- the keep-alive column comes off, and only the root's is not
       [emp] (durable-disk lane E-clauses) ---- *)
    assert (Hrootin : ireg_root ∈ region_inums nib).
    { apply region_inums_spec.
      pose proof (sbo_ninodes sb (cg_sbok Hgeom)).
      pose proof (cg_nin Hgeom).
      unfold ireg_root, FsImg.ROOTINO in *. lia. }
    rewrite big_sepS_sep. iDestruct "HB" as "[HB Hkeeps]".
    iDestruct (col_keeps_root γfs nib Hrootin with "Hkeeps") as "Hkeep".
    iDestruct (col_bundles_domsub with "HB") as %Hdom.
    iDestruct (col_bundles_dirloc with "HB") as %Hdirl.
    (* ---- the abstract state is the map RESTRICTED to the region ---- *)
    assert (HdomIq : dom (col_reg_map nib I) = region_inums nib)
      by exact (col_reg_map_dom nib I Hdom).
    rewrite -HdomIq -big_sepM_dom.
    iAssert (([∗ map] i ↦ n ∈ col_reg_map nib I, col_bundle γfs γi i n)
             ∗ fs_links (fs_link γfs) (col_reg_map nib I))%I
      with "[HB]" as "[Hbund Hlnks]".
    { rewrite /fs_links -big_sepM_sep.
      iApply (big_sepM_impl with "HB").
      iIntros "!>" (i x Hix) "(%n & %Hn & %Hdl & Hb & Hl)".
      apply col_reg_map_lookup in Hix as [HI _].
      rewrite HI in Hn. injection Hn as Hnx. subst x.
      iFrame "Hb Hl". }
    (* ---- and that IS [FsCollect.col_hand] ---- *)
    iAssert (col_hand γfs γi (FsImg.sb_inodestart sb) nib sb sbb used
               (col_reg_map nib I) m Lb C (fs_home_set cov ls))%I
      with "[Hauth Hsbb Hbm Hm Hrecs Hbund Hlnks Hkeep]" as "Hhand".
    { rewrite /col_hand.
      iSplitR; [iPureIntro; exact Hgeom |].
      iSplitR.
      { iPureIntro. intros i. rewrite HdomIq. apply region_inums_spec. }
      iFrame "Hauth".
      iSplitL "Hsbb".
      { rewrite /sb_owned gamma_blk_owned.
        iSplitL "Hsbb"; [iExact "Hsbb" | iPureIntro; exact Hparse]. }
      iSplitL "Hbm"; [iExact "Hbm" |].
      iSplitL "Hm Hrecs".
      { rewrite /col_recs. iFrame "Hm Hrecs". }
      iFrame "Hbund Hlnks Hkeep".
      (* the last row: the per-inum directory clauses, at the RESTRICTED
         map (durable-disk lane E-clauses) *)
      iPureIntro. intros i n Hi.
      apply col_reg_map_lookup in Hi as [HI Hz].
      exact (Hdirl i n Hz HI). }
    iDestruct (col_snap_ok_ex with "Hhand") as %Hok.
    iPureIntro. exact Hok.
  Qed.


  (* ==================================================================== *)
  (*  3.  OPENING THE FIFTY ESCROWS AT ONE GHOST STEP                      *)
  (*                                                                      *)
  (*  [inv N P] opens ONCE per namespace ([FsDurQuiesce.ns_not_reopenable]) *)
  (*  which is why the family sits at [icEscN .@ k]; the induction that     *)
  (*  works is [FsDurQuiesce.esc_ns_still_open], and the mask it leaves is  *)
  (*  the union of the slots' own namespaces, not [↑icEscN].               *)
  (* ==================================================================== *)

  Definition esc_ns (ks : list nat) : coPset :=
    ⋃ ((fun k : nat => (↑(icEscN .@ k) : coPset)) <$> ks).

  Lemma esc_ns_sub (ks : list nat) : esc_ns ks ⊆ (↑icEscN : coPset).
  Proof.
    induction ks as [| k ks IH]; rewrite /esc_ns /=.
    - apply empty_subseteq.
    - apply union_least; [apply ic_escrow_ns_sub | exact IH].
  Qed.

  Lemma esc_ns_cons (k : nat) (ks : list nat) :
    esc_ns (k :: ks) = (↑(icEscN .@ k) : coPset) ∪ esc_ns ks.
  Proof. rewrite /esc_ns /=. done. Qed.

  Lemma esc_ns_still (k : nat) (ks : list nat) (E : coPset) :
    k ∉ ks -> esc_ns ks ⊆ E -> esc_ns ks ⊆ E ∖ ↑(icEscN .@ k).
  Proof.
    intros Hk. revert E. induction ks as [| j ks IH]; intros E Hsub.
    - rewrite /esc_ns /=. apply empty_subseteq.
    - rewrite esc_ns_cons in Hsub. rewrite esc_ns_cons.
      apply not_elem_of_cons in Hk as [Hjk Hks].
      apply union_least.
      + apply esc_ns_still_open; [exact Hjk |].
        etrans; [| exact Hsub]. apply union_subseteq_l.
      + apply IH; [exact Hks |]. etrans; [| exact Hsub].
        apply union_subseteq_r.
  Qed.

  (* "no slot appears twice", in the shape the induction consumes -- stated
     here rather than as [NoDup] because [Stdlib.Lists.List] and [stdpp] both
     export a [NoDup_cons] and the two are different lemmas. *)
  Fixpoint ks_ok (ks : list nat) : Prop :=
    match ks with
    | [] => True
    | k :: ks' => k ∉ ks' /\ ks_ok ks'
    end.

  Lemma ks_ok_seq (n o : nat) : ks_ok (seq o n).
  Proof.
    revert o. induction n as [| n IH]; intros o; [exact I |].
    cbn [seq ks_ok]. split; [| exact (IH (S o))].
    intros Hin. apply elem_of_seq in Hin. lia.
  Qed.

  Lemma ic_escrows_open_list (ks : list nat) (E : coPset) (cn : ic_names)
      (γfs : fs_names) (γi : gname) (cov : gset Z) (ls : Z) :
    ks_ok ks ->
    esc_ns ks ⊆ E ->
    ([∗ list] k ∈ ks, ic_escrow cn γfs γi cov ls k) -∗
    |={E, E ∖ esc_ns ks}=>
      ([∗ list] k ∈ ks, ic_escrow_body cn γfs γi cov ls k)
      ∗ (([∗ list] k ∈ ks, ic_escrow_body cn γfs γi cov ls k)
           ={E ∖ esc_ns ks, E}=∗ True).
  Proof.
    revert E. induction ks as [| k ks IH]; intros E Hnd Hsub.
    - iIntros "_". rewrite /esc_ns /= difference_empty_L.
      iApply fupd_mask_intro; [set_solver |]. iIntros "Hcl".
      iSplitR; [done |].
      iIntros "_". iMod "Hcl". done.
    - destruct Hnd as [Hk Hnd].
      rewrite esc_ns_cons in Hsub.
      assert (Hk1 : (↑(icEscN .@ k) : coPset) ⊆ E)
        by (etrans; [| exact Hsub]; apply union_subseteq_l).
      assert (Hks : esc_ns ks ⊆ E)
        by (etrans; [| exact Hsub]; apply union_subseteq_r).
      iIntros "Hl". rewrite !big_sepL_cons.
      iDestruct "Hl" as "[#Hk Hrest]".
      iMod (inv_acc E (icEscN .@ k) with "Hk") as "[Hbody Hclk]";
        [exact Hk1 |].
      iDestruct "Hbody" as ">Hbody".
      iMod (IH (E ∖ ↑(icEscN .@ k)) Hnd
              (esc_ns_still k ks E Hk Hks) with "Hrest") as "[Hbodies Hclr]".
      rewrite esc_ns_cons.
      rewrite (difference_difference_l_L E (↑(icEscN .@ k)) (esc_ns ks)).
      iModIntro. iFrame "Hbody Hbodies".
      iIntros "[Hbody Hbodies]".
      rewrite -(difference_difference_l_L E (↑(icEscN .@ k)) (esc_ns ks)).
      iMod ("Hclr" with "Hbodies") as "_".
      iMod ("Hclk" with "[Hbody]") as "_"; [iNext; iExact "Hbody" |].
      done.
  Qed.


  (* ==================================================================== *)
  (*  4.  THE ASSEMBLY                                                     *)
  (*                                                                      *)
  (*  ONE ghost step.  Six invariant families are opened -- [ftopN],       *)
  (*  [iregN], [bitmapN], [sbN], [ipoolN] and the fifty [icEscN .@ k] --   *)
  (*  the collection runs destructively inside [pure_keep], and every one  *)
  (*  of them closes with the body it was opened with.  The byte authority *)
  (*  is the CALLER's: [logN] is open at the commit, which is the whole    *)
  (*  reason this lemma takes [col_auth] rather than [fs_bytes_inv].       *)
  (* ==================================================================== *)

  Lemma fs_collect_snap_ok (E : coPset) (cn : ic_names)
      (γfs : fs_names) (γi : gname) (cov : gset Z) (ls : Z) (nib : nat)
      (sb : fs_sb) (Lb : gmap Z (bv 8)) (C : gmap Z (list (bv 8))) :
    col_geom sb (FsImg.sb_inodestart sb) nib (fs_home_set cov ls) ->
    ↑ftopN ⊆ E -> ↑iregN ⊆ E -> ↑bitmapN ⊆ E -> ↑sbN ⊆ E ->
    ↑ipoolN ⊆ E -> ↑icEscN ⊆ E ->
    ireg_inv γi γfs (FsImg.sb_inodestart sb) nib -∗
    bitmap_inv γfs (FsImg.sb_bmapstart sb) cov ls (FsImg.sb_size sb) -∗
    ic_escrows cn γfs γi cov ls -∗
    ipool_inv cn γfs γi cov ls nib -∗
    sb_park γfs sb -∗
    col_auth γfs Lb C (fs_home_set cov ls) -∗
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) ={E}=∗
      ⌜exists S : fs_state_rec, snap_ok S (col_view C (fs_home_set cov ls))⌝
      ∗ col_auth γfs Lb C (fs_home_set cov ls)
      ∗ ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit).
  Proof.
    intros Hgeom Hft Hir Hbmn Hsbn Hipn Hien.
    iIntros "#Hireg #Hbmi #Hesc #Hpool #Hpark Hauth Htx".
    iDestruct "Hireg" as "(#Hiregi & _ & #Hftop)".
    iDestruct "Hbmi" as "(#Hbmb & _)".
    (* ---- 1. the abstract map's authority ---- *)
    iMod (inv_acc E ftopN with "Hftop") as "[Hfb Hclft]"; [exact Hft |].
    iDestruct "Hfb" as ">Hfb".
    iDestruct "Hfb" as (I A) "(Hta & Hlk & Hpk & %Hclean)".
    (* ---- 2. the region ---- *)
    iMod (inv_acc (E ∖ ↑ftopN) iregN with "Hiregi") as "[Hib Hclir]";
      [solve_ndisj |].
    iDestruct "Hib" as ">Hib".
    iDestruct "Hib" as (m) "(Hma & Hblks & Hreg)".
    (* ---- 3. the bitmap ---- *)
    iMod (inv_acc (E ∖ ↑ftopN ∖ ↑iregN) bitmapN with "Hbmb")
      as "[Hbb Hclbm]"; [solve_ndisj |].
    iDestruct "Hbb" as ">Hbb". iDestruct "Hbb" as (used) "Hbres".
    (* ---- 4. block 1 ---- *)
    iMod (sb_park_acc (E ∖ ↑ftopN ∖ ↑iregN ∖ ↑bitmapN) γfs sb with "Hpark")
      as (sbb) "(%Hparse & Hsbb & Hclsb)"; [solve_ndisj |].
    (* ---- 5. the pool, at a quiescent ledger ---- *)
    iMod (ipool_quiesce_acc (E ∖ ↑ftopN ∖ ↑iregN ∖ ↑bitmapN ∖ ↑sbN)
            cn γfs γi cov ls nib with "Hpool Htx")
      as (O X ids) "(%Hlen & %Hrow & Htx & Hrows & Hids & Hmks & Hclp)";
      [solve_ndisj |].
    (* ---- 6. the fifty escrows ---- *)
    assert (Hsube : esc_ns (seq 0%nat NINODE)
                    ⊆ E ∖ ↑ftopN ∖ ↑iregN ∖ ↑bitmapN ∖ ↑sbN ∖ ↑ipoolN).
    { etrans; [apply esc_ns_sub |]. solve_ndisj. }
    iMod (ic_escrows_open_list (seq 0%nat NINODE) _ cn γfs γi cov ls
            (ks_ok_seq NINODE 0%nat) Hsube with "Hesc")
      as "[Hbodies Hcle]".
    (* ---- THE COLLECTION, and it gives everything back ---- *)
    iDestruct (pure_keep_wand _ _
                 (col_bodies_snap_ok cn γfs γi cov ls nib sb sbb used m I O X
                    ids Lb C Hgeom Hrow Hlen Hparse)
                 with "[$Htx $Hauth $Hta $Hma $Hblks $Hbres $Hsbb $Hrows
                        $Hmks $Hids $Hbodies]")
      as "(%Hok & Htx & Hauth & Hta & Hma & Hblks & Hbres & Hsbb & Hrows
           & Hmks & Hids & Hbodies)".
    (* ---- and every invariant closes with the body it was opened with --- *)
    iMod ("Hcle" with "Hbodies") as "_".
    iMod ("Hclp" with "[$Hrows $Hids $Hmks]") as "_".
    iMod ("Hclsb" with "Hsbb") as "_".
    iMod ("Hclbm" with "[Hbres]") as "_".
    { iNext. rewrite /bitmap_body. iExists used. iExact "Hbres". }
    iMod ("Hclir" with "[Hma Hblks Hreg]") as "_".
    { iNext. rewrite /ireg_body. iExists m. iFrame "Hma Hblks Hreg". }
    iMod ("Hclft" with "[Hta Hlk Hpk]") as "_".
    { iNext. rewrite /ftop_body. iExists I, A. iFrame "Hta Hlk Hpk".
      iPureIntro. exact Hclean. }
    iModIntro. iFrame "Hauth Htx". iPureIntro. exact Hok.
  Qed.


  (* ==================================================================== *)
  (*  5.  THE LAW, DISCHARGED                                              *)
  (*                                                                      *)
  (*  [LogSnapLaw.snap_law] is what [LogInv.log_ctx] parks and the commit  *)
  (*  runs; this is the file system supplying it, ONCE, out of the         *)
  (*  invariants the boot chain has just allocated.  The mask the law      *)
  (*  closes over is the six namespaces the collection opens, and the one  *)
  (*  fact a holder still needs about it is that [logN] is not among them  *)
  (*  -- a committer runs the law with the byte view already open.         *)
  (*                                                                      *)
  (*  [γ = icfg_log] is the tie every contract that mixes a threaded log   *)
  (*  gname with the region already carries (fs-log.md section G.17): the  *)
  (*  escrows and the region park shares of [ln_tx icfg_log], while        *)
  (*  [log_ctx] is stated at its own [γ].  True at boot by construction.   *)
  (* ==================================================================== *)

  Lemma fs_snap_law_build (γ : log_names) (cn : ic_names) (γfs : fs_names)
      (γi : gname) (cov : gset Z) (ls : Z) (nib : nat) (sb : fs_sb) :
    γ = icfg_log ->
    col_geom sb (FsImg.sb_inodestart sb) nib (fs_home_set cov ls) ->
    ireg_inv γi γfs (FsImg.sb_inodestart sb) nib -∗
    bitmap_inv γfs (FsImg.sb_bmapstart sb) cov ls (FsImg.sb_size sb) -∗
    ic_escrows cn γfs γi cov ls -∗
    ipool_inv cn γfs γi cov ls nib -∗
    sb_park γfs sb -∗
    snap_law γ γfs cov ls.
  Proof.
    intros -> Hgeom.
    iIntros "#Hireg #Hbm #Hesc #Hpool #Hpark".
    iApply (snap_law_intro icfg_log γfs cov ls
              ((↑ftopN : coPset) ∪ ↑iregN ∪ ↑bitmapN ∪ ↑sbN ∪ ↑ipoolN
               ∪ ↑icEscN)).
    (* [sbN] IS A CHILD OF [logN] (durable-disk lane E-blk1), so
       [solve_ndisj] alone no longer closes this: block 1's park is a
       SIBLING of the byte view's own [fsbN] under one parent, and the fact
       the committer needs is disjointness from [fsbN], not from [logN].
       The other five namespaces are outside [logN] altogether. *)
    { assert (Hoth : (↑logN : coPset)
                     ## ((↑ftopN : coPset) ∪ ↑iregN ∪ ↑bitmapN ∪ ↑ipoolN
                         ∪ ↑icEscN)) by solve_ndisj.
      pose proof (fsbN_logN) as Hfb.
      pose proof (fsbN_sbN_disj) as Hsb.
      set_solver. }
    rewrite /snap_law_at.
    iModIntro. iIntros (E Lb C) "%HN %Hdom %Hlens %Htie %Hdm Hb Ht".
    assert (Hft : (↑ftopN : coPset) ⊆ E) by (etrans; [| exact HN]; set_solver).
    assert (Hir : (↑iregN : coPset) ⊆ E) by (etrans; [| exact HN]; set_solver).
    assert (Hbn : (↑bitmapN : coPset) ⊆ E) by (etrans; [| exact HN]; set_solver).
    assert (Hsn : (↑sbN : coPset) ⊆ E) by (etrans; [| exact HN]; set_solver).
    assert (Hpn : (↑ipoolN : coPset) ⊆ E) by (etrans; [| exact HN]; set_solver).
    assert (Hen : (↑icEscN : coPset) ⊆ E) by (etrans; [| exact HN]; set_solver).
    iMod (fs_collect_snap_ok E cn γfs γi cov ls nib sb Lb C Hgeom
            Hft Hir Hbn Hsn Hpn Hen
            with "Hireg Hbm Hesc Hpool Hpark [Hb] Ht")
      as "(%Hok & Hauth & Ht)".
    { rewrite /col_auth. iFrame "Hb".
      iSplitR; [iPureIntro; exact Hdom |].
      iSplitR; [iPureIntro; exact Hlens |].
      iSplitR; [iPureIntro; exact Htie |].
      iPureIntro; exact Hdm. }
    rewrite /col_auth. iDestruct "Hauth" as "(Hb & _ & _ & _ & _)".
    iModIntro. iFrame "Hb Ht". iPureIntro. exact Hok.
  Qed.

End CollectAll.
