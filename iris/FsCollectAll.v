(* ====================================================================== *)
(*  FsCollectAll.v -- THE ASSEMBLY (durable-disk lane C-8)                 *)
(*  (claude-notes/design/durable-fs-plan.md section 4, "collection at      *)
(*   quiescence"; FsCollect.v does the ARITHMETIC, this file finds the     *)
(*   pieces)                                                              *)
(*                                                                        *)
(*  [fs_collect_dur] below builds the era's DURABLE SNAPSHOT out of the    *)
(*  era's own pieces, at ONE ghost step with the WAL's [LogDefs.ln_tx]     *)
(*  authority empty: the abstract map off [InodeRegion.ftop_inv], the      *)
(*  records off [InodeRegion.ireg_inv], the used set and the free blocks   *)
(*  off [BitmapInv.bitmap_inv], block 1 off [SbPark.sb_park], and one      *)
(*  bundle per region inum off the pool ([IcacheEscrow.ipool_quiesce_acc]) *)
(*  and the fifty slot escrows ([IcacheEscrow.ic_escrow_body_cover_all]).  *)
(*                                                                        *)
(*  THE COLLECTION IS AN ACCESSOR (durable-disk EV-Y), and that is what    *)
(*  lets the TRANSPORT be the mint's caller.  What comes out of            *)
(*  [col_bodies_acc] is [FsState.fs_state (fs_gamma_L γfs) (DfracOwn ¾) S] *)
(*  -- exactly [FsDurXfer.fs_state_xfer_tok]'s source -- beside a closing  *)
(*  wand; the transport RETURNS its source, so every one of the six        *)
(*  invariant families closes with the body it was opened with.  Nothing   *)
(*  pure about the state is materialised on the way: the runs' pairwise    *)
(*  disjointness is read off [FsStateDefs.phi_excl] at a share above a     *)
(*  half, inside the transport, and the ONE pure row that still travels is *)
(*  [FsDurSnap.snap_shape]'s, which no resource pins.                      *)
(*                                                                        *)
(*  IT USED TO BE DESTRUCTIVE, and the device was [pure_keep]: an          *)
(*  entailment [R |- <pure phi>] yields [R |- <pure phi> * R] in an affine *)
(*  logic, so a collection whose conclusion is PURE may drop whatever it   *)
(*  likes.  Two things made the accessor possible instead -- the           *)
(*  partition's three index sets ARE disjoint ([col_sidez_disj], off the   *)
(*  region's own slots), and a supplier's row can be lent with its own way *)
(*  back ([FsCollect.col_row]).                                            *)
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
Require Import LogDefs.
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
Require Import FsDurXfer.       (* the run vocabulary: [xr_fs], [xf_shape] *)
Require Import FsDurSnap.
Require Import FsCollect.
Require Import LogSnapLaw.      (* [snap_law] -- what [log_ctx] parks *)

Local Open Scope Z_scope.

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

  (* ...AND THE CONVERSE, WHICH THE ACCESSOR NEEDS (durable-disk EV-Y):
     with no duplicates to drop the list's big-op IS the set's, both ways.
     Iris states it; naming it here keeps the two directions side by side. *)
  Lemma big_sepS_of_list_nodup `{Countable A} (l : list A) (Φ : A -> iProp Σ) :
    base.NoDup l ->
    ([∗ set] z ∈ (list_to_set l : gset A), Φ z) ⊢ [∗ list] x ∈ l, Φ x.
  Proof. intros Hnd. rewrite (big_sepS_list_to_set Φ l Hnd) //. Qed.

  (* [big_sepS_union_weak] IS DELETED (durable-disk EV-Y).  It covered a
     UNION by dropping the overlap, which is what the pool/marker/live
     partition used to need; the three index sets are now shown DISJOINT
     from the region's own slots ([col_sidez_disj] below), so the exact
     [big_sepS_union] applies and nothing is dropped at that boundary. *)

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

  (* ...AND BACK (durable-disk EV-Y).  The region's inums are the sixteen
     of each block and no block's sixteen meet another's ([region_blk_disj]),
     so the crossing is a bijection and the accessor's closing wand walks it
     in this direction. *)
  Lemma blk_inums_nodup (bi : nat) :
    base.NoDup
      ((fun i : nat => 16 * Z.of_nat bi + Z.of_nat i) <$> seq 0%nat 16%nat).
  Proof.
    apply NoDup_fmap_2; [intros x y Hxy; lia | apply NoDup_seq].
  Qed.

  Lemma nested_of_set (Ψ : Z -> iProp Σ) (nib : nat) :
    ([∗ set] z ∈ region_inums nib, Ψ z)
    ⊢ [∗ list] bi ∈ seq 0%nat nib,
        [∗ list] i ∈ seq 0%nat 16%nat, Ψ (16 * Z.of_nat bi + Z.of_nat i).
  Proof.
    induction nib as [| n IH].
    - iIntros "_". done.
    - rewrite (seq_S n 0).
      rewrite (big_sepL_snoc
                 (fun (_ : nat) (bi : nat) =>
                    ([∗ list] i ∈ seq 0%nat 16%nat,
                       Ψ (16 * Z.of_nat bi + Z.of_nat i))%I)
                 (seq 0 n) (0 + n)%nat).
      rewrite region_inums_S.
      rewrite (big_sepS_union Ψ _ _ (region_blk_disj n)).
      iIntros "[Hpre Hlast]".
      iDestruct (IH with "Hpre") as "$".
      rewrite /blk_inums.
      iDestruct (big_sepS_of_list_nodup _ Ψ (blk_inums_nodup n)
                   with "Hlast") as "Hlast".
      rewrite big_sepL_fmap.
      replace (0 + n)%nat with n by lia.
      iExact "Hlast".
  Qed.

End BigOpsRegion.

(* ====================================================================== *)
(*  0b.  THE NAMESPACE ARITHMETIC THE FIFTY-FOLD OPENING RUNS ON          *)
(* ====================================================================== *)

(* THE SIDE CONDITION A SECOND OPENING WOULD OWE, REFUTED.  [inv_acc] at
   [E] concludes at [E ∖ ↑N]; a second [inv N _] there needs
   [↑N ⊆ E ∖ ↑N].  A namespace's closure is infinite ([nclose_infinite]),
   hence inhabited, and no inhabited set is contained in a set it has been
   removed from.  Stated at an arbitrary [E] so that it covers the nested
   openings the collection would need, not just the outermost one. *)
Lemma ns_not_reopenable (N : namespace) (E : coPset) :
  ↑N ⊆ E -> ~ (↑N ⊆ E ∖ ↑N).
Proof.
  intros HE Hsub.
  pose proof (coPpick_elem_of (↑N) (nclose_infinite N)) as Hx.
  apply (Hsub _) in Hx as Hx'.
  apply elem_of_difference in Hx' as [_ Hnot].
  exact (Hnot Hx).
Qed.

(* ...and the same fact in the form the fix is stated at: two DISTINCT
   namespaces of one family are disjoint, so the two openings compose.
   This is what [icEscN .@ j] / [icEscN .@ k] buys, and it is why the fix
   is a change of allocation rather than of the proof. *)
Lemma esc_ns_disjoint (N : namespace) (j k : nat) :
  j <> k -> (↑N.@j : coPset) ## ↑N.@k.
Proof. intros Hne. apply ndot_ne_disjoint. exact Hne. Qed.

(* the mask a k-th opening leaves still contains every LATER slot's
   namespace, which is the induction step the fifty-fold collection runs *)
Lemma esc_ns_still_open (N : namespace) (E : coPset) (j k : nat) :
  j <> k -> ↑N.@k ⊆ E -> ↑N.@k ⊆ E ∖ ↑N.@j.
Proof.
  intros Hne HE x Hx.
  apply elem_of_difference. split; [exact (HE x Hx)|].
  intros Hxj. exact (esc_ns_disjoint N k j (fun H => Hne (eq_sym H)) x Hx Hxj).
Qed.


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

  (* ==================================================================== *)
  (*  ...AND THE PARTITION IS DISJOINT (durable-disk EV-Y)                  *)
  (*                                                                      *)
  (*  [IcacheEscrow.ipool_quiesce_acc] states its three index sets as a    *)
  (*  UNION and no pure row says they do not overlap.  They do not, and    *)
  (*  the proof is SEPARATION LOGIC: a shared inum would give two          *)
  (*  [FsCollect.col_side]s beside the region's own slot, which            *)
  (*  [FsCollect.col_side_slot_excl] refutes off one exclusive [ghost_map] *)
  (*  element.  Nothing pure about the state is materialised and the       *)
  (*  conclusion is pure, so the caller keeps every row.                   *)
  (* ==================================================================== *)
  (* the refutation at an inum named as a NUMBER, exactly as
     [col_row_slot_acc] is for the door *)
  Lemma col_side_slot_excl_z (γfs : fs_names) (γi : gname) (z : Z)
      (w : mword 32) (d : dinode) :
    bv_unsigned w = z ->
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ireg_slot γfs γi z d -∗
    col_side γfs γi w -∗ col_side γfs γi w -∗ False.
  Proof.
    intros <-. iIntros "Ht Hslot Hs1 Hs2".
    iApply (col_side_slot_excl γfs γi w d with "Ht Hslot Hs1 Hs2").
  Qed.

  Lemma col_sidez_disj (γfs : fs_names) (γi : gname) (m : gmap Z dinode)
      (Rs A B : gset Z) :
    A ⊆ Rs -> B ⊆ Rs ->
    (forall z : Z, z ∈ Rs -> 0 <= z < 2 ^ 32) ->
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ([∗ set] z ∈ Rs, ∃ d : dinode, ⌜m !! z = Some d⌝
                                   ∗ ireg_slot γfs γi z d) -∗
    ([∗ set] z ∈ A, col_sidez γfs γi z) -∗
    ([∗ set] z ∈ B, col_sidez γfs γi z) -∗ ⌜A ## B⌝.
  Proof.
    intros HA HB Hw. iIntros "Ht Hslots HA HB".
    iAssert (⌜forall z : Z, z ∈ A -> z ∈ B -> False⌝)%I
      with "[Ht Hslots HA HB]" as %Hd.
    { rewrite bi.pure_forall. iIntros (z).
      rewrite bi.pure_impl. iIntros (HzA).
      rewrite bi.pure_impl. iIntros (HzB).
      assert (HzR : z ∈ Rs) by exact (HA z HzA).
      iDestruct (big_sepS_elem_of _ Rs z HzR with "Hslots") as (d Hd) "Hslot".
      iDestruct (big_sepS_elem_of _ A z HzA with "HA") as "Hs1".
      iDestruct (big_sepS_elem_of _ B z HzB with "HB") as "Hs2".
      rewrite /col_sidez.
      iApply (col_side_slot_excl_z γfs γi z (mword_of_int z) d
                (moi_unsigned_z z (Hw z HzR)) with "Ht Hslot Hs1 Hs2"). }
    iPureIntro. apply elem_of_disjoint. exact Hd.
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

  (* ...AND THE SAME CROSSING BACK (durable-disk EV-Y).  The records carry
     the block's [ds] and [InodeRegion.ireg_couple] pins every slot's record
     against [m], so the slots come back to their own block with no choice
     to make. *)
  Lemma ireg_blks_collect_of (γfs : fs_names) (γi : gname) (ist : Z)
      (m : gmap Z dinode) (nib : nat) :
    ([∗ list] bi ∈ seq 0%nat nib,
       ∃ ds : list dinode,
         ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝ ∗ ireg_recs γfs ist bi ds) -∗
    ([∗ set] z ∈ region_inums nib,
       ∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d) -∗
    [∗ list] bi ∈ seq 0%nat nib, ireg_blk γi γfs ist m bi.
  Proof.
    iIntros "Hrecs Hslots".
    iDestruct (nested_of_set with "Hslots") as "Hslots".
    iCombine "Hrecs Hslots" as "H". rewrite -big_sepL_sep.
    iApply (big_sepL_impl with "H"). iIntros "!>" (j bi Hj) "[Hr Hs]".
    iDestruct "Hr" as (ds Hwf Hcpl) "Hrecs".
    rewrite /ireg_blk. iExists ds.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Hrecs".
    iApply (big_sepL_impl with "Hs"). iIntros "!>" (q i Hq) "Hs".
    apply lookup_seq in Hq as [-> Hlt]. rewrite Nat.add_0_l.
    iDestruct "Hs" as (d Hd) "Hs".
    rewrite (Hcpl q Hlt) in Hd. apply (inj Some) in Hd. subst d.
    iExact "Hs".
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
        "(%Hok & %Hdok & %Hddix & %Hdoc & _ & Hleg & _ & _)".
      (* the pool row's leg IS [col_side]'s conjunct, on the nose
         (durable-disk EV stage 5): nothing is opened at this boundary any
         more *)
      iRight. iExists (era_node dn0 bm0 data0).
      (* the pool row carries the three directory clauses already
         (durable-disk lane E-clauses); the node is [era_node] of its
         triple, so the transport is one lemma *)
      iSplitR.
      { iPureIntro.
        exact (FsStateEra.node_dir_local_of_ok (bv_unsigned w) cov ls
                 icfg_nib dn0 bm0 data0 Hok Hdok Hddix Hdoc). }
      (* the pool's row is WHOLE; the collection's uniform share is three
         quarters, so the quarter is shed and dropped (durable-disk EV-X) *)
      iDestruct (ic_inode_leg_shed_to with "Hleg") as "[$ _]".
    - iLeft. iExact "Hmk".
  Qed.

  (* ==================================================================== *)
  (*  ...AND THE SAME THREE AS ROWS WITH A WAY BACK (durable-disk EV-Y)    *)
  (* ==================================================================== *)

  Definition col_rowz (γfs : fs_names) (γi : gname) (z : Z) (Q : iProp Σ)
    : iProp Σ :=
    col_row γfs γi (mword_of_int z : mword 32) Q.

  Lemma col_rowz_side (γfs : fs_names) (γi : gname) (z : Z) (Q : iProp Σ) :
    col_rowz γfs γi z Q -∗ col_sidez γfs γi z.
  Proof.
    rewrite /col_rowz /col_sidez. iApply col_row_side.
  Qed.

  (* THE POOL'S ORDINARY ROW.  The alloc arm's leg is at fraction 1; the
     quarter it sheds is KEPT in the row's frame instead of being dropped
     (durable-disk EV-X dropped it, because the collection was
     destructive), and the two content holds ride beside it.  The marker
     arm keeps its two untied holds and nothing else. *)
  Lemma ipool_shape_np_row (γfs : fs_names) (γi : gname) (cov : gset Z)
      (ls : Z) (w : mword 32) :
    ipool_shape_np γfs γi cov ls w -∗
    col_row γfs γi w (ipool_shape_np γfs γi cov ls w).
  Proof.
    rewrite /ipool_shape_np.
    iIntros "[Halloc | (Hmk & Hdv & Hfv)]".
    - rewrite /ipool_alloc.
      iDestruct "Halloc" as (dn0 bm0 data0)
        "(%Hok & %Hdok & %Hddix & %Hdoc & %Huniq & Hleg & Hdv & Hfv)".
      iDestruct (ic_inode_leg_shed_to with "Hleg") as "[Hleg Hrd]".
      rewrite /col_row. iRight.
      iExists (era_node dn0 bm0 data0),
              (inode_rd_era γfs (DfracOwn (1/4)) w (era_node dn0 bm0 data0)
               ∗ dv_ride (bv_unsigned w) (dv_of dn0 data0)
               ∗ fv_ride (bv_unsigned w) (fv_of dn0 data0))%I.
      iSplitR.
      { iPureIntro.
        exact (FsStateEra.node_dir_local_of_ok (bv_unsigned w) cov ls
                 icfg_nib dn0 bm0 data0 Hok Hdok Hddix Hdoc). }
      iFrame "Hleg Hrd Hdv Hfv".
      iIntros "Hleg (Hrd & Hdv & Hfv)".
      iDestruct (ic_inode_leg_shed_of with "Hleg Hrd") as "Hleg".
      iLeft. rewrite /ipool_alloc. iExists dn0, bm0, data0.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |]. iFrame "Hleg Hdv Hfv".
    - rewrite /col_row. iLeft.
      iExists ((∃ e, dv_ride (bv_unsigned w) e)
               ∗ (∃ b, fv_ride (bv_unsigned w) b))%I.
      iFrame "Hmk Hdv Hfv".
      iIntros "Hmk [Hdv Hfv]". iRight. iFrame "Hmk Hdv Hfv".
  Qed.

  Lemma ipool_ord_row (γfs : fs_names) (γi : gname) (cov : gset Z)
      (ls : Z) (w : mword 32) :
    ipool_ord γfs γi cov ls w -∗
    col_row γfs γi w (ipool_ord γfs γi cov ls w).
  Proof.
    rewrite {1}/ipool_ord. iIntros "(Hcnt & Hfrz & Hnp & Hifz)".
    iDestruct (ipool_shape_np_row with "Hnp") as "Hrow".
    iDestruct (col_row_frame γfs γi w _
                 (icnt_half (bv_unsigned w) 0%nat
                  ∗ frzm_h (bv_unsigned w) false
                  ∗ ifreeze_off (bv_unsigned w))%I
                 with "Hrow [$Hcnt $Hfrz $Hifz]") as "Hrow".
    iApply (col_row_mono with "[] Hrow").
    iIntros "[Hnp (Hcnt & Hfrz & Hifz)]".
    rewrite /ipool_ord. iFrame "Hcnt Hfrz Hnp Hifz".
  Qed.

  Lemma ipool_rows_rows (γfs : fs_names) (γi : gname) (cov : gset Z)
      (ls : Z) (O : gset Z) :
    ipool_rows γfs γi cov ls O ⊢
    [∗ set] z ∈ O, col_rowz γfs γi z (ipool_ord γfs γi cov ls (mword_of_int z)).
  Proof.
    rewrite /ipool_rows. iIntros "H".
    iApply (big_sepS_impl with "H"). iIntros "!>" (z Hz) "Hr".
    rewrite /col_rowz. iApply (ipool_ord_row with "Hr").
  Qed.

  Lemma ipool_rows_of (γfs : fs_names) (γi : gname) (cov : gset Z)
      (ls : Z) (O : gset Z) :
    ([∗ set] z ∈ O, ipool_ord γfs γi cov ls (mword_of_int z))
    ⊢ ipool_rows γfs γi cov ls O.
  Proof. rewrite /ipool_rows //. Qed.

  (* ---- the corpse ledger's markers ----------------------------------- *)

  Lemma col_row_mark_z (γfs : fs_names) (γi : gname) (z : Z) (w : mword 32) :
    bv_unsigned w = z ->
    imark γi z -∗ col_row γfs γi w (imark γi z).
  Proof. intros <-. iApply col_row_mark. Qed.

  (* the corpse ledger's markers, as rows: nothing is kept and the way back
     is the identity, so the [X] column closes with what it opened *)
  Lemma imarks_rows (γfs : fs_names) (γi : gname) (X : gset Z) :
    (forall z : Z, z ∈ X -> 0 <= z < 2 ^ 32) ->
    ([∗ set] z ∈ X, imark γi z)
    ⊢ [∗ set] z ∈ X, col_rowz γfs γi z (imark γi z).
  Proof.
    intros Hr. iIntros "H".
    iApply (big_sepS_impl with "H"). iIntros "!>" (z Hz) "Hm".
    rewrite /col_rowz.
    iApply (col_row_mark_z γfs γi z (mword_of_int z)
              (moi_unsigned_z z (Hr z Hz)) with "Hm").
  Qed.


  (* ---- the fifty slot escrows --------------------------------------- *)

  (* ONE SLOT.  [IcacheEscrow.ic_slot_cover]'s three alternatives at a LIVE
     slot: the first is refuted by the pool's own quarter of the identity
     cell ([IcacheEscrow.ic_id_agree] -- the slot cannot be dead and live at
     once), and the other two ARE the two arms of [FsCollect.col_side].  The
     lend's frame and its closing wand are dropped: the collection is
     destructive, and it is spent only where the conclusion is [False]
     (the duplicate refutation inside [esc_covers_got_acc]); the ACCESSOR
     twin, which keeps the lend's frame and its closing wand, is
     [ic_cover_row]. *)
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
    - iDestruct "Hc" as (n) "[%Hdl Hl]".
      rewrite /ic_lend. iDestruct "Hl" as "[(Hid & Hleg) _]".
      (* the cover lends the LEG as one conjunct (durable-disk EV stage 4)
         and [col_side] now IS that conjunct (stage 5): the boundary is a
         pass-through, and the two [ic_inode_leg_open]s that used to sit
         here and at [ipool_shape_np_side] are gone. *)
      iDestruct (ic_id_agree with "Hq Hid") as %(_ & _ & <-).
      rewrite /col_side. iRight. iExists n.
      iSplitR; [iPureIntro; exact Hdl |]. iExact "Hleg".
  Qed.

  (* ...AND THE SAME SLOT AS A ROW (durable-disk EV-Y).  [IcacheEscrow.
     ic_lend] already carries the way back to [ic_escrow_body]; what this
     adds is that the piece the collection takes out of the lend -- the
     leg, or the pool shape's own arm -- can be put back, so the cover and
     the pool's quarter of the identity cell both return.  The dead-slot
     alternative is refuted exactly as before, by that quarter. *)
  Lemma ic_cover_row (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (ls : Z) (k : nat) (dev inum : mword 32) :
    ic_id cn k (1/4) true dev inum -∗
    ic_slot_cover cn γfs γi cov ls k -∗
    col_row γfs γi inum
      (ic_id cn k (1/4) true dev inum ∗ ic_slot_cover cn γfs γi cov ls k).
  Proof.
    iIntros "Hq Hc".
    iDestruct "Hc" as (dev' inum') "[Ha | [Hb | Hc]]".
    - rewrite /ic_lend. iDestruct "Ha" as "[Hid _]".
      iDestruct (ic_id_agree with "Hq Hid") as %(Hv & _ & _). discriminate.
    - rewrite /ic_lend. iDestruct "Hb" as "[[Hid Hnp] Hfr]".
      iDestruct (ic_id_agree with "Hq Hid") as %(_ & _ & <-).
      iDestruct (ipool_shape_np_row with "Hnp") as "Hrow".
      iDestruct (col_row_frame with "Hrow Hq") as "Hrow".
      iDestruct (col_row_frame with "Hrow Hid") as "Hrow".
      iDestruct (col_row_frame with "Hrow Hfr") as "Hrow".
      iApply (col_row_mono with "[] Hrow").
      iIntros "[[[Hnp Hq] Hid] Hfr]". iFrame "Hq".
      iExists dev', inum. iRight. iLeft. rewrite /ic_lend.
      iFrame "Hid Hnp Hfr".
    - iDestruct "Hc" as (n) "[%Hdl Hl]".
      rewrite /ic_lend. iDestruct "Hl" as "[(Hid & Hleg) Hfr]".
      iDestruct (ic_id_agree with "Hq Hid") as %(_ & _ & <-).
      iAssert (col_row γfs γi inum
                 (ic_inode_leg γfs (DfracOwn (3/4)) γi inum n))%I
        with "[Hleg]" as "Hrow".
      { rewrite /col_row. iRight. iExists n, emp%I.
        iSplitR; [iPureIntro; exact Hdl |]. iFrame "Hleg".
        iSplitR; [done |]. iIntros "H _". iExact "H". }
      iDestruct (col_row_frame with "Hrow Hq") as "Hrow".
      iDestruct (col_row_frame with "Hrow Hid") as "Hrow".
      iDestruct (col_row_frame with "Hrow Hfr") as "Hrow".
      iApply (col_row_mono with "[] Hrow").
      iIntros "[[[Hleg Hq] Hid] Hfr]". iFrame "Hq".
      iExists dev', inum. iRight. iRight. iExists n.
      iSplitR; [iPureIntro; exact Hdl |]. rewrite /ic_lend.
      iFrame "Hid Hleg Hfr".
  Qed.

  (* ...AND A COVER IS A BODY (durable-disk EV-Y).  [IcacheEscrow.ic_lend]
     carries its own way back in every alternative, so a slot that was
     opened for the collection closes with no premise at all -- which is
     what lets the fifty escrows be given back after the transport has
     returned the source. *)
  Lemma ic_slot_cover_body (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (ls : Z) (k : nat) :
    ic_slot_cover cn γfs γi cov ls k ⊢ ic_escrow_body cn γfs γi cov ls k.
  Proof.
    iIntros "Hc". iDestruct "Hc" as (dev inum) "[Ha | [Hb | Hc]]".
    - rewrite /ic_lend. iDestruct "Ha" as "[HQ (%R & HR & Hw)]".
      iApply ("Hw" with "HQ HR").
    - rewrite /ic_lend. iDestruct "Hb" as "[HQ (%R & HR & Hw)]".
      iApply ("Hw" with "HQ HR").
    - iDestruct "Hc" as (n) "[_ Hl]". rewrite /ic_lend.
      iDestruct "Hl" as "[HQ (%R & HR & Hw)]".
      iApply ("Hw" with "HQ HR").
  Qed.

  Lemma ic_slot_cover_bodies (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (ls : Z) (l : list nat) :
    ([∗ list] k ∈ l, ic_slot_cover cn γfs γi cov ls k)
    ⊢ [∗ list] k ∈ l, ic_escrow_body cn γfs γi cov ls k.
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (j k Hj) "Hc". iApply (ic_slot_cover_body with "Hc").
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


  (* ==================================================================== *)
  (*  WHAT ONE INUM HANDS THE COLLECTION, AND HOW IT GOES BACK             *)
  (*  (durable-disk EV-Y)                                                  *)
  (*                                                                      *)
  (*  [col_got] is the collection's per-inum output with the               *)
  (*  keep-alive fragment folded in.  It is SELF-DESCRIBING, which is what *)
  (*  makes the closing wand possible: the node is pinned by the abstract  *)
  (*  map's own value at this inum, so the [fs_state] the transport gives  *)
  (*  back is at the very node that was lent; and the keep-alive rides     *)
  (*  under its own existential, because at every inum but the root it is  *)
  (*  [emp] and at the root the type value is pinned by                    *)
  (*  [FsStateLink.link_auth_tok_agree] against the link element.          *)
  (* ==================================================================== *)
  (* THE KEEP-ALIVE FRAGMENT RIDES OUTSIDE THE EXISTENTIAL, exactly as it
     did in the destructive collection's output and for the same reason:
     [big_sepS_sep] splits it off as its own column, which is what
     [col_keeps_root_acc] takes the root's out of. *)
  Definition col_got (γfs : fs_names) (γi : gname) (I : gmap Z fs_node)
      (z : Z) : iProp Σ :=
    ((∃ n : fs_node,
        ⌜I !! z = Some n⌝ ∗ ⌜node_dir_local z icfg_nib n⌝
        ∗ col_bundle γfs γi z n
        ∗ fs_link_node (fs_link γfs) z n)
     ∗ ∃ kv : ity, ireg_keep γfs z kv)%I.

  Lemma col_row_got (γfs : fs_names) (γi : gname) (m : gmap Z dinode)
      (I : gmap Z fs_node) (z : Z) (w : mword 32) (d : dinode) (Q : iProp Σ) :
    bv_unsigned w = z ->
    m !! z = Some d ->
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ghost_map_auth γi 1 m -∗
    ghost_map_auth (fs_top γfs) 1 I -∗
    col_row γfs γi w Q -∗
    ireg_slot γfs γi z d -∗
      ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
      ∗ ghost_map_auth γi 1 m
      ∗ ghost_map_auth (fs_top γfs) 1 I
      ∗ col_got γfs γi I z
      ∗ (col_got γfs γi I z -∗ Q ∗ ireg_slot γfs γi z d).
  Proof.
    intros <- Hmd. iIntros "Ht Hm Hi Hrow Hslot".
    iDestruct (col_row_slot_acc γfs γi w d Q with "Ht Hrow Hslot")
      as "(Ht & Hlnk & %n & %Hdl & Hleg & Hback)".
    iFrame "Ht".
    iDestruct (col_leg_bundle_acc γfs γi w n d m I Hmd
                 with "Hm Hi Hlnk Hleg")
      as "(Hm & Hi & %HIz & Hb & Hle & Hkp & Hback2)".
    iFrame "Hm Hi".
    iSplitL "Hb Hle Hkp".
    { rewrite /col_got. iSplitR "Hkp"; [| iExact "Hkp"]. iExists n.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iFrame "Hb Hle". }
    rewrite /col_got.
    iIntros "[(%n' & %HIz' & %Hdl' & Hb & Hle) Hkp]".
    rewrite HIz in HIz'. apply (inj Some) in HIz'. subst n'.
    iDestruct ("Hback2" with "Hb Hle Hkp") as "[Hlnk Hleg]".
    iApply ("Hback" with "Hleg Hlnk").
  Qed.

  (* ...AND OVER A WHOLE SUPPLIER'S INDEX.  [Ψ] is the supplier's own row
     at that inum, so one lemma serves all three; the closing wand gives
     back the rows AND the region's slots, which is what lets [iregN] and
     the pool close with the bodies they were opened with. *)
  Lemma col_rows_got_acc (γfs : fs_names) (γi : gname) (m : gmap Z dinode)
      (I : gmap Z fs_node) (Rs : gset Z) (Ψ : Z -> iProp Σ) :
    (forall z : Z, z ∈ Rs -> 0 <= z < 2 ^ 32) ->
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ghost_map_auth γi 1 m -∗
    ghost_map_auth (fs_top γfs) 1 I -∗
    ([∗ set] z ∈ Rs, col_rowz γfs γi z (Ψ z)) -∗
    ([∗ set] z ∈ Rs, ∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d) -∗
      ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
      ∗ ghost_map_auth γi 1 m
      ∗ ghost_map_auth (fs_top γfs) 1 I
      ∗ ([∗ set] z ∈ Rs, col_got γfs γi I z)
      ∗ (([∗ set] z ∈ Rs, col_got γfs γi I z)
         -∗ ([∗ set] z ∈ Rs, Ψ z)
            ∗ ([∗ set] z ∈ Rs, ∃ d : dinode, ⌜m !! z = Some d⌝
                                             ∗ ireg_slot γfs γi z d)).
  Proof.
    induction Rs as [| z Rs Hnz IH] using set_ind_L; intros Hw.
    - iIntros "Ht Hm Hi _ _". iFrame "Ht Hm Hi".
      rewrite !big_sepS_empty. iSplitR; [done |].
      iIntros "_". iSplitR; done.
    - iIntros "Ht Hm Hi Hrows Hslots".
      assert (Hzin : z ∈ ({[z]} ∪ Rs : gset Z)).
      { apply elem_of_union_l. by apply elem_of_singleton. }
      assert (Hsub : forall y : Z, y ∈ Rs -> 0 <= y < 2 ^ 32).
      { intros y Hy. apply Hw. by apply elem_of_union_r. }
      rewrite !big_sepS_insert; [| exact Hnz ..].
      iDestruct "Hrows" as "[Hrow Hrows]".
      iDestruct "Hslots" as "[Hslot Hslots]".
      iDestruct (IH Hsub with "Ht Hm Hi Hrows Hslots")
        as "(Ht & Hm & Hi & Hgots & Hback)".
      iDestruct "Hslot" as (d Hd) "Hslot".
      rewrite /col_rowz.
      iDestruct (col_row_got γfs γi m I z (mword_of_int z) d (Ψ z)
                   (moi_unsigned_z z (Hw z Hzin)) Hd
                   with "Ht Hm Hi Hrow Hslot")
        as "(Ht & Hm & Hi & Hgot & Hb1)".
      iFrame "Ht Hm Hi Hgot Hgots".
      iIntros "[Hgot Hgots]".
      iDestruct ("Hb1" with "Hgot") as "[HQ Hslot]".
      iDestruct ("Hback" with "Hgots") as "[HQs Hslots]".
      iFrame "HQ HQs Hslots".
      iExists d. iSplitR; [by iPureIntro |]. iExact "Hslot".
  Qed.

  (* ==================================================================== *)
  (*  ...AND THE FIFTY AS AN ACCESSOR (durable-disk EV-Y)                   *)
  (*                                                                      *)
  (*  THE DUPLICATE IS REFUTED INSIDE THE INDUCTION, which is what lets    *)
  (*  the list of slots and the SET of live inums be the same big-op in    *)
  (*  both directions with no [NoDup] side condition to carry: if the      *)
  (*  head's inum were already among the tail's, the two covers would be   *)
  (*  two [col_side]s at one inum, which the region's own slot refutes     *)
  (*  ([FsCollect.col_side_slot_excl]).  [esc_covers_live] -- the          *)
  (*  destructive twin, which DROPS the head in that case -- is what the   *)
  (*  refutation reads the tail's side off, and it is spent only inside    *)
  (*  the [False] branch.                                                  *)
  (* ==================================================================== *)
  Lemma esc_covers_got_acc (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (ls : Z) (m : gmap Z dinode) (I : gmap Z fs_node)
      (o : nat) (ids : list (bool * mword 32 * mword 32)) :
    (forall z : Z, z ∈ ic_live_inums ids -> 0 <= z < 2 ^ 32) ->
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ghost_map_auth γi 1 m -∗
    ghost_map_auth (fs_top γfs) 1 I -∗
    ([∗ list] k ↦ p ∈ ids,
       (ic_id cn (o + k) (1/4) p.1.1 p.1.2 p.2
        ∗ ic_slot_cover cn γfs γi cov ls (o + k))) -∗
    ([∗ set] z ∈ ic_live_inums ids,
       ∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d) -∗
      ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
      ∗ ghost_map_auth γi 1 m
      ∗ ghost_map_auth (fs_top γfs) 1 I
      ∗ ([∗ set] z ∈ ic_live_inums ids, col_got γfs γi I z)
      ∗ (([∗ set] z ∈ ic_live_inums ids, col_got γfs γi I z)
         -∗ ([∗ list] k ↦ p ∈ ids,
                (ic_id cn (o + k) (1/4) p.1.1 p.1.2 p.2
                 ∗ ic_slot_cover cn γfs γi cov ls (o + k)))
            ∗ ([∗ set] z ∈ ic_live_inums ids,
                 ∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d)).
  Proof.
    revert o. induction ids as [| p ids IH]; intros o Hw.
    - iIntros "Ht Hm Hi _ _". iFrame "Ht Hm Hi".
      rewrite /ic_live_inums /=. rewrite !big_sepS_empty.
      iSplitR; [done |]. iIntros "_". iSplitR; done.
    - iIntros "Ht Hm Hi Hl Hslots".
      rewrite big_sepL_cons. iDestruct "Hl" as "[Hhd Htl]".
      iAssert ([∗ list] k ↦ y ∈ ids,
                 (ic_id cn (S o + k) (1/4) y.1.1 y.1.2 y.2
                  ∗ ic_slot_cover cn γfs γi cov ls (S o + k)))%I
        with "[Htl]" as "Htl".
      { iApply (big_sepL_impl with "Htl"). iIntros "!>" (j y Hj) "H".
        replace (S o + j)%nat with (o + S j)%nat by lia. iExact "H". }
      destruct p as [[v dev] inum]. destruct v; cbn [fst snd].
      + (* A LIVE SLOT *)
        rewrite ic_live_inums_cons_true.
        iDestruct "Hhd" as "[Hid Hcov]". rewrite Nat.add_0_r.
        assert (Hwt : forall z : Z, z ∈ ic_live_inums ids -> 0 <= z < 2 ^ 32).
        { intros y Hy. apply Hw. rewrite ic_live_inums_cons_true.
          by apply elem_of_union_r. }
        assert (Hzr : 0 <= bv_unsigned inum < 2 ^ 32).
        { apply Hw. rewrite ic_live_inums_cons_true.
          apply elem_of_union_l. by apply elem_of_singleton. }
        destruct (decide (bv_unsigned inum ∈ ic_live_inums ids))
          as [Hin | Hnin].
        { (* THE DUPLICATE, REFUTED *)
          iExFalso.
          iDestruct (ic_slot_cover_side with "Hid Hcov") as "Hs1".
          iDestruct (esc_covers_live cn γfs γi cov ls (S o) ids with "Htl")
            as "Hset".
          iDestruct (big_sepS_elem_of _ _ (bv_unsigned inum) Hin with "Hset")
            as "Hs2".
          assert (Hmem : bv_unsigned inum
                         ∈ ({[bv_unsigned inum]} ∪ ic_live_inums ids : gset Z)).
          { apply elem_of_union_l. by apply elem_of_singleton. }
          iDestruct (big_sepS_elem_of _ _ (bv_unsigned inum) Hmem
                       with "Hslots") as (d Hd) "Hslot".
          rewrite /col_sidez ipl_moi_inum.
          iApply (col_side_slot_excl γfs γi inum d with "Ht Hslot Hs1 Hs2"). }
        rewrite !big_sepS_insert; [| exact Hnin ..].
        iDestruct "Hslots" as "[Hslot Hslots]".
        iDestruct (IH (S o) Hwt with "Ht Hm Hi Htl Hslots")
          as "(Ht & Hm & Hi & Hgots & Hback)".
        iDestruct "Hslot" as (d Hd) "Hslot".
        iDestruct (ic_cover_row cn γfs γi cov ls o dev inum with "Hid Hcov")
          as "Hrow".
        iDestruct (col_row_got γfs γi m I (bv_unsigned inum) inum d _
                     eq_refl Hd with "Ht Hm Hi Hrow Hslot")
          as "(Ht & Hm & Hi & Hgot & Hb1)".
        iFrame "Ht Hm Hi Hgot Hgots".
        iIntros "[Hgot Hgots]".
        iDestruct ("Hb1" with "Hgot") as "[[Hid Hcov] Hslot]".
        iDestruct ("Hback" with "Hgots") as "[Htl Hslots]".
        iSplitR "Hslot Hslots".
        { iSplitL "Hid Hcov"; [iFrame "Hid Hcov" |].
          iApply (big_sepL_impl with "Htl"). iIntros "!>" (j y Hj) "H".
          replace (o + S j)%nat with (S o + j)%nat by lia. iExact "H". }
        iFrame "Hslots". iExists d. iSplitR; [by iPureIntro |]. iExact "Hslot".
      + (* A SLOT THAT NAMES NO INODE: nothing is taken and nothing moves *)
        rewrite ic_live_inums_cons_false.
        assert (Hwt : forall z : Z, z ∈ ic_live_inums ids -> 0 <= z < 2 ^ 32).
        { intros y Hy. apply Hw. by rewrite ic_live_inums_cons_false. }
        iDestruct (IH (S o) Hwt with "Ht Hm Hi Htl Hslots")
          as "(Ht & Hm & Hi & Hgots & Hback)".
        iFrame "Ht Hm Hi Hgots".
        iIntros "Hgots".
        iDestruct ("Hback" with "Hgots") as "[Htl Hslots]".
        iFrame "Hslots".
        iSplitL "Hhd"; [iExact "Hhd" |].
        iApply (big_sepL_impl with "Htl"). iIntros "!>" (j y Hj) "H".
        replace (o + S j)%nat with (S o + j)%nat by lia. iExact "H".
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

  (* ...and the converse, which the accessor's closing wand walks *)
  Lemma big_sepL_seq_of_list_of {A : Type} (l : list A) (P : nat -> iProp Σ)
      (o : nat) :
    ([∗ list] k ↦ _ ∈ l, P (o + k)%nat) ⊢ [∗ list] k ∈ seq o (length l), P k.
  Proof.
    revert o. induction l as [| x l IH]; intros o.
    - iIntros "_". done.
    - cbn [length seq].
      rewrite !big_sepL_cons.
      iIntros "[Hh Ht]". rewrite Nat.add_0_r. iFrame "Hh".
      iApply (IH (S o)).
      iApply (big_sepL_impl with "Ht"). iIntros "!>" (j y Hj) "H".
      replace (S o + j)%nat with (o + S j)%nat by lia. iExact "H".
  Qed.

  (* ---- one inum's bundle, and the fifty-fold threading --------------- *)


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

  (* the rows' own sides, which is all the disjointness reading wants *)
  Lemma col_rowz_sides (γfs : fs_names) (γi : gname) (Rs : gset Z)
      (Ψ : Z -> iProp Σ) :
    ([∗ set] z ∈ Rs, col_rowz γfs γi z (Ψ z))
    ⊢ [∗ set] z ∈ Rs, col_sidez γfs γi z.
  Proof.
    iIntros "H". iApply (big_sepS_impl with "H").
    iIntros "!>" (z Hz) "Hr". iApply (col_rowz_side with "Hr").
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

  (* THE REGION-INDEXED COLUMN AND THE HAND'S TWO MAP-INDEXED ONES, both
     ways (durable-disk EV-Y).  The forward direction is what
     [col_bodies_acc] does inline; the reverse is what its closing
     closing wand walks, and it needs the per-inum directory clauses --
     which the hand carries as its last row -- because they sit under the
     column's existential and not under the map's. *)
  Lemma col_gots_to_hand (γfs : fs_names) (γi : gname) (nib : nat)
      (I : gmap Z fs_node) :
    region_inums nib ⊆ dom I ->
    ([∗ set] z ∈ region_inums nib,
       ∃ n : fs_node,
         ⌜I !! z = Some n⌝ ∗ ⌜node_dir_local z icfg_nib n⌝
         ∗ col_bundle γfs γi z n
         ∗ fs_link_node (fs_link γfs) z n)
    ⊢ ([∗ map] i ↦ n ∈ col_reg_map nib I, col_bundle γfs γi i n)
      ∗ fs_links (fs_link γfs) (col_reg_map nib I).
  Proof.
    intros Hdom. iIntros "HB".
    assert (HdomIq : dom (col_reg_map nib I) = region_inums nib)
      by exact (col_reg_map_dom nib I Hdom).
    rewrite -HdomIq -big_sepM_dom.
    rewrite /fs_links -big_sepM_sep.
    iApply (big_sepM_impl with "HB").
    iIntros "!>" (i x Hix) "(%n & %Hn & %Hdl & Hb & Hl)".
    apply col_reg_map_lookup in Hix as [HI _].
    rewrite HI in Hn. injection Hn as Hnx. subst x.
    iFrame "Hb Hl".
  Qed.

  Lemma col_gots_of_hand (γfs : fs_names) (γi : gname) (nib : nat)
      (I : gmap Z fs_node) :
    region_inums nib ⊆ dom I ->
    (forall (i : Z) (n : fs_node),
       i ∈ region_inums nib -> I !! i = Some n -> node_dir_local i icfg_nib n) ->
    ([∗ map] i ↦ n ∈ col_reg_map nib I, col_bundle γfs γi i n)
    ∗ fs_links (fs_link γfs) (col_reg_map nib I)
    ⊢ [∗ set] z ∈ region_inums nib,
        ∃ n : fs_node,
          ⌜I !! z = Some n⌝ ∗ ⌜node_dir_local z icfg_nib n⌝
          ∗ col_bundle γfs γi z n
          ∗ fs_link_node (fs_link γfs) z n.
  Proof.
    intros Hdom Hdl. iIntros "[Hb Hl]".
    assert (HdomIq : dom (col_reg_map nib I) = region_inums nib)
      by exact (col_reg_map_dom nib I Hdom).
    iAssert ([∗ map] i ↦ _ ∈ col_reg_map nib I,
               ∃ n : fs_node,
                 ⌜I !! i = Some n⌝ ∗ ⌜node_dir_local i icfg_nib n⌝
                 ∗ col_bundle γfs γi i n
                 ∗ fs_link_node (fs_link γfs) i n)%I with "[Hb Hl]" as "H".
    { rewrite /fs_links. iCombine "Hb Hl" as "H". rewrite -big_sepM_sep.
      iApply (big_sepM_impl with "H"). iIntros "!>" (i x Hix) "[Hb Hl]".
      apply col_reg_map_lookup in Hix as [HI Hz].
      iExists x. iSplitR; [by iPureIntro |].
      iSplitR; [iPureIntro; exact (Hdl i x Hz HI) |]. iFrame "Hb Hl". }
    rewrite big_sepM_dom HdomIq. iExact "H".
  Qed.

  (* ==================================================================== *)
  (*  2b.  THE HAND'S OWN RUNS (durable-disk lane H4)                      *)
  (*                                                                      *)
  (*  What the mint takes off [FsCollect.col_hand] and what it does NOT.   *)
  (*  It does not take a byte tie, a used-set clause or a disjointness     *)
  (*  clause.  It takes the RUNS -- the same byte legs, listed, at the ONE *)
  (*  share the collection stands at (three quarters; durable-disk EV-X)   *)
  (*  -- and everything the transport wants is read off them              *)
  (*  ([FsDurXfer.phi_runs_q_disj] off [phi_excl], [phi_runs_q_in] off the *)
  (*  era's own authority).  What the collection ASSEMBLES beside that is  *)
  (*  the whole predicate at that share ([col_hand_state_acc]).            *)
  (* ==================================================================== *)

  (* the region's records, re-indexed from (block, slot) to INUM.  The
     resource does not move: [InodeRegion.ireg_recs] IS the sixteen record
     runs, and [ireg_couple] names the map's value at each. *)
  Lemma col_recs_by_inum (γfs : fs_names) (γi : gname) (ist : Z) (nib : nat)
      (m : gmap Z dinode) :
    ([∗ list] bi ∈ seq 0%nat nib,
       ∃ ds : list dinode,
         ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝ ∗ ireg_recs γfs ist bi ds)
    ⊢ [∗ set] z ∈ region_inums nib,
        ∃ d : dinode, ⌜m !! z = Some d⌝
                      ∗ rec_owned_at (fs_gamma_L γfs) ist z d.
  Proof.
    iIntros "H".
    iAssert ([∗ list] bi ∈ seq 0%nat nib,
               [∗ list] i ∈ seq 0%nat 16%nat,
                 ∃ d : dinode,
                   ⌜m !! (16 * Z.of_nat bi + Z.of_nat i)%Z = Some d⌝
                   ∗ rec_owned_at (fs_gamma_L γfs) ist
                       (16 * Z.of_nat bi + Z.of_nat i)%Z d)%I
      with "[H]" as "H".
    { iApply (big_sepL_impl with "H"). iIntros "!>" (j bi Hj) "Hb".
      iDestruct "Hb" as (ds) "(%Hwf & %Hcpl & Hrecs)".
      rewrite /ireg_recs.
      iApply (big_sepL_impl with "Hrecs"). iIntros "!>" (p i Hp) "Hs".
      apply lookup_seq in Hp as [-> Hlt]. rewrite Nat.add_0_l.
      iExists (ds !!! p). iSplitR; [iPureIntro; exact (Hcpl p Hlt) |].
      iExact "Hs". }
    iApply nested_to_set. iExact "H".
  Qed.

  (* ...AND THE SAME CROSSING BACK (durable-disk EV-Y).  The per-block
     [ds] is not remembered by the wand and does not have to be: it is
     DETERMINED by [m] through [InodeRegion.ireg_couple], so the pure row
     below -- read off the records before they move, at no cost -- is
     everything the reverse needs. *)
  Lemma col_recs_pure (γfs : fs_names) (ist : Z) (nib : nat)
      (m : gmap Z dinode) :
    ([∗ list] bi ∈ seq 0%nat nib,
       ∃ ds : list dinode,
         ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝ ∗ ireg_recs γfs ist bi ds)
    ⊢ ⌜forall bi : nat, (bi < nib)%nat ->
         exists ds : list dinode, diblk_wf ds /\ ireg_couple m bi ds⌝.
  Proof.
    iIntros "H".
    rewrite bi.pure_forall. iIntros (bi).
    rewrite bi.pure_impl. iIntros (Hlt).
    assert (Hlk : seq 0%nat nib !! bi = Some bi) by (apply lookup_seq; lia).
    rewrite (big_sepL_lookup _ _ bi bi Hlk).
    iDestruct "H" as (ds Hwf Hcpl) "_". iPureIntro. by exists ds.
  Qed.

  Lemma col_recs_of_inum (γfs : fs_names) (ist : Z) (nib : nat)
      (m : gmap Z dinode) :
    (forall bi : nat, (bi < nib)%nat ->
       exists ds : list dinode, diblk_wf ds /\ ireg_couple m bi ds) ->
    ([∗ set] z ∈ region_inums nib,
       ∃ d : dinode, ⌜m !! z = Some d⌝
                     ∗ rec_owned_at (fs_gamma_L γfs) ist z d)
    ⊢ [∗ list] bi ∈ seq 0%nat nib,
        ∃ ds : list dinode,
          ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝ ∗ ireg_recs γfs ist bi ds.
  Proof.
    intros Hds. iIntros "H".
    iDestruct (nested_of_set with "H") as "H".
    iApply (big_sepL_impl with "H"). iIntros "!>" (j bi Hj) "Hb".
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    destruct (Hds j Hlt) as (ds & Hwf & Hcpl).
    iExists ds. iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    rewrite /ireg_recs.
    iApply (big_sepL_impl with "Hb"). iIntros "!>" (q i Hq) "Hs".
    apply lookup_seq in Hq as [-> Hlt2]. rewrite Nat.add_0_l.
    iDestruct "Hs" as (d Hd) "Hs".
    rewrite (Hcpl q Hlt2) in Hd. apply (inj Some) in Hd. subst d.
    iExact "Hs".
  Qed.

  (* ==================================================================== *)
  (*  ...AND THE SAME ASSEMBLY AS AN ACCESSOR (durable-disk EV-Y)          *)
  (*                                                                      *)
  (*  NOTHING IS DROPPED HERE ANY MORE.  The era's residue that the        *)
  (*  destructive twin above forgets -- the record PROXY                   *)
  (*  [InodeRegion.dinode_at], the abstract fragment [FsState.top_frag_q], *)
  (*  the region's proxy AUTHORITY, and the quarter each of the three      *)
  (*  metadata objects sheds -- rides this wand's frame.  Three of the     *)
  (*  four go back by an [⊣⊢] ([FsStateDefs.blk_owned_split_34],           *)
  (*  [FsStateInode.rec_owned_at_split_34]); the FREE POOL is the one that *)
  (*  needs an agreement, because its rows hide their bytes under an       *)
  (*  existential, and the agreement is the byte authority the collection  *)
  (*  is holding anyway ([FsCollect.col_free_pool_join]).                  *)
  (*                                                                      *)
  (*  The records cross back block by block with no choice to make: the    *)
  (*  per-block [ds] is determined by [m] ([col_recs_of_inum]).            *)
  (* ==================================================================== *)
  Lemma col_hand_footprint_acc (γfs : fs_names) (γi : gname) (nib : nat)
      (sb : fs_sb) (sbb : list (bv 8)) (used : gset Z) (I : gmap Z fs_node)
      (m : gmap Z dinode) (Lb : gmap Z (bv 8))
      (C : gmap Z (list (bv 8))) (home : gset Z) :
    col_hand γfs γi (FsImg.sb_inodestart sb) nib sb sbb used I m Lb C home
    ⊢ ⌜fs_parse_sb (fun _ => sbb) = Some sb⌝
      ∗ ⌜forall i n, I !! i = Some n -> inode_local i n⌝
      ∗ col_auth γfs Lb C home
      ∗ fs_links (fs_link γfs) I
      ∗ (∃ kv : ity, ireg_keep γfs ireg_root kv)
      ∗ fs_footprint (fs_gamma_L γfs) (DfracOwn (3/4))
          (col_state sb sbb I used)
      ∗ (col_auth γfs Lb C home
         -∗ fs_links (fs_link γfs) I
         -∗ (∃ kv : ity, ireg_keep γfs ireg_root kv)
         -∗ fs_footprint (fs_gamma_L γfs) (DfracOwn (3/4))
              (col_state sb sbb I used)
         -∗ col_hand γfs γi (FsImg.sb_inodestart sb) nib sb sbb used I m
              Lb C home).
  Proof.
    iIntros "Hhand".
    iDestruct "Hhand" as "(%Hg & %Hdi & Hau & Hsb & Hbm & Hrec & Hb & Hlk
                           & Hkeep & %Hdirloc)".
    rewrite /sb_owned. iDestruct "Hsb" as "[Hsbb %Hparse]".
    rewrite /free_bitmap_at. iDestruct "Hbm" as "[Hbmb Hpool]".
    (* ---- the local clauses, off the bundles ---- *)
    iAssert (⌜forall i n, I !! i = Some n -> inode_local i n⌝
             ∧ ([∗ map] i ↦ n ∈ I, col_bundle γfs γi i n))%I
      with "[Hb]" as "[%Hloc Hb]".
    { iSplit; [iApply (col_bundles_local with "Hb") | iExact "Hb"]. }
    (* ---- the records' values, against the region's own authority ---- *)
    rewrite /col_recs. iDestruct "Hrec" as "[Hma Hrows]".
    iAssert (⌜forall i n, I !! i = Some n -> m !! i = Some (fn_rec n)⌝
             ∧ (ghost_map_auth γi 1 m
                ∗ [∗ map] i ↦ n ∈ I, col_bundle γfs γi i n))%I
      with "[Hma Hb]" as "[%Hmrec [Hma Hb]]".
    { iSplit; [| iFrame "Hma Hb"].
      rewrite bi.pure_forall. iIntros (i).
      rewrite bi.pure_forall. iIntros (n).
      rewrite bi.pure_impl. iIntros (Hi).
      iDestruct (big_sepM_lookup _ _ i n Hi with "Hb") as "Hbi".
      iApply (col_bundle_rec with "Hma Hbi"). }
    (* ---- and the per-block coupling, which is all the reverse needs ---- *)
    iAssert (⌜forall bi : nat, (bi < nib)%nat ->
               exists ds : list dinode, diblk_wf ds /\ ireg_couple m bi ds⌝
             ∧ ([∗ list] bi ∈ seq 0%nat nib,
                  ∃ ds : list dinode,
                    ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝
                    ∗ ireg_recs γfs (FsImg.sb_inodestart sb) bi ds))%I
      with "[Hrows]" as "[%Hds Hrows]".
    { iSplit; [iApply (col_recs_pure with "Hrows") | iExact "Hrows"]. }
    (* ---- the records, by inum, zipped with the bundles ---- *)
    iDestruct (col_recs_by_inum γfs γi (FsImg.sb_inodestart sb) nib m
                 with "Hrows") as "Hrecs".
    assert (HdomI : dom I = region_inums nib).
    { apply set_eq. intros z. rewrite region_inums_spec. exact (Hdi z). }
    rewrite -HdomI -big_sepM_dom.
    iAssert ([∗ map] i ↦ n ∈ I,
               rec_owned_at (fs_gamma_L γfs) (FsImg.sb_inodestart sb) i
                 (fn_rec n))%I with "[Hrecs]" as "Hrecs".
    { iApply (big_sepM_impl with "Hrecs"). iIntros "!>" (i n Hi) "Hr".
      iDestruct "Hr" as (d Hd) "Hr".
      rewrite (Hmrec i n Hi) in Hd. apply (inj Some) in Hd. subst d.
      iExact "Hr". }
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Hau Hlk Hkeep".
    (* THE THREE METADATA OBJECTS COME DOWN TO THE UNIFORM SHARE, and the
       quarter each sheds is KEPT (durable-disk EV-Y). *)
    iDestruct (blk_owned_shed _ _ _ (gamma_shed_34 _ (fs_gamma_L_frac γfs))
                 with "Hsbb") as "[Hsbb Hsbb4]".
    iDestruct (blk_owned_shed _ _ _ (gamma_shed_34 _ (fs_gamma_L_frac γfs))
                 with "Hbmb") as "[Hbmb Hbmb4]".
    iDestruct (free_pool_shed _ _ _ (gamma_shed_34 _ (fs_gamma_L_frac γfs))
                 with "Hpool") as "[Hpool Hpool4]".
    (* the per-inode step, as an accessor: the wand column is the frame *)
    iCombine "Hrecs Hb" as "Hpairs". rewrite -big_sepM_sep.
    iAssert ([∗ map] i ↦ n ∈ I,
               (inode_phi (gamma_q (fs_gamma_L γfs) (DfracOwn (3/4))) sb i n
                ∗ (inode_phi (gamma_q (fs_gamma_L γfs) (DfracOwn (3/4)))
                     sb i n
                   -∗ rec_owned_at (fs_gamma_L γfs)
                        (FsImg.sb_inodestart sb) i (fn_rec n)
                      ∗ col_bundle γfs γi i n)))%I
      with "[Hpairs]" as "Hpairs".
    { iApply (big_sepM_impl with "Hpairs"). iIntros "!>" (i n Hi) "[Hr Hbi]".
      iApply (col_bundle_phi_acc γfs γi sb i n with "Hr Hbi"). }
    rewrite big_sepM_sep. iDestruct "Hpairs" as "[Hphis Hws]".
    iSplitL "Hsbb Hphis Hbmb Hpool".
    { rewrite /fs_footprint /col_state /=. iFrame "Hsbb Hphis Hbmb Hpool". }
    (* ---- THE WAY BACK ---- *)
    iIntros "Hau Hlk Hkeep Hfoot".
    rewrite /fs_footprint /col_state /=.
    iDestruct "Hfoot" as "(Hsbb & Hphis & Hbmb & Hpool)".
    iDestruct (blk_owned_join_34 _ (fs_gamma_L_frac γfs)
                 with "Hsbb Hsbb4") as "Hsbb".
    iDestruct (blk_owned_join_34 _ (fs_gamma_L_frac γfs)
                 with "Hbmb Hbmb4") as "Hbmb".
    iDestruct (col_free_pool_join γfs Lb C home (FsImg.sb_size sb) used
                 with "Hau Hpool Hpool4") as "[Hau Hpool]".
    iCombine "Hphis Hws" as "Hp". rewrite -big_sepM_sep.
    iAssert ([∗ map] i ↦ n ∈ I,
               (rec_owned_at (fs_gamma_L γfs) (FsImg.sb_inodestart sb) i
                  (fn_rec n)
                ∗ col_bundle γfs γi i n))%I with "[Hp]" as "Hp".
    { iApply (big_sepM_impl with "Hp"). iIntros "!>" (i n Hi) "[Hphi Hw]".
      iApply ("Hw" with "Hphi"). }
    rewrite big_sepM_sep. iDestruct "Hp" as "[Hrecs Hb]".
    iAssert ([∗ map] i ↦ _ ∈ I,
               ∃ d : dinode, ⌜m !! i = Some d⌝
                 ∗ rec_owned_at (fs_gamma_L γfs) (FsImg.sb_inodestart sb) i d)%I
      with "[Hrecs]" as "Hrecs".
    { iApply (big_sepM_impl with "Hrecs"). iIntros "!>" (i n Hi) "Hr".
      iExists (fn_rec n). iSplitR; [iPureIntro; exact (Hmrec i n Hi) |].
      iExact "Hr". }
    rewrite big_sepM_dom HdomI.
    iDestruct (col_recs_of_inum γfs (FsImg.sb_inodestart sb) nib m Hds
                 with "Hrecs") as "Hrows".
    rewrite /col_hand.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Hau".
    iSplitL "Hsbb".
    { rewrite /sb_owned. iFrame "Hsbb". by iPureIntro. }
    iSplitL "Hbmb Hpool".
    { rewrite /free_bitmap_at. iFrame "Hbmb Hpool". }
    iSplitL "Hma Hrows".
    { rewrite /col_recs. iFrame "Hma Hrows". }
    iFrame "Hb Hlk Hkeep". by iPureIntro.
  Qed.

  (* ...AND THE SAME AT THE WHOLE PREDICATE (durable-disk EV-Y): the exact
     source [FsDurXfer.fs_state_xfer] takes at [q = 3/4], WITH the way
     back.  The transport returns its source unchanged, so this wand is
     all the commit needs to close the six invariant families with the
     bodies it opened them with. *)
  Lemma col_hand_state_acc (γfs : fs_names) (γi : gname) (nib : nat)
      (sb : fs_sb) (sbb : list (bv 8)) (used : gset Z) (I : gmap Z fs_node)
      (m : gmap Z dinode) (Lb : gmap Z (bv 8))
      (C : gmap Z (list (bv 8))) (home : gset Z) :
    col_hand γfs γi (FsImg.sb_inodestart sb) nib sb sbb used I m Lb C home
    ⊢ col_auth γfs Lb C home
      ∗ (∃ kv : ity, ireg_keep γfs ireg_root kv)
      ∗ fs_state (fs_gamma_L γfs) (DfracOwn (3/4)) (col_state sb sbb I used)
      ∗ (col_auth γfs Lb C home
         -∗ (∃ kv : ity, ireg_keep γfs ireg_root kv)
         -∗ fs_state (fs_gamma_L γfs) (DfracOwn (3/4))
              (col_state sb sbb I used)
         -∗ col_hand γfs γi (FsImg.sb_inodestart sb) nib sb sbb used I m
              Lb C home).
  Proof.
    iIntros "Hhand".
    iAssert (⌜fs_geom (col_state sb sbb I used)⌝
             ∧ col_hand γfs γi (FsImg.sb_inodestart sb) nib sb sbb used I m
                 Lb C home)%I with "[Hhand]" as "[%Hgeo Hhand]".
    { iSplit; [iApply (col_fs_geom with "Hhand") | iExact "Hhand"]. }
    iDestruct (col_hand_footprint_acc with "Hhand")
      as "(%Hparse & %Hloc & Hau & Hlk & Hkeep & Hfoot & Hback)".
    iFrame "Hau Hkeep".
    iSplitL "Hfoot Hlk".
    { iApply (fs_state_of (fs_gamma_L γfs) (DfracOwn (3/4))
                (col_state sb sbb I used) with "Hfoot Hlk").
      rewrite /fs_pure /col_state /=.
      iSplitR; [by iPureIntro |].
      iSplitR; [| by iPureIntro].
      iApply big_sepM_intro. iIntros "!>" (i n Hi).
      iPureIntro. exact (Hloc i n Hi). }
    iIntros "Hau Hkeep HS".
    iDestruct (fs_state_to with "HS") as "(Hfoot & Hlk & _)".
    iApply ("Hback" with "Hau Hlk Hkeep Hfoot").
  Qed.

  (* ==================================================================== *)
  (*  THE CORE, AS AN ACCESSOR (durable-disk EV-Y)                          *)
  (*                                                                      *)
  (*  Nothing on the left is spent any more.  The three suppliers hand     *)
  (*  their rows out with their own ways back ([FsCollect.col_row]), the   *)
  (*  partition is DISJOINT so the three columns merge and re-split by the *)
  (*  exact [big_sepS_union], the region's slots and records cross both    *)
  (*  ways, and what comes out is exactly [FsDurXfer.fs_state_xfer]'s      *)
  (*  source at [q = 3/4] beside a wand that puts every body back.  The    *)
  (*  ONE pure row that still travels is [FsDurSnap.snap_shape]'s, which   *)
  (*  no resource pins (durable-fs-plan.md section 2).                     *)
  (* ==================================================================== *)
  Lemma col_bodies_acc
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
     ∗ ([∗ list] bi ∈ seq 0%nat nib,
          ireg_blk γi γfs (FsImg.sb_inodestart sb) m bi)
     ∗ bitmap_res γfs (FsImg.sb_bmapstart sb) (FsImg.sb_size sb) used
     ∗ fsblock (fs_bytes γfs) SB_BNO sbb
     ∗ ipool_rows γfs γi cov ls O
     ∗ ([∗ set] z ∈ X, imark γi z)
     ∗ ic_ids cn ids
     ∗ ([∗ list] k ∈ seq 0%nat NINODE, ic_escrow_body cn γfs γi cov ls k))
    ⊢ ∃ S : fs_state_rec,
        ⌜snap_shape S (col_view C (fs_home_set cov ls))⌝
        ∗ col_auth γfs Lb C (fs_home_set cov ls)
        ∗ (∃ kv : ity, ireg_keep γfs ireg_root kv)
        ∗ fs_state (fs_gamma_L γfs) (DfracOwn (3/4)) S
        ∗ (col_auth γfs Lb C (fs_home_set cov ls)
           -∗ (∃ kv : ity, ireg_keep γfs ireg_root kv)
           -∗ fs_state (fs_gamma_L γfs) (DfracOwn (3/4)) S
           -∗ (ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
               ∗ col_auth γfs Lb C (fs_home_set cov ls)
               ∗ ghost_map_auth (fs_top γfs) 1 I
               ∗ ghost_map_auth γi 1 m
               ∗ ([∗ list] bi ∈ seq 0%nat nib,
                    ireg_blk γi γfs (FsImg.sb_inodestart sb) m bi)
               ∗ bitmap_res γfs (FsImg.sb_bmapstart sb) (FsImg.sb_size sb) used
               ∗ fsblock (fs_bytes γfs) SB_BNO sbb
               ∗ ipool_rows γfs γi cov ls O
               ∗ ([∗ set] z ∈ X, imark γi z)
               ∗ ic_ids cn ids
               ∗ ([∗ list] k ∈ seq 0%nat NINODE,
                    ic_escrow_body cn γfs γi cov ls k))).
  Proof.
    intros Hgeom Hrow Hlen Hparse.
    assert (Hwide : forall z : Z, z ∈ region_inums nib -> 0 <= z < 2 ^ 32).
    { intros z Hz. apply region_inums_spec in Hz.
      pose proof (cg_wide Hgeom) as Hw. lia. }
    assert (HOR : O ⊆ region_inums nib).
    { rewrite Hrow. intros y Hy.
      apply elem_of_union. left. apply elem_of_union. by left. }
    assert (HXR : X ⊆ region_inums nib).
    { rewrite Hrow. intros y Hy.
      apply elem_of_union. left. apply elem_of_union. by right. }
    assert (HLR : ic_live_inums ids ⊆ region_inums nib).
    { rewrite Hrow. intros y Hy. apply elem_of_union. by right. }
    assert (HrO : forall z : Z, z ∈ O -> 0 <= z < 2 ^ 32)
      by (intros y Hy; apply Hwide; by apply HOR).
    assert (HrX : forall z : Z, z ∈ X -> 0 <= z < 2 ^ 32)
      by (intros y Hy; apply Hwide; by apply HXR).
    assert (HrL : forall z : Z, z ∈ ic_live_inums ids -> 0 <= z < 2 ^ 32)
      by (intros y Hy; apply Hwide; by apply HLR).
    assert (Hrootin : ireg_root ∈ region_inums nib).
    { apply region_inums_spec.
      pose proof (sbo_ninodes sb (cg_sbok Hgeom)).
      pose proof (cg_nin Hgeom).
      unfold ireg_root, FsImg.ROOTINO in *. lia. }
    iIntros "(Htx & Hauth & Hi & Hm & Hblks & Hbm & Hsbb & Hpool & Hmks
              & Hids & Hesc)".
    (* ---- the region: records apart from slots, both ways ---- *)
    iDestruct (ireg_blks_collect with "Hblks") as "[Hrecs Hslots]".
    (* ---- the escrows: bodies to covers, and a cover is a body ---- *)
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
    (* ---- the two set-indexed suppliers, as rows ---- *)
    iDestruct (ipool_rows_rows with "Hpool") as "HO".
    iDestruct (imarks_rows γfs γi X HrX with "Hmks") as "HX".
    (* ---- THE PARTITION IS DISJOINT, read off the sides ---- *)
    iAssert (⌜O ## X⌝ ∧ ⌜O ## ic_live_inums ids⌝
             ∧ ⌜X ## ic_live_inums ids⌝
             ∧ (ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
                ∗ ([∗ set] z ∈ region_inums nib, (∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d))
                ∗ ([∗ set] z ∈ O,
                     col_rowz γfs γi z
                       (ipool_ord γfs γi cov ls (mword_of_int z)))
                ∗ ([∗ set] z ∈ X, col_rowz γfs γi z (imark γi z))
                ∗ ([∗ list] k ↦ p ∈ ids,
                     (ic_id cn (0 + k)%nat (1/4) p.1.1 p.1.2 p.2
                      ∗ ic_slot_cover cn γfs γi cov ls (0 + k)%nat))))%I
      with "[Htx Hslots HO HX Hzip]"
      as "(%HdOX & %HdOL & %HdXL & (Htx & Hslots & HO & HX & Hzip))".
    { iSplit.
      { iDestruct (col_rowz_sides with "HO") as "HO'".
        iDestruct (col_rowz_sides with "HX") as "HX'".
        iApply (col_sidez_disj γfs γi m (region_inums nib) O X
                  HOR HXR Hwide with "Htx Hslots HO' HX'"). }
      iSplit.
      { iDestruct (col_rowz_sides with "HO") as "HO'".
        iDestruct (esc_covers_live cn γfs γi cov ls 0%nat ids with "Hzip")
          as "HL".
        iApply (col_sidez_disj γfs γi m (region_inums nib) O
                  (ic_live_inums ids) HOR HLR Hwide
                  with "Htx Hslots HO' HL"). }
      iSplit.
      { iDestruct (col_rowz_sides with "HX") as "HX'".
        iDestruct (esc_covers_live cn γfs γi cov ls 0%nat ids with "Hzip")
          as "HL".
        iApply (col_sidez_disj γfs γi m (region_inums nib) X
                  (ic_live_inums ids) HXR HLR Hwide
                  with "Htx Hslots HX' HL"). }
      iFrame "Htx Hslots HO HX Hzip". }
    assert (HdOXL : (O ∪ X) ## ic_live_inums ids)
      by (apply disjoint_union_l; split; assumption).
    (* ---- the slots, split by supplier ---- *)
    iAssert ((([∗ set] z ∈ O, (∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d)) ∗ ([∗ set] z ∈ X, (∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d)))
             ∗ ([∗ set] z ∈ ic_live_inums ids, (∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d)))%I
      with "[Hslots]" as "[[HslO HslX] HslL]".
    { rewrite -(big_sepS_union
                  (fun z => (∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d)%I) O X HdOX).
      rewrite -(big_sepS_union
                  (fun z => (∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d)%I) (O ∪ X) (ic_live_inums ids) HdOXL).
      rewrite -Hrow. iExact "Hslots". }
    (* ---- THE THREE DOORS ---- *)
    iDestruct (col_rows_got_acc γfs γi m I O
                 (fun z => ipool_ord γfs γi cov ls (mword_of_int z)) HrO
                 with "Htx Hm Hi HO HslO")
      as "(Htx & Hm & Hi & HgO & HbO)".
    iDestruct (col_rows_got_acc γfs γi m I X
                 (fun z => imark γi z) HrX
                 with "Htx Hm Hi HX HslX")
      as "(Htx & Hm & Hi & HgX & HbX)".
    iDestruct (esc_covers_got_acc cn γfs γi cov ls m I 0%nat ids HrL
                 with "Htx Hm Hi Hzip HslL")
      as "(Htx & Hm & Hi & HgL & HbL)".
    (* ---- their union IS the region ---- *)
    iAssert ([∗ set] z ∈ region_inums nib, col_got γfs γi I z)%I
      with "[HgO HgX HgL]" as "Hgots".
    { rewrite Hrow.
      rewrite (big_sepS_union (col_got γfs γi I) (O ∪ X)
                 (ic_live_inums ids) HdOXL).
      rewrite (big_sepS_union (col_got γfs γi I) O X HdOX).
      iFrame "HgO HgX HgL". }
    (* ---- the keep-alive column comes off ---- *)
    iEval (rewrite /col_got) in "Hgots".
    rewrite big_sepS_sep.
    iDestruct "Hgots" as "[HB Hkeeps]".
    iAssert (⌜region_inums nib ⊆ dom I⌝
             ∧ ⌜forall (i : Z) (n : fs_node),
                  i ∈ region_inums nib -> I !! i = Some n ->
                  node_dir_local i icfg_nib n⌝
             ∧ ([∗ set] z ∈ region_inums nib,
                  ∃ n : fs_node,
                    ⌜I !! z = Some n⌝ ∗ ⌜node_dir_local z icfg_nib n⌝
                    ∗ col_bundle γfs γi z n
                    ∗ fs_link_node (fs_link γfs) z n))%I
      with "[HB]" as "(%Hdom & %Hdirl & HB)".
    { iSplit; [iApply (col_bundles_domsub with "HB") |].
      iSplit; [iApply (col_bundles_dirloc with "HB") | iExact "HB"]. }
    rewrite (big_sepS_delete (fun z => (∃ kv : ity, ireg_keep γfs z kv)%I)
               (region_inums nib) ireg_root Hrootin).
    iDestruct "Hkeeps" as "[Hkeep Hkeeps]".
    iDestruct (col_gots_to_hand γfs γi nib I Hdom with "HB")
      as "[Hbund Hlnks]".
    (* ---- and that IS [FsCollect.col_hand] ---- *)
    iAssert (col_hand γfs γi (FsImg.sb_inodestart sb) nib sb sbb used
               (col_reg_map nib I) m Lb C (fs_home_set cov ls))%I
      with "[Hauth Hsbb Hbm Hm Hrecs Hbund Hlnks Hkeep]" as "Hhand".
    { rewrite /col_hand.
      iSplitR; [iPureIntro; exact Hgeom |].
      iSplitR.
      { iPureIntro. intros i.
        rewrite (col_reg_map_dom nib I Hdom). apply region_inums_spec. }
      iFrame "Hauth".
      iSplitL "Hsbb".
      { rewrite /sb_owned gamma_blk_owned.
        iSplitL "Hsbb"; [iExact "Hsbb" | iPureIntro; exact Hparse]. }
      iSplitL "Hbm"; [iExact "Hbm" |].
      iSplitL "Hm Hrecs".
      { rewrite /col_recs. iFrame "Hm Hrecs". }
      iFrame "Hbund Hlnks Hkeep".
      iPureIntro. intros i n Hi.
      apply col_reg_map_lookup in Hi as [HI Hz].
      exact (Hdirl i n Hz HI). }
    (* ---- the one pure row no resource pins ---- *)
    iAssert (⌜snap_shape (col_state sb sbb (col_reg_map nib I) used)
                (col_view C (fs_home_set cov ls))⌝
             ∧ col_hand γfs γi (FsImg.sb_inodestart sb) nib sb sbb used
                 (col_reg_map nib I) m Lb C (fs_home_set cov ls))%I
      with "[Hhand]" as "[%Hsh Hhand]".
    { iSplit; [iApply (col_snap_shape with "Hhand") | iExact "Hhand"]. }
    (* ---- THE SOURCE, AND THE WAY BACK ---- *)
    iDestruct (col_hand_state_acc with "Hhand")
      as "(Hauth & Hkeep & HS & Hhback)".
    iExists (col_state sb sbb (col_reg_map nib I) used).
    iSplitR; [by iPureIntro |]. iFrame "Hauth Hkeep HS".
    iIntros "Hauth Hkeep HS".
    iDestruct ("Hhback" with "Hauth Hkeep HS") as "Hhand".
    rewrite /col_hand.
    iDestruct "Hhand" as "(_ & _ & Hauth & Hsbb & Hbm & Hrec & Hbund & Hlnks
                           & Hkeep & _)".
    rewrite /col_recs. iDestruct "Hrec" as "[Hm Hrecs]".
    iEval (rewrite /sb_owned gamma_blk_owned) in "Hsbb".
    iDestruct "Hsbb" as "[Hsbb _]".
    iDestruct (col_gots_of_hand γfs γi nib I Hdom Hdirl with "[$Hbund $Hlnks]")
      as "HB".
    iAssert ([∗ set] z ∈ region_inums nib, ∃ kv : ity, ireg_keep γfs z kv)%I
      with "[Hkeep Hkeeps]" as "Hkeeps".
    { rewrite (big_sepS_delete (fun z => (∃ kv : ity, ireg_keep γfs z kv)%I)
                 (region_inums nib) ireg_root Hrootin).
      iFrame "Hkeep Hkeeps". }
    iAssert ([∗ set] z ∈ region_inums nib,
               ((∃ n : fs_node,
                   ⌜I !! z = Some n⌝ ∗ ⌜node_dir_local z icfg_nib n⌝
                   ∗ col_bundle γfs γi z n
                   ∗ fs_link_node (fs_link γfs) z n)
                ∗ (∃ kv : ity, ireg_keep γfs z kv)))%I
      with "[HB Hkeeps]" as "Hgots".
    { rewrite big_sepS_sep. iFrame "HB Hkeeps". }
    iAssert ([∗ set] z ∈ region_inums nib, col_got γfs γi I z)%I
      with "[Hgots]" as "Hgots".
    { rewrite /col_got. iExact "Hgots". }
    iAssert ((([∗ set] z ∈ O, col_got γfs γi I z)
              ∗ ([∗ set] z ∈ X, col_got γfs γi I z))
             ∗ ([∗ set] z ∈ ic_live_inums ids, col_got γfs γi I z))%I
      with "[Hgots]" as "[[HgO HgX] HgL]".
    { rewrite -(big_sepS_union (col_got γfs γi I) O X HdOX).
      rewrite -(big_sepS_union (col_got γfs γi I) (O ∪ X)
                  (ic_live_inums ids) HdOXL).
      rewrite -Hrow. iExact "Hgots". }
    iDestruct ("HbO" with "HgO") as "[HO HslO]".
    iDestruct ("HbX" with "HgX") as "[HX HslX]".
    iDestruct ("HbL" with "HgL") as "[Hzip HslL]".
    (* the slots go back to the region *)
    iAssert ([∗ set] z ∈ region_inums nib, (∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d))%I
      with "[HslO HslX HslL]" as "Hslots".
    { rewrite Hrow.
      rewrite (big_sepS_union (fun z => (∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d)%I) (O ∪ X)
                 (ic_live_inums ids) HdOXL).
      rewrite (big_sepS_union (fun z => (∃ d : dinode, ⌜m !! z = Some d⌝ ∗ ireg_slot γfs γi z d)%I) O X HdOX).
      iFrame "HslO HslX HslL". }
    iDestruct (ireg_blks_collect_of γfs γi (FsImg.sb_inodestart sb) m nib
                 with "Hrecs Hslots") as "Hblks".
    (* the covers go back to bodies, and the identities come out of the zip *)
    iAssert (([∗ list] k ↦ p ∈ ids, ic_id cn (0 + k)%nat (1/4)
                                      p.1.1 p.1.2 p.2)
             ∗ ([∗ list] k ↦ p ∈ ids,
                  ic_slot_cover cn γfs γi cov ls (0 + k)%nat))%I
      with "[Hzip]" as "[Hids Hcovs]".
    { rewrite -big_sepL_sep. iExact "Hzip". }
    iAssert (ic_ids cn ids)%I with "[Hids]" as "Hids".
    { rewrite /ic_ids. iApply (big_sepL_impl with "Hids").
      iIntros "!>" (k p Hk) "H". rewrite Nat.add_0_l. iExact "H". }
    iAssert ([∗ list] k ∈ seq 0%nat (length ids),
               ic_slot_cover cn γfs γi cov ls k)%I
      with "[Hcovs]" as "Hcovs".
    { iDestruct (big_sepL_seq_of_list_of ids _ 0%nat with "Hcovs")
        as "Hcovs". iExact "Hcovs". }
    rewrite Hlen.
    iDestruct (ic_slot_cover_bodies with "Hcovs") as "Hesc".
    iFrame "Htx Hauth Hi Hm Hblks Hbm Hids Hesc".
    iSplitL "Hsbb"; [iExact "Hsbb" |].
    iSplitL "HO"; [iApply (ipool_rows_of with "HO") |].
    iApply (big_sepS_impl with "HX"). iIntros "!>" (z Hz) "H". iExact "H".
  Qed.

  (* ==================================================================== *)
  (*  3.  OPENING THE FIFTY ESCROWS AT ONE GHOST STEP                      *)
  (*                                                                      *)
  (*  [inv N P] opens ONCE per namespace ([ns_not_reopenable] above),      *)
  (*  which is why the family sits at [icEscN .@ k]; the induction that     *)
  (*  works is [esc_ns_still_open], and the mask it leaves is the union of  *)
  (*  the slots' own namespaces, not [↑icEscN].                            *)
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
      iMod ("Hclk" with "[Hbody]") as "_"; [iApply bi.later_intro; iExact "Hbody" |].
      done.
  Qed.


  (* ==================================================================== *)
  (*  4.  THE ASSEMBLY                                                     *)
  (*                                                                      *)
  (*  ONE ghost step.  Six invariant families are opened -- [ftopN],       *)
  (*  [iregN], [bitmapN], [sbN], [ipoolN] and the fifty [icEscN .@ k] --   *)
  (*  the collection runs as an ACCESSOR (durable-disk EV-Y) and every one *)
  (*  of them closes with the body it was opened with.  The byte authority *)
  (*  is the CALLER's: [logN] is open at the commit, which is the whole    *)
  (*  reason this lemma takes [col_auth] rather than [fs_bytes_inv].       *)
  (* ==================================================================== *)

  Lemma fs_collect_dur (E : coPset) (cn : ic_names)
      (γfs : fs_names) (γi : gname) (cov : gset Z) (ls : Z) (nib : nat)
      (sb : fs_sb) (Lb : gmap Z (bv 8)) (C : gmap Z (list (bv 8))) :
    col_geom sb (FsImg.sb_inodestart sb) nib (fs_home_set cov ls) ->
    ↑ftopN ⊆ E -> ↑iregN ⊆ E -> ↑bitmapN ⊆ E -> ↑sbN ⊆ E ->
    ↑ipoolN ⊆ E -> ↑icEscN ⊆ E ->
    ireg_reg γi γfs (FsImg.sb_inodestart sb) nib -∗
    bitmap_reg γfs (FsImg.sb_bmapstart sb) cov ls (FsImg.sb_size sb) -∗
    ic_escrows cn γfs γi cov ls -∗
    ipool_inv cn γfs γi cov ls nib -∗
    sb_park γfs sb -∗
    col_auth γfs Lb C (fs_home_set cov ls) -∗
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) ={E}=∗
      P_dur (col_view C (fs_home_set cov ls))
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
    (* ---- THE COLLECTION, AS AN ACCESSOR (durable-disk EV-Y) ---- *)
    iDestruct (col_bodies_acc cn γfs γi cov ls nib sb sbb used m I O X
                 ids Lb C Hgeom Hrow Hlen Hparse
                 with "[$Htx $Hauth $Hta $Hma $Hblks $Hbres $Hsbb $Hrows
                        $Hmks $Hids $Hbodies]")
      as (S) "(%Hsh & Hauth & Hkeep & HS & Hback)".
    (* the epoch's own identity: the source's map sits inside the committed
       view's flattening *)
    iAssert (⌜Lb ⊆ fs_dbytes (col_view C (fs_home_set cov ls))⌝
             ∧ col_auth γfs Lb C (fs_home_set cov ls))%I
      with "[Hauth]" as "[%Hle Hauth]".
    { iSplit; [iApply (col_auth_dbytes with "Hauth") | iExact "Hauth"]. }
    (* the root's keep-alive IS the transport's spare link fragment *)
    assert (Hr : ireg_root = FsImg.ROOTINO) by (vm_compute; reflexivity).
    iDestruct "Hkeep" as (kv) "Hkeep".
    iAssert (own (fs_link γfs) (link_tok_elem FsImg.ROOTINO kv))%I
      with "[Hkeep]" as "Hkeep".
    { rewrite /ireg_keep
        (bool_decide_eq_true_2 (ireg_root = ireg_root) eq_refl).
      rewrite -Hr. iExact "Hkeep". }
    (* ---- THE TRANSPORT IS THE MINT'S CALLER ---- *)
    iMod (P_dur_alloc_xfer (fs_gamma_L γfs) (fs_gamma_L_excl γfs)
            (col_auth γfs Lb C (fs_home_set cov ls)) Lb
            (col_agree γfs Lb C (fs_home_set cov ls)) (3/4)%Qp S
            (col_view C (fs_home_set cov ls)) kv qp_half_lt_34 Hsh Hle
            with "Hauth HS Hkeep") as "(Hauth & HS & Hkeep & Hdur)".
    iAssert (∃ kv : ity, ireg_keep γfs ireg_root kv)%I
      with "[Hkeep]" as "Hkeep".
    { iExists kv. rewrite /ireg_keep
        (bool_decide_eq_true_2 (ireg_root = ireg_root) eq_refl).
      rewrite -Hr. iExact "Hkeep". }
    (* ---- and the source goes back, so every body does ---- *)
    iDestruct ("Hback" with "Hauth Hkeep HS")
      as "(Htx & Hauth & Hta & Hma & Hblks & Hbres & Hsbb & Hrows
           & Hmks & Hids & Hbodies)".
    iMod ("Hcle" with "Hbodies") as "_".
    iMod ("Hclp" with "[$Hrows $Hids $Hmks]") as "_".
    iMod ("Hclsb" with "Hsbb") as "_".
    iMod ("Hclbm" with "[Hbres]") as "_".
    { iApply bi.later_intro. rewrite /bitmap_body. iExists used. iExact "Hbres". }
    iMod ("Hclir" with "[Hma Hblks Hreg]") as "_".
    { iApply bi.later_intro. rewrite /ireg_body. iExists m. iFrame "Hma Hblks Hreg". }
    iMod ("Hclft" with "[Hta Hlk Hpk]") as "_".
    { iApply bi.later_intro. rewrite /ftop_body. iExists I, A. iFrame "Hta Hlk Hpk".
      iPureIntro. exact Hclean. }
    iModIntro. iFrame "Hdur Hauth Htx".
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
    ireg_reg γi γfs (FsImg.sb_inodestart sb) nib -∗
    bitmap_reg γfs (FsImg.sb_bmapstart sb) cov ls (FsImg.sb_size sb) -∗
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
    iMod (fs_collect_dur E cn γfs γi cov ls nib sb Lb C Hgeom
            Hft Hir Hbn Hsn Hpn Hen
            with "Hireg Hbm Hesc Hpool Hpark [Hb] Ht")
      as "(Hdur & Hauth & Ht)".
    { rewrite /col_auth. iFrame "Hb".
      iSplitR; [iPureIntro; exact Hdom |].
      iSplitR; [iPureIntro; exact Hlens |].
      iSplitR; [iPureIntro; exact Htie |].
      iPureIntro; exact Hdm. }
    rewrite /col_auth. iDestruct "Hauth" as "(Hb & _ & _ & _ & _)".
    (* THE EPOCH IS BUILT HERE (durable-disk lane H2), at the file system's
       own ghost step, and the WAL only receives it.  [col_view] IS
       [fs_restrict (dv_of_D C) home], so the registry stands at exactly the
       map the commit jumps to.  SINCE EV-Y IT IS THE TRANSPORT THAT BUILDS
       IT, off the collected [FsState.fs_state] at three quarters, so no
       pure disjointness fact is materialised anywhere on this path. *)
    (* [iFrame] must NOT go first here: [P_dur] is an existential over a
       [∗] whose head conjunct is a byte AUTHORITY, so a bare
       [iFrame "Hb Ht"] happily unifies the SNAPSHOT's fresh gname with the
       ERA's [fs_bytes γfs] and leaves an unclosable goal.  Split the law's
       conjunct off by name first. *)
    iModIntro. rewrite /snap_law_out /col_view.
    iSplitL "Hdur"; [iExact "Hdur" |]. iFrame "Hb Ht".
  Qed.

End CollectAll.
