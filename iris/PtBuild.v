(* PtBuild.v -- the PURE page-table CONSTRUCTION layer: what walk /
   mappages do to a [ptree] description (KvmSpec.v states their specs on
   these predicates; the instruction proofs discharge them).

   - [pt_rep t m]: the tree represents EXACTLY the finite map m
     (vpn -> leaf word); the caller-facing view of a table under
     construction.
   - [ptree_same_rep t t']: same represented map -- walk's frame
     condition (it grows intermediate nodes but never writes a leaf).
   - [ptree_level0 t vpn p2 p1 w0]: the pointer path down to vpn's L0
     slot, whose current word is w0 ([ptree_maps] minus the leaf
     classification) -- walk's return value.
   - [pt_empty_node]: a freshly zeroed PT page as a description node;
     every index blocks through it.
   - the [ptree_set_leaf]-through-a-level0-path lemma family: writing a
     classified leaf through walk's returned slot ([mappages]'s store),
     and the [pt_rep] insertion it induces.
   - grafting (attaching a zeroed child under an invalid slot -- walk's
     allocation arm) lands here next.                                    *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Representation predicates.                                          *)
(* ===================================================================== *)

(* the tree represents EXACTLY the finite map [m] (vpn -> leaf word) *)
Definition pt_rep (t : ptree) (m : gmap (mword 27) (mword 64)) : Prop :=
  (forall vpn w, m !! vpn = Some w -> exists p2 p1, ptree_maps t vpn p2 p1 w) /\
  (forall vpn, m !! vpn = None -> ptree_blocks t vpn).

(* xv6-SHAPED blocking: the walk of [vpn] stops at a slot holding the
   LITERAL ZERO word.  [ptree_blocks] only demands model-invalidity
   ([pte_invalid]) -- too weak for the xv6 walk code, which tests the V
   BIT alone: a reserved-encoding word with V=1 is model-invalid yet the
   C walk would descend it.  Tables built by kvmmake/mappages have zero
   stop words by construction, and every construction lemma preserves
   the shape. *)
Definition ptree_blocks0 (t : ptree) (vpn : mword 27) : Prop :=
  (pt_kids t (vpn_idx 2 vpn) = None /\ pt_ents t (vpn_idx 2 vpn) = mword_of_int 0)
  \/ (exists c1,
        pt_kids t (vpn_idx 2 vpn) = Some c1 /\
        pt_kids c1 (vpn_idx 1 vpn) = None /\
        pte_valid (pt_ents t (vpn_idx 2 vpn)) /\
        pte_ptr (pt_ents t (vpn_idx 2 vpn)) /\
        u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1 /\
        pt_ents c1 (vpn_idx 1 vpn) = mword_of_int 0)
  \/ (exists c1 c0,
        pt_kids t (vpn_idx 2 vpn) = Some c1 /\
        pt_kids c1 (vpn_idx 1 vpn) = Some c0 /\
        pte_valid (pt_ents t (vpn_idx 2 vpn)) /\
        pte_ptr (pt_ents t (vpn_idx 2 vpn)) /\
        pte_valid (pt_ents c1 (vpn_idx 1 vpn)) /\
        pte_ptr (pt_ents c1 (vpn_idx 1 vpn)) /\
        u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1 /\
        u_next_base (pt_ents c1 (vpn_idx 1 vpn)) = pt_base c0 /\
        pt_ents c0 (vpn_idx 0 vpn) = mword_of_int 0).

Lemma pte_invalid_zero : pte_invalid (mword_of_int 0).
Proof. intros s. vm_compute. reflexivity. Qed.

Lemma ptree_blocks0_blocks (t : ptree) (vpn : mword 27) :
  ptree_blocks0 t vpn -> ptree_blocks t vpn.
Proof.
  intros [ (Hk & He) | [ (c1 & Hk2 & Hk1 & Hv & Hp & Hb & He)
                       | (c1 & c0 & Hk2 & Hk1 & Hv2 & Hp2 & Hv1 & Hp1 & Hb1 & Hb0 & He) ] ].
  - left. rewrite He. split; [exact Hk | exact pte_invalid_zero].
  - right. left. exists c1. rewrite He.
    repeat split; try assumption; exact pte_invalid_zero.
  - right. right. exists c1, c0. rewrite He.
    repeat split; try assumption; exact pte_invalid_zero.
Qed.

(* the tree represents [m] IN xv6 SHAPE: exact leaves, ZERO stop words *)
Definition pt_rep0 (t : ptree) (m : gmap (mword 27) (mword 64)) : Prop :=
  (forall vpn w, m !! vpn = Some w -> exists p2 p1, ptree_maps t vpn p2 p1 w) /\
  (forall vpn, m !! vpn = None -> ptree_blocks0 t vpn).

Lemma pt_rep0_rep (t : ptree) (m : gmap (mword 27) (mword 64)) :
  pt_rep0 t m -> pt_rep t m.
Proof.
  intros (Hm & Hb). split; [exact Hm |].
  intros vpn Hl. exact (ptree_blocks0_blocks t vpn (Hb vpn Hl)).
Qed.

(* same represented map, xv6-shaped: walk's frame condition *)
Definition ptree_same_rep0 (t t' : ptree) : Prop :=
  pt_base t' = pt_base t /\
  (forall v p2 p1 p0, ptree_maps t v p2 p1 p0 <-> ptree_maps t' v p2 p1 p0) /\
  (forall v, ptree_blocks0 t v <-> ptree_blocks0 t' v).

Lemma ptree_same_rep0_refl (t : ptree) : ptree_same_rep0 t t.
Proof. split; [reflexivity | split; tauto]. Qed.

Lemma ptree_same_rep0_trans (t t' t'' : ptree) :
  ptree_same_rep0 t t' -> ptree_same_rep0 t' t'' -> ptree_same_rep0 t t''.
Proof.
  intros (Hb & Hm & Hbl) (Hb' & Hm' & Hbl').
  split; [congruence |].
  split; intros; [rewrite Hm; apply Hm' | rewrite Hbl; apply Hbl'].
Qed.

Lemma pt_rep0_same (t t' : ptree) (m : gmap (mword 27) (mword 64)) :
  ptree_same_rep0 t t' -> pt_rep0 t m -> pt_rep0 t' m.
Proof.
  intros (Hb & Hm & Hbl) (Hmap & Hblk). split.
  - intros vpn w Hl. destruct (Hmap vpn w Hl) as (p2 & p1 & Hp).
    exists p2, p1. apply Hm. exact Hp.
  - intros vpn Hl. apply Hbl. exact (Hblk vpn Hl).
Qed.

(* same represented map: what walk's tree-growing preserves *)
Definition ptree_same_rep (t t' : ptree) : Prop :=
  pt_base t' = pt_base t /\
  (forall v p2 p1 p0, ptree_maps t v p2 p1 p0 <-> ptree_maps t' v p2 p1 p0) /\
  (forall v, ptree_blocks t v <-> ptree_blocks t' v).

Lemma ptree_same_rep_refl (t : ptree) : ptree_same_rep t t.
Proof. split; [reflexivity | split; tauto]. Qed.

Lemma ptree_same_rep_trans (t t' t'' : ptree) :
  ptree_same_rep t t' -> ptree_same_rep t' t'' -> ptree_same_rep t t''.
Proof.
  intros (Hb & Hm & Hbl) (Hb' & Hm' & Hbl').
  split; [congruence |].
  split; intros; [rewrite Hm; apply Hm' | rewrite Hbl; apply Hbl'].
Qed.

Lemma pt_rep_same (t t' : ptree) (m : gmap (mword 27) (mword 64)) :
  ptree_same_rep t t' -> pt_rep t m -> pt_rep t' m.
Proof.
  intros (Hb & Hm & Hbl) (Hmap & Hblk). split.
  - intros vpn w Hl. destruct (Hmap vpn w Hl) as (p2 & p1 & Hp).
    exists p2, p1. apply Hm. exact Hp.
  - intros vpn Hl. apply Hbl. exact (Hblk vpn Hl).
Qed.

(* the pointer path down to [vpn]'s L0 slot, whose current word is [w0]
   ([ptree_maps] minus the leaf classification -- walk's return value) *)
Definition ptree_level0 (t : ptree) (vpn : mword 27) (p2 p1 w0 : mword 64) : Prop :=
  exists c1 c0,
    pt_kids t (vpn_idx 2 vpn) = Some c1 /\
    pt_kids c1 (vpn_idx 1 vpn) = Some c0 /\
    pt_ents t (vpn_idx 2 vpn) = p2 /\
    pt_ents c1 (vpn_idx 1 vpn) = p1 /\
    pt_ents c0 (vpn_idx 0 vpn) = w0 /\
    u_next_base p2 = pt_base c1 /\
    u_next_base p1 = pt_base c0 /\
    pte_valid p2 /\ pte_ptr p2 /\
    pte_valid p1 /\ pte_ptr p1.

Lemma ptree_maps_level0 (t : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 -> ptree_level0 t vpn p2 p1 p0.
Proof.
  intros (c1 & c0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & _).
  exists c1, c0. tauto.
Qed.

(* the leaf word mappages writes for page [i] of a run starting at
   physical page [ppn0] with permission bits [perm]: PA2PTE(pa)|perm|V,
   A/D clear -- exactly the loop store *)
Definition mappages_pte (ppn0 : mword 44) (perm : Z) (i : nat) : mword 64 :=
  mk_pte (add_vec_int ppn0 (Z.of_nat i)) (Z.lor perm 1).

(* vpn arithmetic for the page run *)
Definition vpn_at (vpn0 : mword 27) (i : nat) : mword 27 :=
  add_vec_int vpn0 (Z.of_nat i).

(* [m] extended with the first [k] pages of the run *)
Fixpoint pt_insert_run (m : gmap (mword 27) (mword 64))
    (vpn0 : mword 27) (ppn0 : mword 44) (perm : Z) (k : nat)
    : gmap (mword 27) (mword 64) :=
  match k with
  | O => m
  | S k' => <[vpn_at vpn0 k' := mappages_pte ppn0 perm k']>
              (pt_insert_run m vpn0 ppn0 perm k')
  end.

(* ===================================================================== *)
(* §2 The empty node: a freshly zeroed PT page.                           *)
(* ===================================================================== *)

Definition pt_empty_node (b : mword 44) : ptree :=
  PtNode b (fun _ => mword_of_int 0) (fun _ => None).

Lemma pt_empty_node_base (b : mword 44) : pt_base (pt_empty_node b) = b.
Proof. reflexivity. Qed.

(* every vpn's walk stops at the ZERO root slot *)
Lemma ptree_blocks0_empty (b : mword 44) (vpn : mword 27) :
  ptree_blocks0 (pt_empty_node b) vpn.
Proof. left. split; reflexivity. Qed.

Lemma pt_rep0_empty (b : mword 44) : pt_rep0 (pt_empty_node b) ∅.
Proof.
  split.
  - intros vpn w Hl. rewrite lookup_empty in Hl. discriminate.
  - intros vpn _. exact (ptree_blocks0_empty b vpn).
Qed.

(* ===================================================================== *)
(* §3 Writing a leaf through a [ptree_level0] path (mappages' store).     *)
(*    [ptree_set_leaf] itself only follows the kid path, so it applies    *)
(*    verbatim; the [_maps_self]-style lemma needs only the path facts,   *)
(*    not a classified OLD leaf (construction writes over a ZERO slot).   *)
(* ===================================================================== *)

Lemma ptree_set_leaf0_maps_self (t : ptree) (vpn : mword 27)
    (p2 p1 w0 w : mword 64) :
  ptree_level0 t vpn p2 p1 w0 ->
  pte_valid w -> pte_leaf w -> pte_no_napot w -> pte_pbmt0 w ->
  ptree_maps (ptree_set_leaf t vpn w) vpn p2 p1 w.
Proof.
  intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 &
          Hv2 & Hn2 & Hv1 & Hn1) Hv Hl Hnap Hpb.
  unfold ptree_set_leaf. rewrite Hk2. rewrite Hk1.
  exists (pt_upd_kid c1 (vpn_idx 1 vpn)
            (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))),
         (pt_upd_ent c0 (vpn_idx 0 vpn) w).
  rewrite !pt_upd_kid_same !pt_upd_kid_ents !pt_upd_kid_base
          !pt_upd_ent_base !pt_upd_ent_same.
  repeat split; try reflexivity; assumption.
Qed.

(* a DIFFERENT blocked vpn stays blocked: its walk either diverges from
   [vpn]'s path at some level, or shares all three indices -- impossible
   for a different vpn ([vpn_idx_inj]) *)
Lemma ptree_set_leaf0_blocks_other (t : ptree) (vpn vpn' : mword 27)
    (p2 p1 w0 w : mword 64) :
  vpn' <> vpn ->
  ptree_level0 t vpn p2 p1 w0 ->
  ptree_blocks0 t vpn' ->
  ptree_blocks0 (ptree_set_leaf t vpn w) vpn'.
Proof.
  intros Hne (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 &
              Hv2 & Hn2 & Hv1 & Hn1) Hbl.
  unfold ptree_set_leaf. rewrite Hk2. rewrite Hk1.
  destruct Hbl as [ (Hn2' & Hi2)
                  | [ (d1 & Hd2 & Hd1 & Hv2' & Hp2' & Hb1' & Hi1')
                    | (d1 & d0 & Hd2 & Hd1 & Hv2' & Hp2' & Hv1' & Hp1' &
                       Hb1' & Hb0' & Hi0') ] ].
  - (* blocked at root: the root slot of vpn' is kid-free, not vpn's *)
    left.
    destruct (decide (vpn_idx 2 vpn' = vpn_idx 2 vpn)) as [Ei2|Ei2].
    { exfalso. rewrite Ei2 in Hn2'. congruence. }
    rewrite (pt_upd_kid_other _ _ _ _ Ei2) !pt_upd_kid_ents.
    split; assumption.
  - (* blocked at mid level *)
    right. left.
    destruct (decide (vpn_idx 2 vpn' = vpn_idx 2 vpn)) as [Ei2|Ei2].
    2:{ exists d1.
        rewrite (pt_upd_kid_other _ _ _ _ Ei2) !pt_upd_kid_ents.
        repeat split; assumption. }
    rewrite Ei2 in Hd2. rewrite Ei2 in Hv2'. rewrite Ei2 in Hp2'.
    rewrite Ei2 in Hb1'.
    assert (Hd1c : d1 = c1) by congruence. subst d1.
    destruct (decide (vpn_idx 1 vpn' = vpn_idx 1 vpn)) as [Ei1|Ei1].
    { exfalso. rewrite Ei1 in Hd1. congruence. }
    exists (pt_upd_kid c1 (vpn_idx 1 vpn)
              (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))).
    rewrite Ei2 !pt_upd_kid_same !pt_upd_kid_ents !pt_upd_kid_base
      (pt_upd_kid_other _ _ _ _ Ei1).
    repeat split; try reflexivity; assumption.
  - (* blocked at the leaf level: same idx2/idx1 forces a different leaf
       index (else vpn' = vpn) *)
    right. right.
    destruct (decide (vpn_idx 2 vpn' = vpn_idx 2 vpn)) as [Ei2|Ei2].
    2:{ exists d1, d0.
        rewrite (pt_upd_kid_other _ _ _ _ Ei2) !pt_upd_kid_ents.
        repeat split; assumption. }
    rewrite Ei2 in Hd2. rewrite Ei2 in Hv2'. rewrite Ei2 in Hp2'.
    rewrite Ei2 in Hb1'.
    assert (Hd1c : d1 = c1) by congruence. subst d1.
    destruct (decide (vpn_idx 1 vpn' = vpn_idx 1 vpn)) as [Ei1|Ei1].
    2:{ exists (pt_upd_kid c1 (vpn_idx 1 vpn)
                  (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))), d0.
        rewrite Ei2 !pt_upd_kid_same !pt_upd_kid_ents !pt_upd_kid_base
          (pt_upd_kid_other _ _ _ _ Ei1).
        repeat split; try reflexivity; assumption. }
    rewrite Ei1 in Hd1. rewrite Ei1 in Hv1'. rewrite Ei1 in Hp1'.
    rewrite Ei1 in Hb0'.
    assert (Hd0c : d0 = c0) by congruence. subst d0.
    destruct (decide (vpn_idx 0 vpn' = vpn_idx 0 vpn)) as [Ei0|Ei0].
    { exfalso. apply Hne. apply vpn_idx_inj; assumption. }
    exists (pt_upd_kid c1 (vpn_idx 1 vpn)
              (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))),
           (pt_upd_ent c0 (vpn_idx 0 vpn) w).
    rewrite Ei2 Ei1 !pt_upd_kid_same !pt_upd_kid_ents !pt_upd_kid_base
      !pt_upd_ent_base (pt_upd_ent_other _ _ _ _ Ei0).
    repeat split; try reflexivity; assumption.
Qed.

(* the base is untouched *)
Lemma ptree_set_leaf_base (t : ptree) (vpn : mword 27) (w : mword 64) :
  pt_base (ptree_set_leaf t vpn w) = pt_base t.
Proof.
  unfold ptree_set_leaf.
  destruct (pt_kids t (vpn_idx 2 vpn)); [| reflexivity].
  destruct (pt_kids p (vpn_idx 1 vpn)); [| reflexivity].
  apply pt_upd_kid_base.
Qed.

(* THE INSERTION: writing a classified leaf through walk's returned slot
   moves the represented map by one insert (xv6 shape preserved) *)
Lemma pt_rep0_insert (t : ptree) (m : gmap (mword 27) (mword 64))
    (vpn : mword 27) (p2 p1 w0 w : mword 64) :
  pt_rep0 t m ->
  ptree_level0 t vpn p2 p1 w0 ->
  pte_valid w -> pte_leaf w -> pte_no_napot w -> pte_pbmt0 w ->
  pt_rep0 (ptree_set_leaf t vpn w) (<[vpn := w]> m).
Proof.
  intros (Hmap & Hblk) Hl0 Hv Hl Hnap Hpb. split.
  - intros v wv Hlk.
    destruct (decide (v = vpn)) as [-> | Hne].
    + rewrite lookup_insert in Hlk. injection Hlk as <-.
      exists p2, p1.
      exact (ptree_set_leaf0_maps_self t vpn p2 p1 w0 w Hl0 Hv Hl Hnap Hpb).
    + rewrite lookup_insert_ne in Hlk; [| exact (fun He => Hne (eq_sym He))].
      destruct (Hmap v wv Hlk) as (q2 & q1 & Hq).
      exists q2, q1.
      exact (ptree_set_leaf_maps_other t vpn v q2 q1 wv w Hne Hq).
  - intros v Hlk.
    destruct (decide (v = vpn)) as [-> | Hne].
    { rewrite lookup_insert in Hlk. discriminate. }
    rewrite lookup_insert_ne in Hlk; [| exact (fun He => Hne (eq_sym He))].
    exact (ptree_set_leaf0_blocks_other t vpn v p2 p1 w0 w Hne Hl0 (Hblk v Hlk)).
Qed.
