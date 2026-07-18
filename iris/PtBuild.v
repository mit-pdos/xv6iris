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
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree WpDecodeBridge.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
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

(* the V-BIT dichotomy the C walk's raw test needs: a word with bit 0
   clear is model-invalid (the first [pte_is_invalid] disjunct fires
   before any other flag is consulted).  With [pte_valid_invalid_excl]
   this refutes the maps/pointer arms in walk's V=0 branch; in the V=1
   branch, blocks0's zero stop word is refuted by the bit itself. *)
Lemma pte_invalid_bit0 (w : mword 64) :
  Z.testbit (bv_unsigned w) 0 = false ->
  pte_invalid w.
Proof.
  intros Hb s.
  unfold pte_is_invalid.
  rewrite (pte_flags_V_bit0 w Hb).
  rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (eq_vec ('b"0" : mword 1) ('b"0")) with true
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

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

(* ===================================================================== *)
(* §4 Grafting: walk's allocation arm.  A blocked-zero slot at level 2    *)
(*    or 1 receives a pointer PTE to a freshly zeroed page, attached to   *)
(*    the description as [pt_empty_node].  The path facts need no         *)
(*    hypotheses; the represented-map preservation needs the grafted      *)
(*    slot to have been a zero stop word.                                 *)
(* ===================================================================== *)

(* ---- extensionality transports: a vpn's walk facts depend only on the *)
(*      slots/kids its own path touches ------------------------------- *)

Lemma ptree_maps_ext (t t' : ptree) (v : mword 27) (p2 p1 p0 : mword 64) :
  pt_kids t' (vpn_idx 2 v) = pt_kids t (vpn_idx 2 v) ->
  pt_ents t' (vpn_idx 2 v) = pt_ents t (vpn_idx 2 v) ->
  ptree_maps t v p2 p1 p0 -> ptree_maps t' v p2 p1 p0.
Proof.
  intros Hk He (c1 & c0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 &
                H11 & H12 & H13 & H14 & H15).
  exists c1, c0. rewrite Hk He.
  repeat split; assumption.
Qed.

Lemma ptree_blocks0_ext (t t' : ptree) (v : mword 27) :
  pt_kids t' (vpn_idx 2 v) = pt_kids t (vpn_idx 2 v) ->
  pt_ents t' (vpn_idx 2 v) = pt_ents t (vpn_idx 2 v) ->
  ptree_blocks0 t v -> ptree_blocks0 t' v.
Proof.
  intros Hk He [ (Hn & Hi) | [ (c1 & Hk2 & Hk1 & Hv & Hp & Hb & Hi)
                             | (c1 & c0 & Hk2 & Hk1 & Hv2 & Hp2 & Hv1 & Hp1 &
                                Hb1 & Hb0 & Hi) ] ].
  - left. rewrite Hk He. split; assumption.
  - right; left. exists c1. rewrite Hk He. repeat split; assumption.
  - right; right. exists c1, c0. rewrite Hk He. repeat split; assumption.
Qed.

(* the level-1 variants: same root kid objects, agreeing at [v]'s L1 slot *)
Lemma ptree_maps_ext1 (t t' c1 c1' : ptree) (v : mword 27) (p2 p1 p0 : mword 64) :
  pt_kids t (vpn_idx 2 v) = Some c1 ->
  pt_kids t' (vpn_idx 2 v) = Some c1' ->
  pt_ents t' (vpn_idx 2 v) = pt_ents t (vpn_idx 2 v) ->
  pt_base c1' = pt_base c1 ->
  pt_kids c1' (vpn_idx 1 v) = pt_kids c1 (vpn_idx 1 v) ->
  pt_ents c1' (vpn_idx 1 v) = pt_ents c1 (vpn_idx 1 v) ->
  ptree_maps t v p2 p1 p0 -> ptree_maps t' v p2 p1 p0.
Proof.
  intros Hk2 Hk2' He2 Hbb Hk1 He1
         (d1 & c0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 &
          H11 & H12 & H13 & H14 & H15).
  assert (Hd : d1 = c1) by congruence. subst d1.
  exists c1', c0. rewrite Hk2' He2 Hbb Hk1 He1.
  repeat split; first [ assumption | reflexivity ].
Qed.

Lemma ptree_blocks0_ext1 (t t' c1 c1' : ptree) (v : mword 27) :
  pt_kids t (vpn_idx 2 v) = Some c1 ->
  pt_kids t' (vpn_idx 2 v) = Some c1' ->
  pt_ents t' (vpn_idx 2 v) = pt_ents t (vpn_idx 2 v) ->
  pt_base c1' = pt_base c1 ->
  pt_kids c1' (vpn_idx 1 v) = pt_kids c1 (vpn_idx 1 v) ->
  pt_ents c1' (vpn_idx 1 v) = pt_ents c1 (vpn_idx 1 v) ->
  ptree_blocks0 t v -> ptree_blocks0 t' v.
Proof.
  intros Hk2 Hk2' He2 Hbb Hk1 He1
         [ (Hn & Hi) | [ (d1 & Hd2 & Hd1 & Hv & Hp & Hb & Hi)
                       | (d1 & d0 & Hd2 & Hd1 & Hv2 & Hp2 & Hv1 & Hp1 &
                          Hb1 & Hb0 & Hi) ] ].
  - congruence.
  - assert (Hd : d1 = c1) by congruence. subst d1.
    right; left. exists c1'. rewrite Hk2' He2 Hbb Hk1 He1.
    repeat split; first [ assumption | reflexivity ].
  - assert (Hd : d1 = c1) by congruence. subst d1.
    right; right. exists c1', d0. rewrite Hk2' He2 Hbb Hk1 He1.
    repeat split; first [ assumption | reflexivity ].
Qed.

(* ---- the pointer PTE walk writes: PA2PTE(page) | PTE_V --------------- *)

Definition pt_ptr_pte (b : mword 44) : mword 64 := mk_pte b PTE_PTR.

Lemma pt_ptr_pte_valid (b : mword 44) : pte_valid (pt_ptr_pte b).
Proof.
  intros s. unfold pt_ptr_pte.
  match goal with |- context[Mk_PTE_Flags (@subrange_vec_dec ?w _ 7 0)] =>
    change w with 64 end.
  rewrite (mk_pte_flags b PTE_PTR ltac:(unfold PTE_PTR; lia)).
  unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
  rewrite (mk_pte_ext b PTE_PTR ltac:(unfold PTE_PTR; lia)).
  vm_compute. reflexivity.
Qed.

Lemma pt_ptr_pte_ptr (b : mword 44) : pte_ptr (pt_ptr_pte b).
Proof.
  unfold pte_ptr, pt_ptr_pte.
  match goal with |- context[Mk_PTE_Flags (@subrange_vec_dec ?w _ 7 0)] =>
    change w with 64 end.
  rewrite (mk_pte_flags b PTE_PTR ltac:(unfold PTE_PTR; lia)).
  vm_compute. reflexivity.
Qed.

Lemma pt_ptr_pte_base (b : mword 44) : u_next_base (pt_ptr_pte b) = b.
Proof.
  unfold u_next_base, pt_ptr_pte.
  unfold PPN_of_PTE. change (Z.eqb 64 32) with false. cbv iota beta.
  rewrite (mk_pte_ppn_field b PTE_PTR ltac:(unfold PTE_PTR; lia)).
  rewrite !autocast_id. reflexivity.
Qed.

(* the classification pins a POINTER word's extension bits (63:54) to
   zero: [pte_is_invalid]'s nonleaf disjunct (A|D|U|ext<>0) must have
   come out false.  This is what makes the C descend's (w>>10)<<12
   compute the true next-level base ([u_next_base w] * 4096).  The
   proof INVERTS the opaque exec fact at the concrete bridge state:
   peel the or_boolM chain until the nonleaf disjunct's boolean is
   forced false. *)
Lemma pte_valid_ptr_ext0 (w : mword 64) :
  pte_valid w -> pte_ptr w ->
  subrange_vec_dec w 63 54 = (zeros' 10 : mword 10).
Proof.
  intros Hv Hp.
  specialize (Hv dstateM).
  unfold pte_is_invalid in Hv.
  (* disjunct 1: V = 0 *)
  rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ dstateM)) in Hv.
  match type of Hv with (if ?c then _ else _) = _ => destruct c end;
    [discriminate Hv |].
  (* disjunct 2: the shadow-stack and-chain (reads menvcfg) *)
  match type of Hv with
  | exec (or_boolM ?ac _) _ = _ =>
      assert (HAC : exists d2 : bool, exec ac dstateM = Some (d2, dstateM))
  end.
  { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ dstateM)).
    match goal with |- exists _, (if ?c then _ else _) = _ => destruct c end;
      [| eexists; reflexivity].
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ dstateM)).
    match goal with |- exists _, (if ?c then _ else _) = _ => destruct c end;
      [| eexists; reflexivity].
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ dstateM)).
    match goal with |- exists _, (if ?c then _ else _) = _ => destruct c end;
      [| eexists; reflexivity].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg dstateM)).
    eexists. apply exec_returnM. }
  destruct HAC as (d2 & HAC).
  rewrite (exec_or_boolM_Some _ _ _ _ _ HAC) in Hv.
  destruct d2; [discriminate Hv |].
  (* disjunct 3: R=0 & W=1 & X=1 *)
  rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ dstateM)) in Hv.
  match type of Hv with (if ?c then _ else _) = _ => destruct c end;
    [discriminate Hv |].
  (* disjunct 4: nonleaf & (A|D|U|ext<>0) -- the payload *)
  rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ dstateM)) in Hv.
  match type of Hv with (if ?c then _ else _) = _ => destruct c eqn:E3 end;
    [discriminate Hv |].
  clear Hv.
  unfold pte_ptr in Hp. rewrite Hp in E3.
  rewrite andb_true_l in E3.
  apply orb_false_iff in E3. destruct E3 as [_ E3].
  apply orb_false_iff in E3. destruct E3 as [_ E3].
  apply orb_false_iff in E3. destruct E3 as [_ E3].
  unfold neq_vec in E3. apply negb_false_iff in E3.
  apply eq_vec_true_iff in E3.
  unfold ext_bits_of_PTE, Mk_PTE_Ext in E3.
  change (Z.eqb 64 64) with true in E3. cbv beta iota in E3.
  exact E3.
Qed.

(* ---- the two graft operations --------------------------------------- *)

(* attach a zeroed page [b] under the ROOT slot of [vpn]'s path *)
Definition pt_graft2 (t : ptree) (vpn : mword 27) (b : mword 44) : ptree :=
  pt_upd_kid (pt_upd_ent t (vpn_idx 2 vpn) (pt_ptr_pte b))
             (vpn_idx 2 vpn) (Some (pt_empty_node b)).

(* the updated L1 node: a zeroed page [b] under [vpn]'s L1 slot of [c1] *)
Definition pt_graft1_kid (c1 : ptree) (vpn : mword 27) (b : mword 44) : ptree :=
  pt_upd_kid (pt_upd_ent c1 (vpn_idx 1 vpn) (pt_ptr_pte b))
             (vpn_idx 1 vpn) (Some (pt_empty_node b)).

(* attach a zeroed page [b] under the L1 slot of [vpn]'s existing L1 node *)
Definition pt_graft1 (t : ptree) (vpn : mword 27) (b : mword 44) : ptree :=
  match pt_kids t (vpn_idx 2 vpn) with
  | Some c1 => pt_upd_kid t (vpn_idx 2 vpn) (Some (pt_graft1_kid c1 vpn b))
  | None => t
  end.

(* ---- projection laws ------------------------------------------------- *)

Lemma pt_graft2_base (t : ptree) (vpn : mword 27) (b : mword 44) :
  pt_base (pt_graft2 t vpn b) = pt_base t.
Proof. reflexivity. Qed.

Lemma pt_graft2_kid (t : ptree) (vpn : mword 27) (b : mword 44) :
  pt_kids (pt_graft2 t vpn b) (vpn_idx 2 vpn) = Some (pt_empty_node b).
Proof. apply pt_upd_kid_same. Qed.

Lemma pt_graft2_ent (t : ptree) (vpn : mword 27) (b : mword 44) :
  pt_ents (pt_graft2 t vpn b) (vpn_idx 2 vpn) = pt_ptr_pte b.
Proof.
  unfold pt_graft2. rewrite pt_upd_kid_ents. apply pt_upd_ent_same.
Qed.

Lemma pt_graft2_kids_other (t : ptree) (vpn : mword 27) (b : mword 44)
    (j : mword 9) :
  j <> vpn_idx 2 vpn -> pt_kids (pt_graft2 t vpn b) j = pt_kids t j.
Proof.
  intros Hne. unfold pt_graft2.
  rewrite (pt_upd_kid_other _ _ _ _ Hne). apply pt_upd_ent_kids.
Qed.

Lemma pt_graft2_ents_other (t : ptree) (vpn : mword 27) (b : mword 44)
    (j : mword 9) :
  j <> vpn_idx 2 vpn -> pt_ents (pt_graft2 t vpn b) j = pt_ents t j.
Proof.
  intros Hne. unfold pt_graft2.
  rewrite pt_upd_kid_ents. apply (pt_upd_ent_other _ _ _ _ Hne).
Qed.

Lemma pt_graft1_kid_base (c1 : ptree) (vpn : mword 27) (b : mword 44) :
  pt_base (pt_graft1_kid c1 vpn b) = pt_base c1.
Proof. reflexivity. Qed.

Lemma pt_graft1_kid_kid (c1 : ptree) (vpn : mword 27) (b : mword 44) :
  pt_kids (pt_graft1_kid c1 vpn b) (vpn_idx 1 vpn) = Some (pt_empty_node b).
Proof. apply pt_upd_kid_same. Qed.

Lemma pt_graft1_kid_ent (c1 : ptree) (vpn : mword 27) (b : mword 44) :
  pt_ents (pt_graft1_kid c1 vpn b) (vpn_idx 1 vpn) = pt_ptr_pte b.
Proof.
  unfold pt_graft1_kid. rewrite pt_upd_kid_ents. apply pt_upd_ent_same.
Qed.

Lemma pt_graft1_kid_kids_other (c1 : ptree) (vpn : mword 27) (b : mword 44)
    (j : mword 9) :
  j <> vpn_idx 1 vpn -> pt_kids (pt_graft1_kid c1 vpn b) j = pt_kids c1 j.
Proof.
  intros Hne. unfold pt_graft1_kid.
  rewrite (pt_upd_kid_other _ _ _ _ Hne). apply pt_upd_ent_kids.
Qed.

Lemma pt_graft1_kid_ents_other (c1 : ptree) (vpn : mword 27) (b : mword 44)
    (j : mword 9) :
  j <> vpn_idx 1 vpn -> pt_ents (pt_graft1_kid c1 vpn b) j = pt_ents c1 j.
Proof.
  intros Hne. unfold pt_graft1_kid.
  rewrite pt_upd_kid_ents. apply (pt_upd_ent_other _ _ _ _ Hne).
Qed.

Lemma pt_graft1_base (t : ptree) (vpn : mword 27) (b : mword 44) :
  pt_base (pt_graft1 t vpn b) = pt_base t.
Proof.
  unfold pt_graft1. destruct (pt_kids t (vpn_idx 2 vpn)); reflexivity.
Qed.

Lemma pt_graft1_kid_at (t c1 : ptree) (vpn : mword 27) (b : mword 44) :
  pt_kids t (vpn_idx 2 vpn) = Some c1 ->
  pt_kids (pt_graft1 t vpn b) (vpn_idx 2 vpn) = Some (pt_graft1_kid c1 vpn b).
Proof.
  intros Hk2. unfold pt_graft1. rewrite Hk2. apply pt_upd_kid_same.
Qed.

Lemma pt_graft1_ents (t : ptree) (vpn : mword 27) (b : mword 44) (j : mword 9) :
  pt_ents (pt_graft1 t vpn b) j = pt_ents t j.
Proof.
  unfold pt_graft1. destruct (pt_kids t (vpn_idx 2 vpn));
    [apply pt_upd_kid_ents | reflexivity].
Qed.

Lemma pt_graft1_kids_other (t : ptree) (vpn : mword 27) (b : mword 44)
    (j : mword 9) :
  j <> vpn_idx 2 vpn -> pt_kids (pt_graft1 t vpn b) j = pt_kids t j.
Proof.
  intros Hne. unfold pt_graft1. destruct (pt_kids t (vpn_idx 2 vpn));
    [apply (pt_upd_kid_other _ _ _ _ Hne) | reflexivity].
Qed.

(* ---- level0 progress ------------------------------------------------- *)

(* the generic [ptree_level0] introduction (also serves blocks0's arm 3) *)
Lemma ptree_level0_intro (t c1 c0 : ptree) (vpn : mword 27) :
  pt_kids t (vpn_idx 2 vpn) = Some c1 ->
  pt_kids c1 (vpn_idx 1 vpn) = Some c0 ->
  pte_valid (pt_ents t (vpn_idx 2 vpn)) ->
  pte_ptr (pt_ents t (vpn_idx 2 vpn)) ->
  pte_valid (pt_ents c1 (vpn_idx 1 vpn)) ->
  pte_ptr (pt_ents c1 (vpn_idx 1 vpn)) ->
  u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1 ->
  u_next_base (pt_ents c1 (vpn_idx 1 vpn)) = pt_base c0 ->
  ptree_level0 t vpn (pt_ents t (vpn_idx 2 vpn)) (pt_ents c1 (vpn_idx 1 vpn))
    (pt_ents c0 (vpn_idx 0 vpn)).
Proof.
  intros Hk2 Hk1 Hv2 Hp2 Hv1 Hp1 Hb1 Hb0.
  exists c1, c0. repeat split; first [ assumption | reflexivity ].
Qed.

(* after the L1 graft, [vpn]'s pointer path reaches L0 with a ZERO slot *)
Lemma pt_graft1_level0 (t c1 : ptree) (vpn : mword 27) (b : mword 44) :
  pt_kids t (vpn_idx 2 vpn) = Some c1 ->
  pte_valid (pt_ents t (vpn_idx 2 vpn)) ->
  pte_ptr (pt_ents t (vpn_idx 2 vpn)) ->
  u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1 ->
  ptree_level0 (pt_graft1 t vpn b) vpn
    (pt_ents t (vpn_idx 2 vpn)) (pt_ptr_pte b) (mword_of_int 0).
Proof.
  intros Hk2 Hv2 Hp2 Hb1.
  exists (pt_graft1_kid c1 vpn b), (pt_empty_node b).
  rewrite (pt_graft1_kid_at t c1 vpn b Hk2) pt_graft1_kid_kid
          (pt_graft1_ents t vpn b) pt_graft1_kid_ent pt_graft1_kid_base.
  repeat split;
    first [ assumption | reflexivity
          | exact (pt_ptr_pte_valid b) | exact (pt_ptr_pte_ptr b)
          | exact (pt_ptr_pte_base b) ].
Qed.

(* ---- represented-map preservation ------------------------------------ *)

Lemma pt_graft2_same_rep0 (t : ptree) (vpn : mword 27) (b : mword 44) :
  pt_kids t (vpn_idx 2 vpn) = None ->
  pt_ents t (vpn_idx 2 vpn) = mword_of_int 0 ->
  ptree_same_rep0 t (pt_graft2 t vpn b).
Proof.
  intros Hk He. split; [apply pt_graft2_base | split].
  - (* maps *)
    intros v p2 p1 p0.
    destruct (decide (vpn_idx 2 v = vpn_idx 2 vpn)) as [Ei | Ei].
    + split; intros (c1 & c0 & H1 & H2 & _); exfalso.
      * rewrite Ei in H1. congruence.
      * rewrite Ei in H1. rewrite pt_graft2_kid in H1.
        injection H1 as H1. subst c1. cbn in H2. discriminate.
    + split; intro Hm.
      * exact (ptree_maps_ext t (pt_graft2 t vpn b) v p2 p1 p0
                 (pt_graft2_kids_other t vpn b _ Ei)
                 (pt_graft2_ents_other t vpn b _ Ei) Hm).
      * exact (ptree_maps_ext (pt_graft2 t vpn b) t v p2 p1 p0
                 (eq_sym (pt_graft2_kids_other t vpn b _ Ei))
                 (eq_sym (pt_graft2_ents_other t vpn b _ Ei)) Hm).
  - (* blocks0 *)
    intros v.
    destruct (decide (vpn_idx 2 v = vpn_idx 2 vpn)) as [Ei | Ei].
    + (* both sides hold outright *)
      split; intros _.
      * right; left. exists (pt_empty_node b).
        rewrite Ei pt_graft2_kid pt_graft2_ent.
        repeat split;
          first [ reflexivity | exact (pt_ptr_pte_valid b)
                | exact (pt_ptr_pte_ptr b) | exact (pt_ptr_pte_base b) ].
      * left. rewrite Ei. split; assumption.
    + split; intro Hb.
      * exact (ptree_blocks0_ext t (pt_graft2 t vpn b) v
                 (pt_graft2_kids_other t vpn b _ Ei)
                 (pt_graft2_ents_other t vpn b _ Ei) Hb).
      * exact (ptree_blocks0_ext (pt_graft2 t vpn b) t v
                 (eq_sym (pt_graft2_kids_other t vpn b _ Ei))
                 (eq_sym (pt_graft2_ents_other t vpn b _ Ei)) Hb).
Qed.

Lemma pt_graft1_same_rep0 (t c1 : ptree) (vpn : mword 27) (b : mword 44) :
  pt_kids t (vpn_idx 2 vpn) = Some c1 ->
  pt_kids c1 (vpn_idx 1 vpn) = None ->
  pt_ents c1 (vpn_idx 1 vpn) = mword_of_int 0 ->
  ptree_same_rep0 t (pt_graft1 t vpn b).
Proof.
  intros Hk2 Hk1 He1.
  pose proof (pt_graft1_kid_at t c1 vpn b Hk2) as Hat.
  split; [apply pt_graft1_base | split].
  - (* maps *)
    intros v p2 p1 p0.
    destruct (decide (vpn_idx 2 v = vpn_idx 2 vpn)) as [Ei2 | Ei2].
    + destruct (decide (vpn_idx 1 v = vpn_idx 1 vpn)) as [Ei1 | Ei1].
      * (* both sides refutable *)
        split;
          intros (d1 & d0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 &
                  H10 & H11 & H12 & H13 & H14 & H15); exfalso.
        -- rewrite Ei2 in H1.
           assert (Hd : d1 = c1) by congruence. subst d1.
           rewrite Ei1 in H2. congruence.
        -- rewrite Ei2 in H1. rewrite Hat in H1.
           injection H1 as H1. subst d1.
           rewrite Ei1 in H2. rewrite pt_graft1_kid_kid in H2.
           injection H2 as H2. subst d0.
           cbn in H5. subst p0.
           exact (pte_valid_invalid_excl _ H12 pte_invalid_zero).
      * (* same root chunk, different L1 chunk: level-1 transport *)
        split; intro Hm.
        -- exact (ptree_maps_ext1 t (pt_graft1 t vpn b) c1
                    (pt_graft1_kid c1 vpn b) v p2 p1 p0
                    ltac:(rewrite Ei2; exact Hk2)
                    ltac:(rewrite Ei2; exact Hat)
                    (pt_graft1_ents t vpn b _)
                    (pt_graft1_kid_base c1 vpn b)
                    (pt_graft1_kid_kids_other c1 vpn b _ Ei1)
                    (pt_graft1_kid_ents_other c1 vpn b _ Ei1) Hm).
        -- exact (ptree_maps_ext1 (pt_graft1 t vpn b) t
                    (pt_graft1_kid c1 vpn b) c1 v p2 p1 p0
                    ltac:(rewrite Ei2; exact Hat)
                    ltac:(rewrite Ei2; exact Hk2)
                    (eq_sym (pt_graft1_ents t vpn b _))
                    (eq_sym (pt_graft1_kid_base c1 vpn b))
                    (eq_sym (pt_graft1_kid_kids_other c1 vpn b _ Ei1))
                    (eq_sym (pt_graft1_kid_ents_other c1 vpn b _ Ei1)) Hm).
    + split; intro Hm.
      * exact (ptree_maps_ext t (pt_graft1 t vpn b) v p2 p1 p0
                 (pt_graft1_kids_other t vpn b _ Ei2)
                 (pt_graft1_ents t vpn b _) Hm).
      * exact (ptree_maps_ext (pt_graft1 t vpn b) t v p2 p1 p0
                 (eq_sym (pt_graft1_kids_other t vpn b _ Ei2))
                 (eq_sym (pt_graft1_ents t vpn b _)) Hm).
  - (* blocks0 *)
    intros v.
    destruct (decide (vpn_idx 2 v = vpn_idx 2 vpn)) as [Ei2 | Ei2].
    + destruct (decide (vpn_idx 1 v = vpn_idx 1 vpn)) as [Ei1 | Ei1].
      * (* arm 2 of t <-> arm 3 of the grafted tree *)
        split; intro Hb.
        -- destruct Hb as [ (Hn & _) | [ (d1 & Hd2 & Hd1 & Hv & Hp & Hbb & Hi)
                                       | (d1 & d0 & Hd2 & Hd1 & _) ] ].
           ++ exfalso. rewrite Ei2 in Hn. congruence.
           ++ rewrite Ei2 in Hd2.
              assert (Hd : d1 = c1) by congruence. subst d1.
              rewrite Ei2 in Hv. rewrite Ei2 in Hp. rewrite Ei2 in Hbb.
              right; right.
              exists (pt_graft1_kid c1 vpn b), (pt_empty_node b).
              rewrite Ei2 Ei1 Hat pt_graft1_kid_kid
                      (pt_graft1_ents t vpn b (vpn_idx 2 vpn))
                      pt_graft1_kid_ent pt_graft1_kid_base.
              repeat split;
                first [ assumption | reflexivity
                      | exact (pt_ptr_pte_valid b) | exact (pt_ptr_pte_ptr b)
                      | exact (pt_ptr_pte_base b) ].
           ++ exfalso. rewrite Ei2 in Hd2.
              assert (Hd : d1 = c1) by congruence. subst d1.
              rewrite Ei1 in Hd1. congruence.
        -- destruct Hb as [ (Hn & _) | [ (d1 & Hd2 & Hd1 & _)
                                       | (d1 & d0 & Hd2 & Hd1 & Hv2 & Hp2 &
                                          Hv1 & Hp1 & Hb1 & Hb0 & Hi) ] ].
           ++ exfalso. rewrite Ei2 in Hn. congruence.
           ++ exfalso. rewrite Ei2 in Hd2. rewrite Hat in Hd2.
              injection Hd2 as Hd2. subst d1.
              rewrite Ei1 in Hd1. rewrite pt_graft1_kid_kid in Hd1.
              congruence.
           ++ rewrite Ei2 in Hd2. rewrite Hat in Hd2.
              injection Hd2 as Hd2. subst d1.
              rewrite (pt_graft1_ents t vpn b (vpn_idx 2 v)) in Hv2.
              rewrite (pt_graft1_ents t vpn b (vpn_idx 2 v)) in Hp2.
              rewrite (pt_graft1_ents t vpn b (vpn_idx 2 v)) in Hb1.
              rewrite pt_graft1_kid_base in Hb1.
              rewrite Ei2 in Hv2. rewrite Ei2 in Hp2. rewrite Ei2 in Hb1.
              right; left. exists c1.
              rewrite Ei2 Ei1.
              repeat split; assumption.
      * (* same root chunk, different L1 chunk: level-1 transport *)
        split; intro Hb.
        -- exact (ptree_blocks0_ext1 t (pt_graft1 t vpn b) c1
                    (pt_graft1_kid c1 vpn b) v
                    ltac:(rewrite Ei2; exact Hk2)
                    ltac:(rewrite Ei2; exact Hat)
                    (pt_graft1_ents t vpn b _)
                    (pt_graft1_kid_base c1 vpn b)
                    (pt_graft1_kid_kids_other c1 vpn b _ Ei1)
                    (pt_graft1_kid_ents_other c1 vpn b _ Ei1) Hb).
        -- exact (ptree_blocks0_ext1 (pt_graft1 t vpn b) t
                    (pt_graft1_kid c1 vpn b) c1 v
                    ltac:(rewrite Ei2; exact Hat)
                    ltac:(rewrite Ei2; exact Hk2)
                    (eq_sym (pt_graft1_ents t vpn b _))
                    (eq_sym (pt_graft1_kid_base c1 vpn b))
                    (eq_sym (pt_graft1_kid_kids_other c1 vpn b _ Ei1))
                    (eq_sym (pt_graft1_kid_ents_other c1 vpn b _ Ei1)) Hb).
    + split; intro Hb.
      * exact (ptree_blocks0_ext t (pt_graft1 t vpn b) v
                 (pt_graft1_kids_other t vpn b _ Ei2)
                 (pt_graft1_ents t vpn b _) Hb).
      * exact (ptree_blocks0_ext (pt_graft1 t vpn b) t v
                 (eq_sym (pt_graft1_kids_other t vpn b _ Ei2))
                 (eq_sym (pt_graft1_ents t vpn b _)) Hb).
Qed.

(* ===================================================================== *)
(* §5 The Iris layer: a kalloc'd+memset ZEROED page becomes a description *)
(*    node ([zero_page_to_node]); grafting it into an owned tree under a  *)
(*    freshly written pointer-PTE slot ([ptree_own_graft2/_graft1]); the  *)
(*    read-only slot accessors walk's descend reads use; and the L0-slot  *)
(*    accessor mappages' remap-check read + leaf store go through.        *)
(* ===================================================================== *)

Section PtBuildIris.
  Context `{!riscvGS Σ}.

  (* the Pt4kWalk address facts at PtTree's [u_pte_addr] spelling
     (identical definitions; [exact] bridges by conversion) *)
  Local Lemma u_pte_addr_aligned8 (b : mword 44) (i : mword 9) :
    is_aligned_paddr (Physaddr (u_pte_addr b i)) 8 = true.
  Proof. exact (pte_addr_at_aligned8 b i). Qed.

  Local Lemma pa_add_page_slot_u (b : mword 44) (i j : nat) :
    (i < 512)%nat -> (j < 8)%nat ->
    pa_add (zero_extend' 64 (concat_vec b (zeros' 12 : mword 12))) (i * 8 + j)
    = pa_add (u_pte_addr b (mword_of_int (Z.of_nat i))) j.
  Proof. exact (pa_add_page_slot b i j). Qed.

  (* byte [j] of the zero word *)
  Lemma nth_byte_zero (j : nat) :
    nth_byte (mword_of_int 0 : mword 64) j = (mword_of_int 0 : mword 8).
  Proof.
    apply bv_eq. unfold nth_byte.
    rewrite bv_extract_unsigned.
    replace (bv_unsigned (mword_of_int 0 : mword 64)) with 0
      by (vm_compute; reflexivity).
    rewrite Z.shiftr_0_l.
    unfold bv_wrap. rewrite Zmod_0_l.
    vm_compute. reflexivity.
  Qed.

  (* chunk a flat byte run into fixed-size blocks *)
  Lemma big_sepL_seq_chunk (Φ : nat -> iProp Σ) (k n : nat) :
    ([∗ list] j ∈ seq 0 (k * n), Φ j) ⊣⊢
    ([∗ list] i ∈ seq 0 k, [∗ list] j ∈ seq 0 n, Φ (i * n + j)%nat).
  Proof.
    induction k as [| k IH]; [reflexivity |].
    replace (S k * n)%nat with (k * n + n)%nat by lia.
    rewrite seq_app big_sepL_app IH.
    replace (S k) with (k + 1)%nat by lia.
    rewrite seq_app big_sepL_app.
    cbn [seq Nat.add]. rewrite big_sepL_singleton.
    f_equiv.
    rewrite <- (big_sepL_fmap (Nat.add (k * n)) (fun _ j => Φ j) (seq 0 n)).
    rewrite fmap_add_seq.
    replace (k * n + 0)%nat with (k * n)%nat by lia.
    reflexivity.
  Qed.

  (* 4096 zero bytes at ppn [b]'s page = a zeroed description node (at
     any level: an empty node has no kids, so the kid conjunct is free) *)
  Lemma zero_page_to_node (lvl : nat) (dq : dfrac) (b : mword 44) :
    ([∗ list] j ∈ seq 0 4096,
       mem_pointsto
         (pa_add (zero_extend' 64 (concat_vec b (zeros' 12 : mword 12))) j)
         dq (mword_of_int 0 : mword 8))
    ⊢ ptree_own lvl dq (pt_empty_node b).
  Proof.
    iIntros "Hbytes".
    iAssert (pt_page_own dq (pt_empty_node b)) with "[Hbytes]" as "Hpg".
    { iEval (change 4096%nat with (512 * 8)%nat) in "Hbytes".
      iEval (rewrite big_sepL_seq_chunk) in "Hbytes".
      rewrite /pt_page_own /seqZ.
      rewrite big_sepL_fmap.
      iEval (change (Z.to_nat 512) with 512%nat).
      iApply (big_sepL_mono with "Hbytes").
      intros k i Hki. apply lookup_seq in Hki. destruct Hki as [-> Hlt].
      cbn [Nat.add pt_base pt_ents pt_empty_node].
      replace (Z.of_nat k + 0) with (Z.of_nat k) by lia.
      iIntros "Hb".
      iApply word_pointsto_intro.
      { exact (u_pte_addr_aligned8 b (mword_of_int (Z.of_nat k))). }
      iApply (big_sepL_mono with "Hb").
      intros k' j Hkj. apply lookup_seq in Hkj. destruct Hkj as [-> Hjlt].
      cbn [Nat.add].
      rewrite nth_byte_zero.
      rewrite (pa_add_page_slot_u b k k' Hlt Hjlt).
      reflexivity.
    }
    destruct lvl.
    - iSplitL "Hpg"; [iExact "Hpg" | done].
    - iSplitL "Hpg"; [iExact "Hpg" |].
      iApply big_sepL_intro. iIntros "!>" (k i Hki). simpl. done.
  Qed.

  (* insert a child under a kid-free index (the big-op slot was [emp]) *)
  Lemma pt_kids_own_ins (lvl : nat) (dq : dfrac) (t : ptree) (i : mword 9) :
    pt_kids t i = None ->
    pt_kids_own lvl dq t ⊢
      ∀ c' : ptree,
        ptree_own lvl dq c' -∗
        pt_kids_own lvl dq (pt_upd_kid t i (Some c')).
  Proof.
    intros Hk.
    pose proof (bv_unsigned_in_range _ i) as Hir.
    assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 9) = 512)
      by (vm_compute; reflexivity).
    rewrite Hm in Hir.
    assert (Hlk : seqZ 0 512 !! Z.to_nat (bv_unsigned i) = Some (bv_unsigned i)).
    { apply lookup_seqZ. split; lia. }
    iIntros "Hks" (c') "Hc".
    rewrite /pt_kids_own.
    rewrite (big_sepL_delete
               (fun _ j => (match pt_kids (pt_upd_kid t i (Some c')) (mword_of_int j) with
                            | Some cc => ptree_own lvl dq cc
                            | None => emp end)%I)
               _ _ _ Hlk).
    iSplitL "Hc".
    { rewrite pt_mword9_id pt_upd_kid_same. iExact "Hc". }
    iEval (rewrite (big_sepL_delete _ _ _ _ Hlk)) in "Hks".
    iDestruct "Hks" as "[_ Hks]".
    iApply (big_sepL_mono with "Hks").
    intros k j Hkj. cbn beta.
    case_decide as Hkk; [reflexivity |].
    rewrite pt_upd_kid_other; [reflexivity |].
    apply lookup_seqZ in Hkj. destruct Hkj as [-> Hjlt].
    intros Heq. apply Hkk.
    apply (f_equal bv_unsigned) in Heq.
    rewrite pt_mword9_unsigned in Heq; [| lia].
    lia.
  Qed.

  (* ---- read-only slot accessors (walk's descend reads) ---------------- *)

  Lemma ptree_own_slot2_ro (dq : dfrac) (t : ptree) (vpn : mword 27) :
    ptree_own 2 dq t ⊢
      pt_addr2 t vpn ↦₈{dq} pt_ents t (vpn_idx 2 vpn) ∗
      (pt_addr2 t vpn ↦₈{dq} pt_ents t (vpn_idx 2 vpn) -∗ ptree_own 2 dq t).
  Proof.
    iIntros "[Hpg Hks]".
    iDestruct (pt_page_own_acc_ro dq t (vpn_idx 2 vpn) with "Hpg") as "[Hs2 Hpg]".
    iFrame "Hs2". iIntros "Hs2".
    iSplitL "Hpg Hs2"; [(iApply "Hpg"; iExact "Hs2") | iExact "Hks"].
  Qed.

  Lemma ptree_own_slot1_ro (dq : dfrac) (t c1 : ptree) (vpn : mword 27) :
    pt_kids t (vpn_idx 2 vpn) = Some c1 ->
    u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1 ->
    ptree_own 2 dq t ⊢
      pt_addr1 (pt_ents t (vpn_idx 2 vpn)) vpn ↦₈{dq} pt_ents c1 (vpn_idx 1 vpn) ∗
      (pt_addr1 (pt_ents t (vpn_idx 2 vpn)) vpn ↦₈{dq} pt_ents c1 (vpn_idx 1 vpn) -∗
       ptree_own 2 dq t).
  Proof.
    intros Hk2 Hb1.
    iIntros "[Hpg Hks]".
    iDestruct (pt_kids_own_acc_ro 1 dq t (vpn_idx 2 vpn) c1 Hk2 with "Hks") as "[Hc1 Hks]".
    iDestruct "Hc1" as "[Hpg1 Hks1]".
    iDestruct (pt_page_own_acc_ro dq c1 (vpn_idx 1 vpn) with "Hpg1") as "[Hs1 Hpg1]".
    unfold pt_addr1. rewrite Hb1.
    iFrame "Hs1". iIntros "Hs1".
    iSplitL "Hpg"; [iExact "Hpg" |].
    iApply "Hks".
    iSplitL "Hpg1 Hs1"; [(iApply "Hpg1"; iExact "Hs1") | iExact "Hks1"].
  Qed.

  (* ---- grafting a zeroed child into the owned tree --------------------- *)

  (* ROOT graft: the root slot cell comes out (walk reads it, sees V=0,
     writes the pointer PTE); the closing wand takes the rewritten cell +
     the zeroed child and yields ownership of the grafted tree *)
  Lemma ptree_own_graft2 (dq : dfrac) (t : ptree) (vpn : mword 27) (b : mword 44) :
    pt_kids t (vpn_idx 2 vpn) = None ->
    ptree_own 2 dq t ⊢
      pt_addr2 t vpn ↦₈{dq} pt_ents t (vpn_idx 2 vpn) ∗
      (pt_addr2 t vpn ↦₈{dq} pt_ptr_pte b -∗
       ptree_own 1 dq (pt_empty_node b) -∗
       ptree_own 2 dq (pt_graft2 t vpn b)).
  Proof.
    intros Hk.
    iIntros "[Hpg Hks]".
    iDestruct (pt_page_own_acc dq t (vpn_idx 2 vpn) with "Hpg") as "[Hs2 Hpg]".
    iFrame "Hs2".
    iIntros "Hs2 Hc".
    iSpecialize ("Hpg" $! (pt_ptr_pte b) with "Hs2").
    iDestruct (pt_kids_own_ins 1 dq t (vpn_idx 2 vpn) Hk with "Hks") as "Hks".
    iSpecialize ("Hks" $! (pt_empty_node b) with "Hc").
    rewrite ptree_own_S.
    iSplitL "Hpg"; [iExact "Hpg" | iExact "Hks"].
  Qed.

  (* L1 graft: [vpn]'s L1 slot cell (inside the existing kid [c1]) comes
     out; the closing wand takes the rewritten cell + the zeroed child *)
  Lemma ptree_own_graft1 (dq : dfrac) (t c1 : ptree) (vpn : mword 27) (b : mword 44) :
    pt_kids t (vpn_idx 2 vpn) = Some c1 ->
    pt_kids c1 (vpn_idx 1 vpn) = None ->
    u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1 ->
    ptree_own 2 dq t ⊢
      pt_addr1 (pt_ents t (vpn_idx 2 vpn)) vpn ↦₈{dq} pt_ents c1 (vpn_idx 1 vpn) ∗
      (pt_addr1 (pt_ents t (vpn_idx 2 vpn)) vpn ↦₈{dq} pt_ptr_pte b -∗
       ptree_own 0 dq (pt_empty_node b) -∗
       ptree_own 2 dq (pt_graft1 t vpn b)).
  Proof.
    intros Hk2 Hk1 Hb1.
    iIntros "[Hpg Hks]".
    iDestruct (pt_kids_own_acc 1 dq t (vpn_idx 2 vpn) c1 Hk2 with "Hks") as "[Hc1 Hks]".
    iDestruct "Hc1" as "[Hpg1 Hks1]".
    iDestruct (pt_page_own_acc dq c1 (vpn_idx 1 vpn) with "Hpg1") as "[Hs1 Hpg1]".
    unfold pt_addr1. rewrite Hb1.
    iFrame "Hs1".
    iIntros "Hs1 Hc".
    iSpecialize ("Hpg1" $! (pt_ptr_pte b) with "Hs1").
    iDestruct (pt_kids_own_ins 0 dq c1 (vpn_idx 1 vpn) Hk1 with "Hks1") as "Hks1".
    iSpecialize ("Hks1" $! (pt_empty_node b) with "Hc").
    iSpecialize ("Hks" $! (pt_graft1_kid c1 vpn b) with "[Hpg1 Hks1]").
    { rewrite ptree_own_S.
      iSplitL "Hpg1"; [iExact "Hpg1" | iExact "Hks1"]. }
    rewrite /pt_graft1 Hk2.
    rewrite ptree_own_S.
    iSplitL "Hpg"; [iExact "Hpg" | iExact "Hks"].
  Qed.

  (* ---- the L0-slot accessor (mappages' remap-check read + leaf store) - *)

  Lemma ptree_own_level0_upd (dq : dfrac) (t : ptree) (vpn : mword 27)
      (p2 p1 w0 : mword 64) :
    ptree_level0 t vpn p2 p1 w0 ->
    ptree_own 2 dq t ⊢
      pt_addr0 p1 vpn ↦₈{dq} w0 ∗
      (∀ w' : mword 64,
         pt_addr0 p1 vpn ↦₈{dq} w' -∗
         ptree_own 2 dq (ptree_set_leaf t vpn w')).
  Proof.
    intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 & _).
    iIntros "[Hpg Hks]".
    iDestruct (pt_kids_own_acc 1 dq t (vpn_idx 2 vpn) c1 Hk2 with "Hks") as "[Hc1 Hks]".
    iDestruct "Hc1" as "[Hpg1 Hks1]".
    iDestruct (pt_kids_own_acc 0 dq c1 (vpn_idx 1 vpn) c0 Hk1 with "Hks1") as "[Hc0 Hks1]".
    iDestruct "Hc0" as "[Hpg0 Hemp]".
    iDestruct (pt_page_own_acc dq c0 (vpn_idx 0 vpn) with "Hpg0") as "[Hs0 Hpg0]".
    rewrite He0.
    unfold pt_addr0. rewrite Hb0.
    iFrame "Hs0".
    iIntros (w') "Hs0".
    unfold ptree_set_leaf. rewrite Hk2. rewrite Hk1.
    rewrite ptree_own_S.
    iSplitL "Hpg"; [iExact "Hpg" |].
    iApply "Hks".
    rewrite ptree_own_S.
    iSplitL "Hpg1"; [iExact "Hpg1" |].
    iApply "Hks1".
    iSplitL "Hpg0 Hs0"; [(iApply "Hpg0"; iExact "Hs0") | iExact "Hemp"].
  Qed.

End PtBuildIris.

(* ===================================================================== *)
(* §6 Address-arithmetic bridges: walk's computed register values are     *)
(*    the description's addresses.  Each bridge first reduces the         *)
(*    [shift_bits_*] forms (concrete shift amounts) to plain              *)
(*    [shiftl]/[shiftr], then works at [bv_unsigned].                     *)
(* ===================================================================== *)

(* the ext bits pin a classified pointer word below 2^54 *)
Lemma pte_valid_ptr_lt54 (w : mword 64) :
  pte_valid w -> pte_ptr w ->
  bv_unsigned w < 18014398509481984.
Proof.
  intros Hv Hp.
  pose proof (pte_valid_ptr_ext0 w Hv Hp) as Hext.
  apply (f_equal bv_unsigned) in Hext.
  rewrite (subrange64_unsigned_63_54 w) in Hext.
  replace (bv_unsigned (zeros' 10 : mword 10)) with 0 in Hext
    by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range _ w) as Hw.
  unfold bv_modulus in Hw.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64))
    with 18446744073709551616 in Hw.
  rewrite Z.shiftr_div_pow2 in Hext; [| lia].
  change (2 ^ 54) with 18014398509481984 in Hext.
  change (2 ^ 10) with 1024 in Hext.
  assert (Hd : 0 <= bv_unsigned w / 18014398509481984 < 1024)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small _ _ Hd) in Hext.
  pose proof (Z.div_mod (bv_unsigned w) 18014398509481984 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (bv_unsigned w) 18014398509481984 ltac:(lia)) as Hmb.
  rewrite Hdm. rewrite Hext.
  rewrite Z.mul_0_r. rewrite Z.add_0_l.
  exact (proj2 Hmb).
Qed.

(* (ii) THE DESCEND BASE: (w >> 10) << 12 is the next-level page base *)
Lemma walk_descend_base (w : mword 64) :
  pte_valid w -> pte_ptr w ->
  shift_bits_left
    (shift_bits_right w (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
    (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
  = zero_extend' 64 (concat_vec (u_next_base w) (zeros' 12 : mword 12)).
Proof.
  intros Hv Hp.
  pose proof (pte_valid_ptr_lt54 w Hv Hp) as Hlt.
  assert (Hred : shift_bits_left
      (shift_bits_right w (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
      (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
    = shiftl (shiftr w 10) 12).
  { unfold shift_bits_left, shift_bits_right.
    f_equal.
    all: try (vm_compute; reflexivity).
    all: f_equal; vm_compute; reflexivity. }
  rewrite Hred.
  assert (Hunb : bv_unsigned (u_next_base w) = (bv_unsigned w ≫ 10) `mod` 2 ^ 44).
  { unfold u_next_base, PPN_of_PTE.
    change (Z.eqb 64 32) with false. cbv beta iota.
    rewrite !autocast_id. exact (subrange64_unsigned_53_10 w). }
  apply bv_eq.
  rewrite page_base_unsigned. rewrite Hunb.
  unfold shiftl, shiftr, with_word, get_word,
    MachineWord.MachineWord.logical_shift_left,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftl_unsigned. rewrite bv_shiftr_unsigned.
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 12))) with 12
    by (vm_compute; reflexivity).
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 10))) with 10
    by (vm_compute; reflexivity).
  rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 10) with 1024.
  assert (Hq : 0 <= bv_unsigned w / 1024 < 2 ^ 44)
    by (split; [apply Z.div_pos; pose proof (bv_unsigned_in_range _ w); lia
               | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small _ _ Hq).
  replace (Z.shiftl (bv_unsigned w / 1024) 12) with (bv_unsigned w / 1024 * 4096)
    by (rewrite Z.shiftl_mul_pow2; [reflexivity | lia]).
  apply bv_wrap_small.
  unfold bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616.
  lia.
Qed.

(* (iii) THE ALLOC PTE: (pa >> 12) << 10 | 1 is the pointer PTE of pa's
   ppn, and that ppn's page base is pa itself (pa page-aligned, < 2^56) *)
Lemma walk_alloc_pte (pa : mword 64) :
  uint pa `mod` 4096 = 0 ->
  uint pa < 72057594037927936 ->
  or_vec
    (shift_bits_left
       (shift_bits_right pa (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
       (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
    (sign_extend' 64 (mword_of_int 1 : mword 12))
  = pt_ptr_pte (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44).
Proof.
  intros Hal Hlt.
  rewrite uint_unsigned in Hal. rewrite uint_unsigned in Hlt.
  assert (Hred : shift_bits_left
      (shift_bits_right pa (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
      (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0)
    = shiftl (shiftr pa 12) 10).
  { unfold shift_bits_left, shift_bits_right.
    f_equal.
    all: try (vm_compute; reflexivity).
    all: f_equal; vm_compute; reflexivity. }
  rewrite Hred.
  assert (Hppn : bv_unsigned (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44)
                 = bv_unsigned pa / 4096).
  { rewrite autocast_id.
    unfold subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
    rewrite bv_extract_unsigned.
    change (Z.of_N (MachineWord.MachineWord.Z_idx 12)) with 12.
    change (MachineWord.MachineWord.Z_idx (55 - 12 + 1)) with 44%N.
    rewrite Z.shiftr_div_pow2; [| lia].
    change (2 ^ 12) with 4096.
    apply bv_wrap_small.
    unfold bv_modulus.
    change (2 ^ Z.of_N 44) with 17592186044416.
    split.
    - apply Z.div_pos; [exact (proj1 (bv_unsigned_in_range _ pa)) | reflexivity].
    - apply Z.div_lt_upper_bound; [reflexivity |].
      change (4096 * 17592186044416) with 72057594037927936.
      exact Hlt. }
  apply bv_eq.
  rewrite (mk_pte_unsigned _ PTE_PTR ltac:(unfold PTE_PTR; lia)).
  rewrite Hppn.
  unfold or_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.or.
  rewrite bv_or_unsigned.
  replace (bv_unsigned (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)) with 1
    by (vm_compute; reflexivity).
  unfold shiftl, shiftr, with_word, get_word,
    MachineWord.MachineWord.logical_shift_left,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftl_unsigned. rewrite bv_shiftr_unsigned.
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 10))) with 10
    by (vm_compute; reflexivity).
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 12))) with 12
    by (vm_compute; reflexivity).
  rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 12) with 4096.
  assert (Hq : 0 <= bv_unsigned pa / 4096 < 17592186044416)
    by (split; [apply Z.div_pos; pose proof (bv_unsigned_in_range _ pa); lia
               | apply Z.div_lt_upper_bound; lia]).
  replace (Z.shiftl (bv_unsigned pa / 4096) 10) with (bv_unsigned pa / 4096 * 1024)
    by (rewrite Z.shiftl_mul_pow2; [reflexivity | lia]).
  rewrite bv_wrap_small.
  2:{ unfold bv_modulus.
      change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616.
      lia. }
  rewrite <- Z_lor_disjoint_add.
  - reflexivity.
  - change 1024 with (2 ^ 10).
    apply Z_land_shift_low.
    + apply Z.leb_le; reflexivity.
    + change (2 ^ 10) with 1024.
      split; [apply Z.leb_le; reflexivity | reflexivity].
Qed.

(* the ppn's page base is pa itself *)
Lemma walk_alloc_page_base (pa : mword 64) :
  uint pa `mod` 4096 = 0 ->
  uint pa < 72057594037927936 ->
  zero_extend' 64 (concat_vec
    (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44)
    (zeros' 12 : mword 12)) = pa.
Proof.
  intros Hal Hlt.
  rewrite uint_unsigned in Hal. rewrite uint_unsigned in Hlt.
  apply bv_eq.
  rewrite page_base_unsigned.
  assert (Hppn : bv_unsigned (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44)
                 = bv_unsigned pa / 4096).
  { rewrite autocast_id.
    unfold subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
    rewrite bv_extract_unsigned.
    change (Z.of_N (MachineWord.MachineWord.Z_idx 12)) with 12.
    change (MachineWord.MachineWord.Z_idx (55 - 12 + 1)) with 44%N.
    rewrite Z.shiftr_div_pow2; [| lia].
    change (2 ^ 12) with 4096.
    apply bv_wrap_small.
    unfold bv_modulus.
    change (2 ^ Z.of_N 44) with 17592186044416.
    split.
    - apply Z.div_pos; [exact (proj1 (bv_unsigned_in_range _ pa)) | reflexivity].
    - apply Z.div_lt_upper_bound; [reflexivity |].
      change (4096 * 17592186044416) with 72057594037927936.
      exact Hlt. }
  rewrite Hppn.
  apply Z.mod_divide in Hal; [| lia]. destruct Hal as [q Hq].
  rewrite Hq. rewrite Z.div_mul; [| lia]. lia.
Qed.

(* (i) THE SLOT ADDRESS, level 2 (shift 30): srl/andi/slli/add compute
   the description's slot address from the page base and the va *)
Lemma walk_slot_addr2 (b : mword 44) (va : mword 64) :
  uint va < 274877906944 ->
  add_vec
    (shift_bits_left
       (and_vec
          (shift_bits_right va
             (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
          (sign_extend' 64 (mword_of_int 511 : mword 12)))
       (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
    (zero_extend' 64 (concat_vec b (zeros' 12 : mword 12)))
  = u_pte_addr b (vpn_idx 2 (svpn_of va)).
Proof.
  intros Hva. pose proof Hva as Hva'. rewrite uint_unsigned in Hva'.
  assert (Hred : shift_bits_left
      (and_vec
         (shift_bits_right va
            (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
         (sign_extend' 64 (mword_of_int 511 : mword 12)))
      (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)
    = shiftl (and_vec (shiftr va 30) (sign_extend' 64 (mword_of_int 511 : mword 12))) 3).
  { unfold shift_bits_left, shift_bits_right.
    f_equal.
    all: try (vm_compute; reflexivity).
    all: f_equal.
    all: try (vm_compute; reflexivity).
    all: f_equal; vm_compute; reflexivity. }
  rewrite Hred.
  assert (Hidx : bv_unsigned (vpn_idx 2 (svpn_of va))
                 = Z.shiftr (bv_unsigned va) 30 `mod` 512).
  { cbn [vpn_idx].
    rewrite (pt_sub27_26_18 (svpn_of va)).
    rewrite (svpn_of_unsigned_lo va Hva).
    rewrite uint_unsigned.
    rewrite Z.shiftr_shiftr; [| apply Z.leb_le; reflexivity].
    change (12 + 18) with 30. change (2 ^ 9) with 512. reflexivity.
  }
  apply bv_eq.
  replace (bv_unsigned (u_pte_addr b (vpn_idx 2 (svpn_of va))))
    with (bv_unsigned b * 4096 + bv_unsigned (vpn_idx 2 (svpn_of va)) * 8)
    by (symmetry; exact (pte_addr_at_unsigned b (vpn_idx 2 (svpn_of va)))).
  rewrite Hidx.
  unfold add_vec, and_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add, MachineWord.MachineWord.and.
  unfold shiftl, shiftr, with_word,
    MachineWord.MachineWord.logical_shift_left,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_add_unsigned. rewrite bv_shiftl_unsigned.
  rewrite bv_and_unsigned. rewrite bv_shiftr_unsigned.
  match goal with |- context [Z.shiftr (bv_unsigned va) (bv_unsigned ?am)] =>
    replace (bv_unsigned am) with 30 by (vm_compute; reflexivity) end.
  match goal with |- context [Z.land _ (bv_unsigned ?mm)] =>
    replace (bv_unsigned mm) with 511 by (vm_compute; reflexivity) end.
  match goal with |- context [Z.shiftl _ (bv_unsigned ?sm)] =>
    replace (bv_unsigned sm) with 3 by (vm_compute; reflexivity) end.
  match goal with |- context [_ + bv_unsigned ?pb] =>
    replace (bv_unsigned pb) with (bv_unsigned b * 4096)
      by (symmetry; exact (page_base_unsigned b)) end.
  change 511 with (Z.ones 9).
  rewrite Z.land_ones; [| apply Z.leb_le; reflexivity].
  change (2 ^ 9) with 512.
  replace (Z.shiftl (Z.shiftr (bv_unsigned va) 30 `mod` 512) 3)
    with (Z.shiftr (bv_unsigned va) 30 `mod` 512 * 8)
    by (rewrite Z.shiftl_mul_pow2; [reflexivity | apply Z.leb_le; reflexivity]).
  pose proof (Z.mod_pos_bound (Z.shiftr (bv_unsigned va) 30) 512
                ltac:(reflexivity)) as Hmb.
  pose proof (bv_unsigned_in_range _ b) as Hbr.
  unfold bv_modulus in Hbr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 44)) with 17592186044416 in Hbr.
  match goal with |- context [bv_wrap ?n (?x * 8)] =>
    replace (bv_wrap n (x * 8)) with (x * 8)
      by (symmetry; apply bv_wrap_small;
          unfold bv_modulus;
          change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64))
            with 18446744073709551616;
          lia) end.
  rewrite bv_wrap_small.
  2:{ unfold bv_modulus.
      change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64))
        with 18446744073709551616.
      lia. }
  apply Z.add_comm.
Qed.

(* (i) THE SLOT ADDRESS, level 1 (shift 21): srl/andi/slli/add compute
   the description's slot address from the page base and the va *)
Lemma walk_slot_addr1 (b : mword 44) (va : mword 64) :
  uint va < 274877906944 ->
  add_vec
    (shift_bits_left
       (and_vec
          (shift_bits_right va
             (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
          (sign_extend' 64 (mword_of_int 511 : mword 12)))
       (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
    (zero_extend' 64 (concat_vec b (zeros' 12 : mword 12)))
  = u_pte_addr b (vpn_idx 1 (svpn_of va)).
Proof.
  intros Hva. pose proof Hva as Hva'. rewrite uint_unsigned in Hva'.
  assert (Hred : shift_bits_left
      (and_vec
         (shift_bits_right va
            (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
         (sign_extend' 64 (mword_of_int 511 : mword 12)))
      (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)
    = shiftl (and_vec (shiftr va 21) (sign_extend' 64 (mword_of_int 511 : mword 12))) 3).
  { unfold shift_bits_left, shift_bits_right.
    f_equal.
    all: try (vm_compute; reflexivity).
    all: f_equal.
    all: try (vm_compute; reflexivity).
    all: f_equal; vm_compute; reflexivity. }
  rewrite Hred.
  assert (Hidx : bv_unsigned (vpn_idx 1 (svpn_of va))
                 = Z.shiftr (bv_unsigned va) 21 `mod` 512).
  { cbn [vpn_idx].
    rewrite (pt_sub27_17_9 (svpn_of va)).
    rewrite (svpn_of_unsigned_lo va Hva).
    rewrite uint_unsigned.
    rewrite Z.shiftr_shiftr; [| apply Z.leb_le; reflexivity].
    change (12 + 9) with 21. change (2 ^ 9) with 512. reflexivity.
  }
  apply bv_eq.
  replace (bv_unsigned (u_pte_addr b (vpn_idx 1 (svpn_of va))))
    with (bv_unsigned b * 4096 + bv_unsigned (vpn_idx 1 (svpn_of va)) * 8)
    by (symmetry; exact (pte_addr_at_unsigned b (vpn_idx 1 (svpn_of va)))).
  rewrite Hidx.
  unfold add_vec, and_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add, MachineWord.MachineWord.and.
  unfold shiftl, shiftr, with_word,
    MachineWord.MachineWord.logical_shift_left,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_add_unsigned. rewrite bv_shiftl_unsigned.
  rewrite bv_and_unsigned. rewrite bv_shiftr_unsigned.
  match goal with |- context [Z.shiftr (bv_unsigned va) (bv_unsigned ?am)] =>
    replace (bv_unsigned am) with 21 by (vm_compute; reflexivity) end.
  match goal with |- context [Z.land _ (bv_unsigned ?mm)] =>
    replace (bv_unsigned mm) with 511 by (vm_compute; reflexivity) end.
  match goal with |- context [Z.shiftl _ (bv_unsigned ?sm)] =>
    replace (bv_unsigned sm) with 3 by (vm_compute; reflexivity) end.
  match goal with |- context [_ + bv_unsigned ?pb] =>
    replace (bv_unsigned pb) with (bv_unsigned b * 4096)
      by (symmetry; exact (page_base_unsigned b)) end.
  change 511 with (Z.ones 9).
  rewrite Z.land_ones; [| apply Z.leb_le; reflexivity].
  change (2 ^ 9) with 512.
  replace (Z.shiftl (Z.shiftr (bv_unsigned va) 21 `mod` 512) 3)
    with (Z.shiftr (bv_unsigned va) 21 `mod` 512 * 8)
    by (rewrite Z.shiftl_mul_pow2; [reflexivity | apply Z.leb_le; reflexivity]).
  pose proof (Z.mod_pos_bound (Z.shiftr (bv_unsigned va) 21) 512
                ltac:(reflexivity)) as Hmb.
  pose proof (bv_unsigned_in_range _ b) as Hbr.
  unfold bv_modulus in Hbr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 44)) with 17592186044416 in Hbr.
  match goal with |- context [bv_wrap ?n (?x * 8)] =>
    replace (bv_wrap n (x * 8)) with (x * 8)
      by (symmetry; apply bv_wrap_small;
          unfold bv_modulus;
          change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64))
            with 18446744073709551616;
          lia) end.
  rewrite bv_wrap_small.
  2:{ unfold bv_modulus.
      change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64))
        with 18446744073709551616.
      lia. }
  apply Z.add_comm.
Qed.

(* (i) THE SLOT ADDRESS, level 0 (shift 12): srl/andi/slli/add compute
   the description's slot address from the page base and the va *)
Lemma walk_slot_addr0 (b : mword 44) (va : mword 64) :
  uint va < 274877906944 ->
  add_vec
    (shift_bits_left
       (and_vec
          (shift_bits_right va
             (subrange_vec_dec (mword_of_int 12 : mword 64) (Z.sub log2_xlen 1) 0))
          (sign_extend' 64 (mword_of_int 511 : mword 12)))
       (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
    (zero_extend' 64 (concat_vec b (zeros' 12 : mword 12)))
  = u_pte_addr b (vpn_idx 0 (svpn_of va)).
Proof.
  intros Hva. pose proof Hva as Hva'. rewrite uint_unsigned in Hva'.
  assert (Hred : shift_bits_left
      (and_vec
         (shift_bits_right va
            (subrange_vec_dec (mword_of_int 12 : mword 64) (Z.sub log2_xlen 1) 0))
         (sign_extend' 64 (mword_of_int 511 : mword 12)))
      (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)
    = shiftl (and_vec (shiftr va 12) (sign_extend' 64 (mword_of_int 511 : mword 12))) 3).
  { unfold shift_bits_left, shift_bits_right.
    f_equal.
    all: try (vm_compute; reflexivity).
    all: f_equal.
    all: try (vm_compute; reflexivity).
    all: f_equal; vm_compute; reflexivity. }
  rewrite Hred.
  assert (Hidx : bv_unsigned (vpn_idx 0 (svpn_of va))
                 = Z.shiftr (bv_unsigned va) 12 `mod` 512).
  { cbn [vpn_idx].
    rewrite (pt_sub27_8_0 (svpn_of va)).
    rewrite (svpn_of_unsigned_lo va Hva).
    rewrite uint_unsigned.
    change (2 ^ 9) with 512. reflexivity.
  }
  apply bv_eq.
  replace (bv_unsigned (u_pte_addr b (vpn_idx 0 (svpn_of va))))
    with (bv_unsigned b * 4096 + bv_unsigned (vpn_idx 0 (svpn_of va)) * 8)
    by (symmetry; exact (pte_addr_at_unsigned b (vpn_idx 0 (svpn_of va)))).
  rewrite Hidx.
  unfold add_vec, and_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add, MachineWord.MachineWord.and.
  unfold shiftl, shiftr, with_word,
    MachineWord.MachineWord.logical_shift_left,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_add_unsigned. rewrite bv_shiftl_unsigned.
  rewrite bv_and_unsigned. rewrite bv_shiftr_unsigned.
  match goal with |- context [Z.shiftr (bv_unsigned va) (bv_unsigned ?am)] =>
    replace (bv_unsigned am) with 12 by (vm_compute; reflexivity) end.
  match goal with |- context [Z.land _ (bv_unsigned ?mm)] =>
    replace (bv_unsigned mm) with 511 by (vm_compute; reflexivity) end.
  match goal with |- context [Z.shiftl _ (bv_unsigned ?sm)] =>
    replace (bv_unsigned sm) with 3 by (vm_compute; reflexivity) end.
  match goal with |- context [_ + bv_unsigned ?pb] =>
    replace (bv_unsigned pb) with (bv_unsigned b * 4096)
      by (symmetry; exact (page_base_unsigned b)) end.
  change 511 with (Z.ones 9).
  rewrite Z.land_ones; [| apply Z.leb_le; reflexivity].
  change (2 ^ 9) with 512.
  replace (Z.shiftl (Z.shiftr (bv_unsigned va) 12 `mod` 512) 3)
    with (Z.shiftr (bv_unsigned va) 12 `mod` 512 * 8)
    by (rewrite Z.shiftl_mul_pow2; [reflexivity | apply Z.leb_le; reflexivity]).
  pose proof (Z.mod_pos_bound (Z.shiftr (bv_unsigned va) 12) 512
                ltac:(reflexivity)) as Hmb.
  pose proof (bv_unsigned_in_range _ b) as Hbr.
  unfold bv_modulus in Hbr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 44)) with 17592186044416 in Hbr.
  match goal with |- context [bv_wrap ?n (?x * 8)] =>
    replace (bv_wrap n (x * 8)) with (x * 8)
      by (symmetry; apply bv_wrap_small;
          unfold bv_modulus;
          change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64))
            with 18446744073709551616;
          lia) end.
  rewrite bv_wrap_small.
  2:{ unfold bv_modulus.
      change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64))
        with 18446744073709551616.
      lia. }
  apply Z.add_comm.
Qed.

(* the C walk's V-bit test: [andi a5, w, 1; beqz a5] branches exactly on
   bit 0 of the slot word *)
Lemma walk_vbit_eq (w : mword 64) :
  eq_vec (and_vec w (sign_extend' 64 (mword_of_int 1 : mword 12))) zero_reg
  = negb (Z.testbit (bv_unsigned w) 0).
Proof.
  assert (Hand : bv_unsigned (and_vec w (sign_extend' 64 (mword_of_int 1 : mword 12)))
                 = Z.b2z (Z.odd (bv_unsigned w))).
  { unfold and_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      to_word, get_word, SailStdpp.Values.with_word.
    unfold MachineWord.MachineWord.and.
    rewrite bv_and_unsigned.
    match goal with |- context [Z.land _ (bv_unsigned ?mm)] =>
      replace (bv_unsigned mm) with 1 by (vm_compute; reflexivity) end.
    change 1 with (Z.ones 1) at 1.
    rewrite Z.land_ones; [| apply Z.leb_le; reflexivity].
    change (2 ^ 1) with 2.
    apply Zmod_odd. }
  rewrite Z.bit0_odd.
  destruct (Z.odd (bv_unsigned w)) eqn:E; cbn [Z.b2z] in Hand.
  - cbn [negb]. apply eq_vec_false_iff.
    intro Hc. apply (f_equal bv_unsigned) in Hc.
    rewrite Hand in Hc.
    replace (bv_unsigned (zero_reg : mword 64)) with 0 in Hc
      by (vm_compute; reflexivity).
    discriminate Hc.
  - cbn [negb]. apply eq_vec_true_iff.
    apply bv_eq. rewrite Hand.
    vm_compute. reflexivity.
Qed.
