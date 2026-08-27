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
Require Import RiscvModelBytes RiscvPtsto RiscvExec RiscvTryStep RiscvExtras.
Require Import PtAdBits Pt4kWalk CommonWalk PtTree WpDecodeBridge.
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

(* The leaf word a vpn's path CURRENTLY reaches, as a FUNCTION of the
   tree (the tree is concrete data, so the represented map is recoverable
   from it): [None] when the path is cut short by a missing l1/l0 node,
   otherwise the word sitting in the l0 slot.  This is what lets a
   modulo-A/D mapping spec be turned back into an EXACT [pt_rep0] map
   ([UptTree.upt_spec_rep0]). *)
Definition pt_leaf_word (t : ptree) (vpn : mword 27) : option (mword 64) :=
  match pt_kids t (vpn_idx 2 vpn) with
  | None => None
  | Some c1 =>
      match pt_kids c1 (vpn_idx 1 vpn) with
      | None => None
      | Some c0 => Some (pt_ents c0 (vpn_idx 0 vpn))
      end
  end.

Lemma ptree_maps_leaf_word (t : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 -> pt_leaf_word t vpn = Some p0.
Proof.
  intros (c1 & c0 & Hk2 & Hk1 & _ & _ & He0 & _).
  unfold pt_leaf_word. rewrite Hk2 Hk1 He0. reflexivity.
Qed.

(* ===================================================================== *)
(* FUEL-GENERIC descent relations (the walk-loop pure layer).  A node [t]  *)
(* sitting at level [lvl] on [vpn]'s path either MAPS down to a valid leaf, *)
(* reaches level 0 (any leaf word), or BLOCKS at a zero (V=0) word.  The    *)
(* fixed-3-level [ptree_maps]/[ptree_level0]/[ptree_blocks0] are the [lvl=2] *)
(* instances (bridges below).                                              *)
(* ===================================================================== *)
Fixpoint ptree_maps_lvl (lvl : nat) (t : ptree) (vpn : mword 27) (p0 : mword 64) : Prop :=
  match lvl with
  | O => pt_ents t (vpn_idx 0 vpn) = p0
         /\ pte_valid p0 /\ pte_leaf p0 /\ pte_no_napot p0 /\ pte_pbmt0 p0
  | S l => exists c,
      pt_kids t (vpn_idx (S l) vpn) = Some c
      /\ pte_valid (pt_ents t (vpn_idx (S l) vpn))
      /\ pte_ptr (pt_ents t (vpn_idx (S l) vpn))
      /\ u_next_base (pt_ents t (vpn_idx (S l) vpn)) = pt_base c
      /\ ptree_maps_lvl l c vpn p0
  end.

Fixpoint ptree_level0_lvl (lvl : nat) (t : ptree) (vpn : mword 27) (w0 : mword 64) : Prop :=
  match lvl with
  | O => pt_ents t (vpn_idx 0 vpn) = w0
  | S l => exists c,
      pt_kids t (vpn_idx (S l) vpn) = Some c
      /\ pte_valid (pt_ents t (vpn_idx (S l) vpn))
      /\ pte_ptr (pt_ents t (vpn_idx (S l) vpn))
      /\ u_next_base (pt_ents t (vpn_idx (S l) vpn)) = pt_base c
      /\ ptree_level0_lvl l c vpn w0
  end.

Fixpoint ptree_blocks0_lvl (lvl : nat) (t : ptree) (vpn : mword 27) : Prop :=
  match lvl with
  | O => pt_ents t (vpn_idx 0 vpn) = mword_of_int 0
  | S l => (pt_kids t (vpn_idx (S l) vpn) = None
              /\ pt_ents t (vpn_idx (S l) vpn) = mword_of_int 0)
           \/ (exists c,
                 pt_kids t (vpn_idx (S l) vpn) = Some c
                 /\ pte_valid (pt_ents t (vpn_idx (S l) vpn))
                 /\ pte_ptr (pt_ents t (vpn_idx (S l) vpn))
                 /\ u_next_base (pt_ents t (vpn_idx (S l) vpn)) = pt_base c
                 /\ ptree_blocks0_lvl l c vpn)
  end.

(* every mapped walk reaches level 0 *)
Lemma ptree_maps_lvl_level0_lvl (lvl : nat) (t : ptree) (vpn : mword 27) (p0 : mword 64) :
  ptree_maps_lvl lvl t vpn p0 -> ptree_level0_lvl lvl t vpn p0.
Proof.
  revert t. induction lvl as [|l IH]; intros t; cbn.
  - intros (He & _). exact He.
  - intros (c & Hk & Hv & Hp & Hb & Hrec). exists c.
    repeat split; try assumption. apply IH; exact Hrec.
Qed.

(* ---- level-2 bridges to the fixed-depth relations -------------------- *)
Lemma ptree_maps_maps_lvl2 (t : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 -> ptree_maps_lvl 2 t vpn p0.
Proof.
  intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb2 & Hb1 &
          Hv2 & Hp2 & Hv1 & Hp1 & Hv0 & Hl0 & Hn0 & Hpb0).
  cbn. exists c1. rewrite He2. repeat split; try assumption.
  cbn. exists c0. rewrite He1. rewrite He0. repeat split; assumption.
Qed.

Lemma ptree_level0_lvl2_level0 (t : ptree) (vpn : mword 27) (w0 : mword 64) :
  ptree_level0_lvl 2 t vpn w0 -> exists p2 p1, ptree_level0 t vpn p2 p1 w0.
Proof.
  cbn. intros (c1 & Hk2 & Hv2 & Hp2 & Hb2 & c0 & Hk1 & Hv1 & Hp1 & Hb1 & He0).
  exists (pt_ents t (vpn_idx 2 vpn)), (pt_ents c1 (vpn_idx 1 vpn)).
  exists c1, c0. repeat split; (assumption || reflexivity).
Qed.

Lemma ptree_blocks0_blocks0_lvl2 (t : ptree) (vpn : mword 27) :
  ptree_blocks0 t vpn -> ptree_blocks0_lvl 2 t vpn.
Proof.
  intros [ [Hk He] | [ (c1 & Hk2 & Hk1 & Hv2 & Hp2 & Hb2 & He1) |
                       (c1 & c0 & Hk2 & Hk1 & Hv2 & Hp2 & Hv1 & Hp1 & Hb2 & Hb1 & He0) ] ].
  - left. split; assumption.
  - right. exists c1. repeat split; try assumption.
    left. split; assumption.
  - right. exists c1. repeat split; try assumption.
    right. exists c0. repeat split; assumption.
Qed.

(* ---- existential-descent support (the alloc arm / kalloc's page) ----- *)

(* one-step descend unfolds (named, for the loop body's V=1 arm) *)
Lemma ptree_maps_lvl_S (l : nat) (t : ptree) (vpn : mword 27) (p0 : mword 64) :
  ptree_maps_lvl (S l) t vpn p0 <->
  exists c, pt_kids t (vpn_idx (S l) vpn) = Some c
         /\ pte_valid (pt_ents t (vpn_idx (S l) vpn))
         /\ pte_ptr (pt_ents t (vpn_idx (S l) vpn))
         /\ u_next_base (pt_ents t (vpn_idx (S l) vpn)) = pt_base c
         /\ ptree_maps_lvl l c vpn p0.
Proof. reflexivity. Qed.
Lemma ptree_blocks0_lvl_S (l : nat) (t : ptree) (vpn : mword 27) :
  ptree_blocks0_lvl (S l) t vpn <->
  (pt_kids t (vpn_idx (S l) vpn) = None /\ pt_ents t (vpn_idx (S l) vpn) = mword_of_int 0)
  \/ (exists c, pt_kids t (vpn_idx (S l) vpn) = Some c
         /\ pte_valid (pt_ents t (vpn_idx (S l) vpn))
         /\ pte_ptr (pt_ents t (vpn_idx (S l) vpn))
         /\ u_next_base (pt_ents t (vpn_idx (S l) vpn)) = pt_base c
         /\ ptree_blocks0_lvl l c vpn).
Proof. reflexivity. Qed.

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

(* a freshly kalloc'd, zeroed page blocks EVERY vpn at EVERY level: this is
   the verdict the loop carries for the subtree it just grafted, with the
   page [b] the existential kalloc chose. *)
Lemma ptree_blocks0_lvl_empty (lvl : nat) (b : mword 44) (vpn : mword 27) :
  ptree_blocks0_lvl lvl (pt_empty_node b) vpn.
Proof. destruct lvl; cbn; [ reflexivity | left; split; reflexivity ]. Qed.

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

(* ---- §3b THE DELETION: uvmunmap's [*pte = 0] ------------------------- *)
(* The mirror image of the insertion.  Writing the LITERAL ZERO through a
   level0 path re-blocks that vpn IN THE xv6 SHAPE -- [ptree_blocks0]'s
   third disjunct, whose every conjunct is a [ptree_level0] conjunct plus
   the freshly-written zero slot.  So no leaf classification is needed
   (there is nothing to classify), and the OLD word [w0] is irrelevant:
   uvmunmap clears a slot whether it held a leaf or not. *)

Lemma ptree_set_leaf0_blocks_self (t : ptree) (vpn : mword 27)
    (p2 p1 w0 : mword 64) :
  ptree_level0 t vpn p2 p1 w0 ->
  ptree_blocks0 (ptree_set_leaf t vpn (mword_of_int 0)) vpn.
Proof.
  intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 &
          Hv2 & Hn2 & Hv1 & Hn1).
  unfold ptree_set_leaf. rewrite Hk2. rewrite Hk1.
  right. right.
  exists (pt_upd_kid c1 (vpn_idx 1 vpn)
            (Some (pt_upd_ent c0 (vpn_idx 0 vpn) (mword_of_int 0)))),
         (pt_upd_ent c0 (vpn_idx 0 vpn) (mword_of_int 0)).
  rewrite !pt_upd_kid_same !pt_upd_kid_ents !pt_upd_kid_base
          !pt_upd_ent_base !pt_upd_ent_same.
  rewrite He2 He1.
  repeat split; try reflexivity; assumption.
Qed.

Lemma pt_rep0_delete (t : ptree) (m : gmap (mword 27) (mword 64))
    (vpn : mword 27) (p2 p1 w0 : mword 64) :
  pt_rep0 t m ->
  ptree_level0 t vpn p2 p1 w0 ->
  pt_rep0 (ptree_set_leaf t vpn (mword_of_int 0)) (delete vpn m).
Proof.
  intros (Hmap & Hblk) Hl0. split.
  - intros v wv Hlk.
    destruct (decide (v = vpn)) as [-> | Hne].
    { rewrite lookup_delete in Hlk. discriminate. }
    rewrite lookup_delete_ne in Hlk; [| exact (fun He => Hne (eq_sym He))].
    destruct (Hmap v wv Hlk) as (q2 & q1 & Hq).
    exists q2, q1.
    exact (ptree_set_leaf_maps_other t vpn v q2 q1 wv (mword_of_int 0) Hne Hq).
  - intros v Hlk.
    destruct (decide (v = vpn)) as [-> | Hne].
    { exact (ptree_set_leaf0_blocks_self t vpn p2 p1 w0 Hl0). }
    rewrite lookup_delete_ne in Hlk; [| exact (fun He => Hne (eq_sym He))].
    exact (ptree_set_leaf0_blocks_other t vpn v p2 p1 w0 (mword_of_int 0)
             Hne Hl0 (Hblk v Hlk)).
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
  (* disjunct 4 (NEW upstream): a PBMT encoding the platform does not know,
     gated on Svpbmt.  [dstateM] is concrete, so the probe just computes. *)
  match type of Hv with
  | exec (or_boolM ?ac _) _ = _ =>
      assert (HAC4 : exists d4 : bool, exec ac dstateM = Some (d4, dstateM))
  end.
  { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ dstateM)).
    match goal with |- exists _, (if ?c then _ else _) = _ => destruct c end;
      [| eexists; reflexivity].
    eexists. vm_compute. reflexivity. }
  destruct HAC4 as (d4 & HAC4).
  rewrite (exec_or_boolM_Some _ _ _ _ _ HAC4) in Hv.
  destruct d4; [discriminate Hv |].
  (* disjunct 5 (NEW upstream): the remaining checks moved UNDER a
     [pte_reserved_bits_must_be_zero] gate, which this privileged-ISA version
     sets; the nonleaf payload is its first arm. *)
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ dstateM)) in Hv.
  match type of Hv with (if ?c then _ else _) = _ => destruct c eqn:Eprb end;
    [| vm_compute in Eprb; discriminate Eprb ].
  (* the payload: nonleaf & (A|D|U|ext<>0) *)
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

(* LEVEL-GENERIC graft: attach a zeroed page [b] under slot [i] of node [t]
   and write the pointer PTE into slot [i].  [pt_graft2 t vpn b] is
   [pt_graft t (vpn_idx 2 vpn) b] and [pt_graft1_kid c1 vpn b] is
   [pt_graft c1 (vpn_idx 1 vpn) b] (both hold definitionally). *)
Definition pt_graft (t : ptree) (i : mword 9) (b : mword 44) : ptree :=
  pt_upd_kid (pt_upd_ent t i (pt_ptr_pte b)) i (Some (pt_empty_node b)).

Lemma pt_graft_base (t : ptree) (i : mword 9) (b : mword 44) :
  pt_base (pt_graft t i b) = pt_base t.
Proof. reflexivity. Qed.
Lemma pt_graft_kid (t : ptree) (i : mword 9) (b : mword 44) :
  pt_kids (pt_graft t i b) i = Some (pt_empty_node b).
Proof. unfold pt_graft. rewrite pt_upd_kid_same. reflexivity. Qed.
Lemma pt_graft_ent (t : ptree) (i : mword 9) (b : mword 44) :
  pt_ents (pt_graft t i b) i = pt_ptr_pte b.
Proof. unfold pt_graft. rewrite pt_upd_kid_ents. cbn. case_decide; [reflexivity | contradiction]. Qed.
Lemma pt_graft_kids_other (t : ptree) (i j : mword 9) (b : mword 44) :
  j <> i -> pt_kids (pt_graft t i b) j = pt_kids t j.
Proof. intros Hne. unfold pt_graft. rewrite pt_upd_kid_other; [ reflexivity | exact Hne ]. Qed.
Lemma pt_graft_ents_other (t : ptree) (i j : mword 9) (b : mword 44) :
  j <> i -> pt_ents (pt_graft t i b) j = pt_ents t j.
Proof. intros Hne. unfold pt_graft. rewrite pt_upd_kid_ents. cbn. case_decide; [ contradiction | reflexivity ]. Qed.

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

(* ---- level-indexed same-representation, for the GENERIC walk loop ----- *)
(* [ptree_same_rep0] is hard-wired to the 3-level walk, so the two graft
   preservations above are depth-specific.  The generic loop instead works
   with a subtree at an abstract level [lvl] and threads a level-indexed
   relation.  To bridge back to the whole-tree relation (which exposes the
   intermediate PTEs [p2 p1] as outputs) the fuel-generic maps predicate
   must carry the whole path of PTEs, indexed by level via [P : nat -> _];
   [ptree_maps_path_lvl 2 t v P p0] is exactly [ptree_maps t v (P 2) (P 1) p0].
   The loop needs three facts, all uniform in [lvl]:
     - grafting a fresh empty page at a stopped slot preserves it
       ([ptree_same_rep0_lvl_graft]) -- the alloc arm's local step;
     - replacing a child subtree by an equivalent one preserves it one
       level up ([ptree_same_rep0_lvl_upd_kid]) -- the zipper's restore;
     - at level 2 it coincides with the whole-tree [ptree_same_rep0]
       ([ptree_same_rep0_lvl_2]) -- the final bridge. *)
Fixpoint ptree_maps_path_lvl (lvl : nat) (t : ptree) (vpn : mword 27)
    (P : nat -> mword 64) (p0 : mword 64) : Prop :=
  match lvl with
  | O => pt_ents t (vpn_idx 0 vpn) = p0
         /\ pte_valid p0 /\ pte_leaf p0 /\ pte_no_napot p0 /\ pte_pbmt0 p0
  | S l => exists c,
      pt_kids t (vpn_idx (S l) vpn) = Some c
      /\ pt_ents t (vpn_idx (S l) vpn) = P (S l)
      /\ pte_valid (P (S l)) /\ pte_ptr (P (S l))
      /\ u_next_base (P (S l)) = pt_base c
      /\ ptree_maps_path_lvl l c vpn P p0
  end.

Definition ptree_same_rep0_lvl (lvl : nat) (t t' : ptree) : Prop :=
  pt_base t' = pt_base t /\
  (forall v P p0, ptree_maps_path_lvl lvl t v P p0 <-> ptree_maps_path_lvl lvl t' v P p0) /\
  (forall v, ptree_blocks0_lvl lvl t v <-> ptree_blocks0_lvl lvl t' v).

Lemma ptree_same_rep0_lvl_refl (lvl : nat) (t : ptree) :
  ptree_same_rep0_lvl lvl t t.
Proof. split; [reflexivity | split; [intros; tauto | intros; tauto]]. Qed.

Lemma ptree_same_rep0_lvl_trans (lvl : nat) (t t' t'' : ptree) :
  ptree_same_rep0_lvl lvl t t' -> ptree_same_rep0_lvl lvl t' t'' ->
  ptree_same_rep0_lvl lvl t t''.
Proof.
  intros (Hb & Hm & Hbl) (Hb' & Hm' & Hbl').
  split; [ rewrite Hb'; exact Hb | split ].
  - intros v P p0. rewrite (Hm v P p0). exact (Hm' v P p0).
  - intros v. rewrite (Hbl v). exact (Hbl' v).
Qed.

(* a freshly kalloc'd, zeroed page NEVER maps: every ent is the zero word *)
Lemma ptree_maps_path_lvl_empty_False (lvl : nat) (b : mword 44)
    (vpn : mword 27) (P : nat -> mword 64) (p0 : mword 64) :
  ptree_maps_path_lvl lvl (pt_empty_node b) vpn P p0 -> False.
Proof.
  destruct lvl; cbn.
  - intros (He & Hv & _). rewrite <- He in Hv.
    exact (pte_valid_invalid_excl _ Hv pte_invalid_zero).
  - intros (c & Hk & _). discriminate.
Qed.

(* the alloc arm's local step: grafting a fresh empty page at a stopped
   slot (kids None, ent zero) leaves the represented map unchanged at
   [S l] (the slot went from a dead end to a pointer into a page that maps
   nothing).  Holds only above level 0 -- the walk never grafts at a leaf. *)
Lemma ptree_same_rep0_lvl_graft (l : nat) (t : ptree) (i : mword 9) (b : mword 44) :
  pt_kids t i = None ->
  pt_ents t i = mword_of_int 0 ->
  ptree_same_rep0_lvl (S l) t (pt_graft t i b).
Proof.
  intros Hk He. split; [ apply pt_graft_base | split ].
  - (* maps: both sides refutable at slot i, transported elsewhere *)
    intros v P p0. destruct (decide (vpn_idx (S l) v = i)) as [Ei | Ei].
    + split.
      * intros (c & H1 & _). rewrite Ei in H1. congruence.
      * intros (c & H1 & _ & _ & _ & _ & H6). rewrite Ei pt_graft_kid in H1.
        injection H1 as H1. subst c.
        destruct (ptree_maps_path_lvl_empty_False l b v P p0 H6).
    + pose proof (pt_graft_kids_other t i (vpn_idx (S l) v) b Ei) as Hko.
      pose proof (pt_graft_ents_other t i (vpn_idx (S l) v) b Ei) as Heo.
      split.
      * intros (c & H1 & H2 & H3 & H4 & H5 & H6). exists c.
        rewrite Hko Heo. repeat split; assumption.
      * intros (c & H1 & H2 & H3 & H4 & H5 & H6). exists c.
        rewrite Hko in H1. rewrite Heo in H2.
        repeat split; assumption.
  - (* blocks0: both sides hold at slot i (stop vs descend-into-empty) *)
    intros v. destruct (decide (vpn_idx (S l) v = i)) as [Ei | Ei].
    + split; intros _.
      * right. exists (pt_empty_node b).
        rewrite !Ei !pt_graft_kid !pt_graft_ent !pt_ptr_pte_base !pt_empty_node_base.
        repeat split;
          first [ reflexivity | exact (pt_ptr_pte_valid b)
                | exact (pt_ptr_pte_ptr b) | apply ptree_blocks0_lvl_empty ].
      * left. rewrite Ei. split; [ exact Hk | exact He ].
    + pose proof (pt_graft_kids_other t i (vpn_idx (S l) v) b Ei) as Hko.
      pose proof (pt_graft_ents_other t i (vpn_idx (S l) v) b Ei) as Heo.
      split.
      * intros [ (Hn & Hz) | (c & H1 & H2 & H3 & H4 & H5) ].
        -- left. rewrite Hko Heo. split; [ exact Hn | exact Hz ].
        -- right. exists c. rewrite Hko !Heo. repeat split; assumption.
      * intros [ (Hn & Hz) | (c & H1 & H2 & H3 & H4 & H5) ].
        -- left. rewrite Hko in Hn. rewrite Heo in Hz. split; [ exact Hn | exact Hz ].
        -- right. exists c. rewrite Hko in H1. rewrite !Heo in H2 H3 H4.
           repeat split; assumption.
Qed.

(* the zipper's restore step: replacing a child subtree by a level-[l]
   equivalent one preserves the level-[S l] representation of the parent.
   Iterated up the descent path, this lifts a local [ptree_same_rep0_lvl]
   witness all the way to the root. *)
Lemma ptree_same_rep0_lvl_upd_kid (l : nat) (t : ptree) (i : mword 9) (c c' : ptree) :
  pt_kids t i = Some c ->
  ptree_same_rep0_lvl l c c' ->
  ptree_same_rep0_lvl (S l) t (pt_upd_kid t i (Some c')).
Proof.
  intros Hk (Hbase & Hmaps & Hblk). split; [ apply pt_upd_kid_base | split ].
  - intros v P p0. destruct (decide (vpn_idx (S l) v = i)) as [Ei | Ei].
    + split.
      * intros (d & H1 & H2 & H3 & H4 & H5 & H6).
        rewrite Ei in H1. assert (d = c) as -> by congruence.
        exists c'. rewrite !Ei pt_upd_kid_same pt_upd_kid_ents.
        rewrite Ei in H2.
        repeat split; try reflexivity; try assumption;
          [ rewrite Hbase; exact H5 | apply (proj1 (Hmaps v P p0)); exact H6 ].
      * intros (d & H1 & H2 & H3 & H4 & H5 & H6).
        rewrite Ei pt_upd_kid_same in H1. injection H1 as H1. subst d.
        rewrite Ei pt_upd_kid_ents in H2.
        exists c. rewrite !Ei.
        repeat split; try reflexivity; try assumption;
          [ rewrite <- Hbase; exact H5 | apply (proj2 (Hmaps v P p0)); exact H6 ].
    + pose proof (pt_upd_kid_other t i (Some c') (vpn_idx (S l) v) Ei) as Hko.
      pose proof (pt_upd_kid_ents t i (Some c') (vpn_idx (S l) v)) as Heo.
      split.
      * intros (d & H1 & H2 & H3 & H4 & H5 & H6). exists d.
        rewrite Hko Heo. repeat split; assumption.
      * intros (d & H1 & H2 & H3 & H4 & H5 & H6). exists d.
        rewrite Hko in H1. rewrite Heo in H2.
        repeat split; assumption.
  - intros v. destruct (decide (vpn_idx (S l) v = i)) as [Ei | Ei].
    + split.
      * intros [ (Hn & _) | (d & H1 & H2 & H3 & H4 & H5) ].
        -- rewrite Ei in Hn. congruence.
        -- rewrite Ei in H1. assert (d = c) as -> by congruence.
           right. exists c'. rewrite !Ei pt_upd_kid_same !pt_upd_kid_ents.
           rewrite !Ei in H2 H3 H4.
           repeat split; try reflexivity; try assumption;
             [ rewrite Hbase; exact H4 | apply (proj1 (Hblk v)); exact H5 ].
      * intros [ (Hn & _) | (d & H1 & H2 & H3 & H4 & H5) ].
        -- rewrite Ei pt_upd_kid_same in Hn. discriminate.
        -- rewrite Ei pt_upd_kid_same in H1. injection H1 as H1. subst d.
           rewrite Ei !pt_upd_kid_ents in H2 H3 H4.
           right. exists c. rewrite !Ei.
           repeat split; try reflexivity; try assumption;
             [ rewrite <- Hbase; exact H4 | apply (proj2 (Hblk v)); exact H5 ].
    + pose proof (pt_upd_kid_other t i (Some c') (vpn_idx (S l) v) Ei) as Hko.
      pose proof (pt_upd_kid_ents t i (Some c') (vpn_idx (S l) v)) as Heo.
      split.
      * intros [ (Hn & Hz) | (d & H1 & H2 & H3 & H4 & H5) ].
        -- left. rewrite Hko Heo. split; [ exact Hn | exact Hz ].
        -- right. exists d. rewrite Hko !Heo. repeat split; assumption.
      * intros [ (Hn & Hz) | (d & H1 & H2 & H3 & H4 & H5) ].
        -- left. rewrite Hko in Hn. rewrite Heo in Hz. split; [ exact Hn | exact Hz ].
        -- right. exists d. rewrite Hko in H1. rewrite !Heo in H2 H3 H4.
           repeat split; assumption.
Qed.

(* [ptree_maps_path_lvl 2] is exactly the whole-tree [ptree_maps], with the
   two intermediate PTEs read off [P] at 2 and 1. *)
Lemma ptree_maps_path_lvl2 (t : ptree) (v : mword 27) (P : nat -> mword 64) (p0 : mword 64) :
  ptree_maps_path_lvl 2 t v P p0 <-> ptree_maps t v (P 2%nat) (P 1%nat) p0.
Proof.
  split.
  - intros (c1 & Hk2 & He2 & Hv2 & Hp2 & Hu2 &
            c0 & Hk1 & He1 & Hv1 & Hp1 & Hu1 & He0 & Hvl & Hlf & Hnn & Hpb).
    exists c1, c0. repeat split; assumption.
  - intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hu2 & Hu1 &
            Hv2 & Hp2 & Hv1 & Hp1 & Hvl & Hlf & Hnn & Hpb).
    exists c1. repeat split; try assumption.
    exists c0. repeat split; assumption.
Qed.

(* the reverse of [ptree_blocks0_blocks0_lvl2]: flatten the fuel-nested
   disjunction back into the whole-tree three-way one. *)
Lemma ptree_blocks0_lvl2_blocks0 (t : ptree) (v : mword 27) :
  ptree_blocks0_lvl 2 t v -> ptree_blocks0 t v.
Proof.
  intros [ (Hn & Hz) | (c1 & Hk2 & Hv2 & Hp2 & Hu2 & Hb1) ].
  - left. split; assumption.
  - destruct Hb1 as [ (Hn1 & Hz1) | (c0 & Hk1 & Hv1 & Hp1 & Hu1 & Hb0) ].
    + right; left. exists c1. repeat split; assumption.
    + right; right. exists c1, c0. repeat split; assumption.
Qed.

(* the bridge: at the root level the fuel-generic relation is exactly the
   whole-tree [ptree_same_rep0] the walk's postcondition speaks. *)
Lemma ptree_same_rep0_lvl_2 (t t' : ptree) :
  ptree_same_rep0_lvl 2 t t' <-> ptree_same_rep0 t t'.
Proof.
  split; intros (Hb & Hm & Hbl); split; [ exact Hb | split | exact Hb | split ].
  - intros v p2 p1 p0.
    pose (P := fun k : nat => match k with 2%nat => p2 | _ => p1 end).
    change (ptree_maps t v (P 2%nat) (P 1%nat) p0 <-> ptree_maps t' v (P 2%nat) (P 1%nat) p0).
    rewrite <- !(ptree_maps_path_lvl2 _ v P p0). exact (Hm v P p0).
  - intros v. split; intro H.
    + apply ptree_blocks0_lvl2_blocks0. apply (Hbl v).
      apply ptree_blocks0_blocks0_lvl2; exact H.
    + apply ptree_blocks0_lvl2_blocks0. apply (Hbl v).
      apply ptree_blocks0_blocks0_lvl2; exact H.
  - intros v P p0. rewrite !(ptree_maps_path_lvl2 _ v P p0). exact (Hm v (P 2%nat) (P 1%nat) p0).
  - intros v. split; intro H.
    + apply ptree_blocks0_blocks0_lvl2. apply (Hbl v).
      apply ptree_blocks0_lvl2_blocks0; exact H.
    + apply ptree_blocks0_blocks0_lvl2. apply (Hbl v).
      apply ptree_blocks0_lvl2_blocks0; exact H.
Qed.

(* ---- level0-threading: the zipper's restore extends a level-[l]
   [ptree_level0_lvl] fact up one level.  This is the second fact the walk
   loop threads (besides same-rep): the walk's tail wants [ptree_level0]
   for the exit page, and on the alloc path that comes from the freshly
   grafted empty chain.  Two flavours -- descend (V=1, kid already there,
   restore via [pt_upd_kid]) and graft (alloc, fresh ptr PTE + empty kid,
   restore via [pt_upd_kid (pt_upd_ent ...)]) -- plus the empty terminal. *)
Lemma ptree_level0_lvl_empty0 (b : mword 44) (vpn : mword 27) :
  ptree_level0_lvl 0 (pt_empty_node b) vpn (mword_of_int 0).
Proof. reflexivity. Qed.

Lemma ptree_level0_lvl_upd_kid_intro (l : nat) (t : ptree) (i : mword 9)
    (c' : ptree) (vpn : mword 27) (w : mword 64) :
  vpn_idx (S l) vpn = i ->
  pte_valid (pt_ents t i) -> pte_ptr (pt_ents t i) ->
  u_next_base (pt_ents t i) = pt_base c' ->
  ptree_level0_lvl l c' vpn w ->
  ptree_level0_lvl (S l) (pt_upd_kid t i (Some c')) vpn w.
Proof.
  intros Ei Hv Hp Hu H0. exists c'.
  rewrite !Ei pt_upd_kid_same pt_upd_kid_ents.
  repeat split; first [ reflexivity | exact Hv | exact Hp | exact Hu | exact H0 ].
Qed.

Lemma ptree_level0_lvl_graft_intro (l : nat) (t : ptree) (i : mword 9)
    (b : mword 44) (c' : ptree) (vpn : mword 27) (w : mword 64) :
  vpn_idx (S l) vpn = i ->
  pt_base c' = b ->
  ptree_level0_lvl l c' vpn w ->
  ptree_level0_lvl (S l) (pt_upd_kid (pt_upd_ent t i (pt_ptr_pte b)) i (Some c')) vpn w.
Proof.
  intros Ei Hb H0. exists c'.
  rewrite !Ei pt_upd_kid_same !pt_upd_kid_ents !pt_upd_ent_same pt_ptr_pte_base Hb.
  repeat split;
    first [ reflexivity | exact (pt_ptr_pte_valid b) | exact (pt_ptr_pte_ptr b)
          | exact H0 ].
Qed.

(* ---- leaf-carrying descent: like ptree_level0_lvl but records the actual
   level-0 page reached, so the walk's tail learns [u_next_base p1 = pt_base leaf]
   (the returned slot address sits in exactly the page the walk descended to). *)
Fixpoint ptree_leaf_lvl (lvl : nat) (t : ptree) (vpn : mword 27) (leaf : ptree) : Prop :=
  match lvl with
  | O => leaf = t
  | S l => exists c,
      pt_kids t (vpn_idx (S l) vpn) = Some c
      /\ pte_valid (pt_ents t (vpn_idx (S l) vpn))
      /\ pte_ptr (pt_ents t (vpn_idx (S l) vpn))
      /\ u_next_base (pt_ents t (vpn_idx (S l) vpn)) = pt_base c
      /\ ptree_leaf_lvl l c vpn leaf
  end.

Lemma ptree_leaf_lvl_upd_kid_intro (l : nat) (t : ptree) (i : mword 9)
    (c' leaf : ptree) (vpn : mword 27) :
  vpn_idx (S l) vpn = i ->
  pte_valid (pt_ents t i) -> pte_ptr (pt_ents t i) ->
  u_next_base (pt_ents t i) = pt_base c' ->
  ptree_leaf_lvl l c' vpn leaf ->
  ptree_leaf_lvl (S l) (pt_upd_kid t i (Some c')) vpn leaf.
Proof.
  intros Ei Hv Hp Hu H0. exists c'.
  rewrite !Ei pt_upd_kid_same pt_upd_kid_ents.
  repeat split; first [ reflexivity | exact Hv | exact Hp | exact Hu | exact H0 ].
Qed.

Lemma ptree_leaf_lvl_graft_intro (l : nat) (t : ptree) (i : mword 9)
    (b : mword 44) (c' leaf : ptree) (vpn : mword 27) :
  vpn_idx (S l) vpn = i ->
  pt_base c' = b ->
  ptree_leaf_lvl l c' vpn leaf ->
  ptree_leaf_lvl (S l) (pt_upd_kid (pt_upd_ent t i (pt_ptr_pte b)) i (Some c')) vpn leaf.
Proof.
  intros Ei Hb H0. exists c'.
  rewrite !Ei pt_upd_kid_same !pt_upd_kid_ents !pt_upd_ent_same pt_ptr_pte_base Hb.
  repeat split;
    first [ reflexivity | exact (pt_ptr_pte_valid b) | exact (pt_ptr_pte_ptr b)
          | exact H0 ].
Qed.

(* the root-level bridge: reaching [leaf] gives the whole-tree [ptree_level0]
   at [leaf]'s slot word, with the returned level-1 PTE pointing at [leaf]. *)
Lemma ptree_leaf_lvl_2 (tf : ptree) (vpn : mword 27) (leaf : ptree) :
  ptree_leaf_lvl 2 tf vpn leaf ->
  exists p2 p1,
    ptree_level0 tf vpn p2 p1 (pt_ents leaf (vpn_idx 0 vpn))
    /\ u_next_base p1 = pt_base leaf.
Proof.
  intros (c1 & Hk2 & Hv2 & Hp2 & Hu2 & c0 & Hk1 & Hv1 & Hp1 & Hu1 & Hl0).
  cbn in Hl0. subst c0.
  exists (pt_ents tf (vpn_idx 2 vpn)), (pt_ents c1 (vpn_idx 1 vpn)).
  split; [| exact Hu1].
  exists c1, leaf. repeat split; assumption.
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
  (* A6.21: a node is built at the USER tier ([Some cur_ctx]) -- a fresh
     kalloc page is a THREAD's, and installing it in the shared kernel table
     forgets the registration ([TsoCtx.ctx_phys_word_ledger]), which is
     exactly right: it stops being any one thread's. *)
  Context `{XI : TsoCtx.CurCtx}.

  (* the Pt4kWalk address facts at PtTree's [u_pte_addr] spelling
     (identical definitions; [exact] bridges by conversion) *)
  Local Lemma u_pte_addr_aligned8 (b : mword 44) (i : mword 9) :
    is_aligned_paddr (Physaddr (u_pte_addr b i)) 8 = true.
  Proof. exact (pte_addr_at_aligned8 b i). Qed.

  (* byte [j] of slot [i] of a node page = byte [i*8+j] of the page, at
     [PageGeom.page_base]'s spelling of the page's base.  [Pt4kWalk] states
     the same fact with [page_base] written out ([page_base] is
     definitionally that [zero_extend'/concat_vec] form, so [exact]
     bridges); it cannot state it at this spelling itself, because
     [PageGeom.v] imports the iris proofmode and Pt4kWalk.v is deliberately
     ssreflect-free (27 of its rewrites use the vanilla [rewrite .. by ..]
     form).  So the [page_base] restatement lives here, once -- PtFree.v's
     [pt_slots_any_phys] is its other consumer. *)
  Lemma pa_add_page_slot_pb (b : mword 44) (i j : nat) :
    (i < 512)%nat -> (j < 8)%nat ->
    pa_add (page_base b) (i * 8 + j)
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
    pt_node_claim b -∗
    ([∗ list] j ∈ seq 0 4096,
       TsoCtx.ctx_phys_pointsto TsoCtx.cur_ctx
         (pa_add (zero_extend' 64 (concat_vec b (zeros' 12 : mword 12))) j)
         dq (mword_of_int 0 : mword 8))
    -∗ ptree_own lvl dq (pt_empty_node b).
  Proof.
    iIntros "#Hcl Hbytes".
    iAssert (pt_page_own dq (pt_empty_node b)) with "[Hbytes]" as "Hpg".
    { iEval (change 4096%nat with (512 * 8)%nat) in "Hbytes".
      iEval (rewrite big_sepL_seq_chunk) in "Hbytes".
      rewrite /pt_page_own. rewrite pt_empty_node_base. iSplitR; [iExact "Hcl" |].
      rewrite /seqZ.
      rewrite big_sepL_fmap.
      iEval (change (Z.to_nat 512) with 512%nat).
      iApply (big_sepL_mono with "Hbytes").
      intros k i Hki. apply lookup_seq in Hki. destruct Hki as [-> Hlt].
      cbn [Nat.add pt_base pt_ents pt_empty_node].
      replace (Z.of_nat k + 0) with (Z.of_nat k) by lia.
      iIntros "Hb".
      rewrite (pt_slot_own_ctx (UTier TsoCtx.cur_ctx) TsoCtx.cur_ctx _ _ _
                 eq_refl).
      iApply TsoCtx.ctx_phys_word_pointsto_intro.
      { exact (u_pte_addr_aligned8 b (mword_of_int (Z.of_nat k))). }
      iApply (big_sepL_mono with "Hb").
      intros k' j Hkj. apply lookup_seq in Hkj. destruct Hkj as [-> Hjlt].
      cbn [Nat.add].
      rewrite nth_byte_zero.
      rewrite (pa_add_page_slot_pb b k k' Hlt Hjlt).
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
    pose proof (pt_bv9_range i) as Hir.
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

  (* extract a node's persistent identity claim (uniform-claims PHYSICAL
     TIER): the S-mode walk needs it to convert a slot word [↦ₚ₈ ⇄ ↦₈] via
     [pt_slot_phys_to_mem] (KptTree).  Non-destructive -- [pt_node_claim] is
     persistent, so tree ownership is kept. *)
  Lemma pt_page_own_claim (dq : dfrac) (t : ptree) :
    pt_page_own dq t ⊢ pt_node_claim (pt_base t) ∗ pt_page_own dq t.
  Proof.
    iIntros "[#Hcl Hs]".
    iSplitR; [iExact "Hcl" |].
    rewrite /pt_page_own. iSplitR; [iExact "Hcl" | iExact "Hs"].
  Qed.

  Lemma ptree_own_node_claim (lvl : nat) (dq : dfrac) (t : ptree) :
    ptree_own (S lvl) dq t ⊢ pt_node_claim (pt_base t) ∗ ptree_own (S lvl) dq t.
  Proof.
    iIntros "H". iEval (rewrite ptree_own_S) in "H". iDestruct "H" as "[Hpg Hks]".
    iDestruct (pt_page_own_claim with "Hpg") as "[#Hcl Hpg]".
    iSplitR; [iExact "Hcl" |].
    iEval (rewrite ptree_own_S). iSplitL "Hpg"; [iExact "Hpg" | iExact "Hks"].
  Qed.

  (* ---- read-only slot accessors (walk's descend reads) ---------------- *)

  Lemma ptree_own_slot2_ro (dq : dfrac) (t : ptree) (vpn : mword 27) :
    ptree_own 2 dq t ⊢
      pt_addr2 t vpn ↦ₚₜ{dq} pt_ents t (vpn_idx 2 vpn) ∗
      (pt_addr2 t vpn ↦ₚₜ{dq} pt_ents t (vpn_idx 2 vpn) -∗ ptree_own 2 dq t).
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
      pt_addr1 (pt_ents t (vpn_idx 2 vpn)) vpn ↦ₚₜ{dq} pt_ents c1 (vpn_idx 1 vpn) ∗
      (pt_addr1 (pt_ents t (vpn_idx 2 vpn)) vpn ↦ₚₜ{dq} pt_ents c1 (vpn_idx 1 vpn) -∗
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
  Lemma ptree_own_graft2 (dq : dfrac) (t : ptree) (vpn : mword 27) :
    pt_kids t (vpn_idx 2 vpn) = None ->
    ptree_own 2 dq t ⊢
      pt_addr2 t vpn ↦ₚₜ{dq} pt_ents t (vpn_idx 2 vpn) ∗
      (∀ b : mword 44,
      pt_addr2 t vpn ↦ₚₜ{dq} pt_ptr_pte b -∗
       ptree_own 1 dq (pt_empty_node b) -∗
       ptree_own 2 dq (pt_graft2 t vpn b)).
  Proof.
    intros Hk.
    iIntros "[Hpg Hks]".
    iDestruct (pt_page_own_acc dq t (vpn_idx 2 vpn) with "Hpg") as "[Hs2 Hpg]".
    iFrame "Hs2".
    iIntros (b) "Hs2 Hc".
    iSpecialize ("Hpg" $! (pt_ptr_pte b) with "Hs2").
    iDestruct (pt_kids_own_ins 1 dq t (vpn_idx 2 vpn) Hk with "Hks") as "Hks".
    iSpecialize ("Hks" $! (pt_empty_node b) with "Hc").
    rewrite ptree_own_S.
    iSplitL "Hpg"; [iExact "Hpg" | iExact "Hks"].
  Qed.

  (* L1 graft: [vpn]'s L1 slot cell (inside the existing kid [c1]) comes
     out; the closing wand takes the rewritten cell + the zeroed child *)
  Lemma ptree_own_graft1 (dq : dfrac) (t c1 : ptree) (vpn : mword 27) :
    pt_kids t (vpn_idx 2 vpn) = Some c1 ->
    pt_kids c1 (vpn_idx 1 vpn) = None ->
    u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1 ->
    ptree_own 2 dq t ⊢
      pt_addr1 (pt_ents t (vpn_idx 2 vpn)) vpn ↦ₚₜ{dq} pt_ents c1 (vpn_idx 1 vpn) ∗
      (∀ b : mword 44,
      pt_addr1 (pt_ents t (vpn_idx 2 vpn)) vpn ↦ₚₜ{dq} pt_ptr_pte b -∗
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
    iIntros (b) "Hs1 Hc".
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
      pt_node_claim (u_next_base p1) ∗
      pt_addr0 p1 vpn ↦ₚₜ{dq} w0 ∗
      (∀ w' : mword 64,
      pt_addr0 p1 vpn ↦ₚₜ{dq} w' -∗
         ptree_own 2 dq (ptree_set_leaf t vpn w')).
  Proof.
    intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 & _).
    iIntros "[Hpg Hks]".
    iDestruct (pt_kids_own_acc 1 dq t (vpn_idx 2 vpn) c1 Hk2 with "Hks") as "[Hc1 Hks]".
    iDestruct "Hc1" as "[Hpg1 Hks1]".
    iDestruct (pt_kids_own_acc 0 dq c1 (vpn_idx 1 vpn) c0 Hk1 with "Hks1") as "[Hc0 Hks1]".
    iDestruct "Hc0" as "[Hpg0 Hemp]".
    iDestruct (pt_page_own_claim with "Hpg0") as "[#Hcl0 Hpg0]".
    iSplitR; [rewrite Hb0; iExact "Hcl0" |].
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

  (* The READ-ONLY twin of [ptree_own_level0_upd] (the slot read of ismapped,
     walkaddr, and copyout's PTE_W test):
     same [ptree_level0] path over the [_ro] node/kid accessors, so the
     closing wand restores the SAME tree -- no [ptree_set_leaf].  Since both
     [ptree_own 2 dq t] occurrences are then IDENTICAL, do NOT introduce a
     bare [rewrite ptree_own_S] here (it would hit the goal's copy too); the
     [iSplitL] chain below closes the tree back up as it stands. *)
  Lemma ptree_own_level0_ro (dq : dfrac) (t : ptree) (vpn : mword 27)
      (p2 p1 w0 : mword 64) :
    ptree_level0 t vpn p2 p1 w0 ->
    ptree_own 2 dq t ⊢
      pt_node_claim (u_next_base p1) ∗
      pt_addr0 p1 vpn ↦ₚₜ{dq} w0 ∗
      (pt_addr0 p1 vpn ↦ₚₜ{dq} w0 -∗ ptree_own 2 dq t).
  Proof.
    intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 & _).
    iIntros "[Hpg Hks]".
    iDestruct (pt_kids_own_acc_ro 1 dq t (vpn_idx 2 vpn) c1 Hk2 with "Hks") as "[Hc1 Hks]".
    iDestruct "Hc1" as "[Hpg1 Hks1]".
    iDestruct (pt_kids_own_acc_ro 0 dq c1 (vpn_idx 1 vpn) c0 Hk1 with "Hks1") as "[Hc0 Hks1]".
    iDestruct "Hc0" as "[Hpg0 Hemp]".
    iDestruct (pt_page_own_claim with "Hpg0") as "[#Hcl0 Hpg0]".
    iSplitR; [rewrite Hb0; iExact "Hcl0" |].
    iDestruct (pt_page_own_acc_ro dq c0 (vpn_idx 0 vpn) with "Hpg0") as "[Hs0 Hpg0]".
    rewrite He0.
    unfold pt_addr0. rewrite Hb0.
    iFrame "Hs0".
    iIntros "Hs0".
    iSplitL "Hpg"; [iExact "Hpg" |].
    iApply "Hks".
    iSplitL "Hpg1"; [iExact "Hpg1" |].
    iApply "Hks1".
    iSplitL "Hpg0 Hs0"; [(iApply "Hpg0"; iExact "Hs0") | iExact "Hemp"].
  Qed.

  (* ===================================================================== *)
  (* LEVEL-GENERIC single-step descent accessors -- the reusable layer the  *)
  (* fuel-inducted walk loop needs.  [ptree_own_slot2_ro]/[slot1_ro],        *)
  (* [ptree_own_graft2]/[graft1] are the level-2/level-1 specializations.    *)
  (* ===================================================================== *)

  (* read node [t]'s own slot [i] (read-only), at ANY level [S lvl] *)
  Lemma ptree_own_cell_ro (lvl : nat) (dq : dfrac) (t : ptree) (i : mword 9) :
    ptree_own (S lvl) dq t ⊢
      u_pte_addr (pt_base t) i ↦ₚₜ{dq} pt_ents t i ∗
      (u_pte_addr (pt_base t) i ↦ₚₜ{dq} pt_ents t i -∗ ptree_own (S lvl) dq t).
  Proof.
    iIntros "[Hpg Hks]".
    iDestruct (pt_page_own_acc_ro dq t i with "Hpg") as "[Hs Hclose]".
    iFrame "Hs". iIntros "Hs". rewrite ptree_own_S.
    iSplitL "Hclose Hs"; [ iApply "Hclose"; iExact "Hs" | iExact "Hks" ].
  Qed.

  (* descend one level into an existing kid [c] at slot [i], frame-preserving:
     the closing wand takes ANY replacement child back (covers the pure descend
     AND a subtree modified deeper down). *)
  Lemma ptree_own_descend (lvl : nat) (dq : dfrac) (t c : ptree) (i : mword 9) :
    pt_kids t i = Some c ->
    ptree_own (S lvl) dq t ⊢
      ptree_own lvl dq c ∗
      (∀ c' : ptree, ptree_own lvl dq c' -∗ ptree_own (S lvl) dq (pt_upd_kid t i (Some c'))).
  Proof.
    intros Hk. rewrite ptree_own_S. iIntros "[Hpg Hks]".
    iDestruct (pt_kids_own_acc lvl dq t i c Hk with "Hks") as "[Hc Hclose]".
    iFrame "Hc". iIntros (c') "Hc'". rewrite ptree_own_S.
    iSplitL "Hpg"; [ iExact "Hpg" | iApply "Hclose"; iExact "Hc'" ].
  Qed.

  (* allocate under an EMPTY slot [i] (the walk's alloc arm), at ANY level *)
  Lemma ptree_own_graft (lvl : nat) (dq : dfrac) (t : ptree) (i : mword 9) :
    pt_kids t i = None ->
    ptree_own (S lvl) dq t ⊢
      u_pte_addr (pt_base t) i ↦ₚₜ{dq} pt_ents t i ∗
      (∀ b : mword 44,
      u_pte_addr (pt_base t) i ↦ₚₜ{dq} pt_ptr_pte b -∗
         ptree_own lvl dq (pt_empty_node b) -∗
         ptree_own (S lvl) dq (pt_graft t i b)).
  Proof.
    intros Hk. rewrite ptree_own_S. iIntros "[Hpg Hks]".
    iDestruct (pt_page_own_acc dq t i with "Hpg") as "[Hs Hpgc]".
    iFrame "Hs". iIntros (b) "Hs Hc".
    iSpecialize ("Hpgc" $! (pt_ptr_pte b) with "Hs").
    iDestruct (pt_kids_own_ins lvl dq (pt_upd_ent t i (pt_ptr_pte b)) i with "Hks") as "Hins".
    { exact Hk. }
    iSpecialize ("Hins" $! (pt_empty_node b) with "Hc").
    rewrite ptree_own_S. unfold pt_graft.
    iSplitL "Hpgc"; [ iExact "Hpgc" | iExact "Hins" ].
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

(* LEVEL-GENERIC slot address: the walk loop's srl/andi/slli/add at level [L]
   (shift amount [12 + 9*L] = the s4 counter's value) computes the
   description's level-[L] slot address.  Subsumes walk_slot_addr{0,1,2} so
   the fuel-generic loop body applies ONE lemma with its abstract level. *)
Lemma walk_slot_addr_lvl (L : nat) (b : mword 44) (va : mword 64) :
  (L <= 2)%nat ->
  uint va < 274877906944 ->
  add_vec
    (shift_bits_left
       (and_vec
          (shift_bits_right va
             (subrange_vec_dec (mword_of_int (12 + 9 * Z.of_nat L) : mword 64) (Z.sub log2_xlen 1) 0))
          (sign_extend' 64 (mword_of_int 511 : mword 12)))
       (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
    (zero_extend' 64 (concat_vec b (zeros' 12 : mword 12)))
  = u_pte_addr b (vpn_idx L (svpn_of va)).
Proof.
  intros HL Hva. destruct L as [|[|[|L']]].
  - change (12 + 9 * Z.of_nat 0)%Z with 12%Z. exact (walk_slot_addr0 b va Hva).
  - change (12 + 9 * Z.of_nat 1)%Z with 21%Z. exact (walk_slot_addr1 b va Hva).
  - change (12 + 9 * Z.of_nat 2)%Z with 30%Z. exact (walk_slot_addr2 b va Hva).
  - exfalso. lia.
Qed.

(* [andi w,1] keeps exactly bit 0 of [w] -- the VALUE the C source's
   [( *pte & PTE_V) ? 1 : 0] returns, and the ingredient of the walk's
   zero/nonzero verdict below. *)
Lemma andi1_unsigned (w : mword 64) :
  bv_unsigned (and_vec w (sign_extend' 64 (mword_of_int 1 : mword 12)) : mword 64)
  = Z.b2z (Z.odd (bv_unsigned w)).
Proof.
  unfold and_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  match goal with |- context [Z.land _ (bv_unsigned ?mm)] =>
    replace (bv_unsigned mm) with 1 by (vm_compute; reflexivity) end.
  change 1 with (Z.ones 1) at 1.
  rewrite Z.land_ones; [| apply Z.leb_le; reflexivity].
  change (2 ^ 1) with 2.
  apply Zmod_odd.
Qed.

(* the C walk's V-bit test: [andi a5, w, 1; beqz a5] branches exactly on
   bit 0 of the slot word *)
Lemma walk_vbit_eq (w : mword 64) :
  eq_vec (and_vec w (sign_extend' 64 (mword_of_int 1 : mword 12))) zero_reg
  = negb (Z.testbit (bv_unsigned w) 0).
Proof.
  pose proof (andi1_unsigned w) as Hand.
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

(* the VALUE side of the same test (ismapped RETURNS the masked word, where
   the walk only needs [walk_vbit_eq]'s zero/nonzero verdict): V IS bit 0, so
   [andi w,1] on a model-valid PTE is exactly 1.  [pte_invalid_bit0] +
   [pte_valid_invalid_excl] turn "valid" into "bit 0 is set". *)
Lemma pte_valid_bit0 (w : mword 64) :
  pte_valid w ->
  and_vec w (sign_extend' 64 (mword_of_int 1 : mword 12)) = mword_of_int 1.
Proof.
  intros Hv.
  assert (Hb : Z.testbit (bv_unsigned w) 0 = true).
  { destruct (Z.testbit (bv_unsigned w) 0) eqn:E; [reflexivity | exfalso].
    exact (pte_valid_invalid_excl w Hv (pte_invalid_bit0 _ E)). }
  rewrite Z.bit0_odd in Hb.
  apply bv_eq. rewrite andi1_unsigned. rewrite Hb.
  vm_compute; reflexivity.
Qed.

(* the c.andi immediate, in the shape [walk_vbit_eq]/[pte_valid_bit0] use *)
Lemma candi1_imm :
  (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64)
  = sign_extend' 64 (mword_of_int 1 : mword 12).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* THE V&U BIT TEST -- the same bridge one field wider.                    *)
(*                                                                         *)
(*   walkaddr merges C's two flag tests into a single                      *)
(*   [andi a3,a5,17] / [li a4,17] / [beq], i.e. it tests bits 0 (V) and 4  *)
(*   (U) at once.  [pte_vu_bits] is that test's verdict, in the form        *)
(*   [PtTree.pte_vu] states it -- over the model's flag accessors.  Only    *)
(*   the direction the TAKEN [beq] needs is proved: the fall-through arm    *)
(*   returns 0 and needs nothing.                                          *)
(* ---------------------------------------------------------------------- *)

Lemma andi17_unsigned (w : mword 64) :
  bv_unsigned (and_vec w (sign_extend' 64 (mword_of_int 17 : mword 12)) : mword 64)
  = Z.land (bv_unsigned w) 17.
Proof.
  unfold and_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  match goal with |- context [Z.land _ (bv_unsigned ?mm)] =>
    replace (bv_unsigned mm) with 17 by (vm_compute; reflexivity) end.
  reflexivity.
Qed.

Local Lemma pb_z_land_17 (x : Z) :
  Z.land x 17 = 17 -> Z.testbit x 0 = true /\ Z.testbit x 4 = true.
Proof.
  intros H. split.
  - apply (f_equal (fun z => Z.testbit z 0)) in H.
    rewrite Z.land_spec in H.
    assert (T : Z.testbit 17 0 = true) by (vm_compute; reflexivity).
    rewrite T in H. rewrite andb_true_r in H. exact H.
  - apply (f_equal (fun z => Z.testbit z 4)) in H.
    rewrite Z.land_spec in H.
    assert (T : Z.testbit 17 4 = true) by (vm_compute; reflexivity).
    rewrite T in H. rewrite andb_true_r in H. exact H.
Qed.

Local Lemma pb_z_bit_to_mod (y : Z) : Z.testbit y 0 = true -> y mod 2 = 1.
Proof. intros H. rewrite Z.bit0_odd in H. rewrite Zmod_odd. rewrite H. reflexivity. Qed.

Local Lemma pb_z_bit0_of (x : Z) : Z.testbit x 0 = true -> (x mod 256) mod 2 = 1.
Proof.
  intros H. apply pb_z_bit_to_mod.
  change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low; [exact H | lia].
Qed.

Local Lemma pb_z_bit4_of (x : Z) : Z.testbit x 4 = true -> (x mod 256) / 16 mod 2 = 1.
Proof.
  intros H. apply pb_z_bit_to_mod.
  change 16 with (2 ^ 4). rewrite Z.div_pow2_bits; [| lia | lia].
  change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low; [| lia].
  replace (0 + 4) with 4 by lia. exact H.
Qed.

(* the flag-byte field extractions, off the width-generic
   [RiscvExtras.subrange_dec_unsigned] *)
Local Lemma pb_sub_7_0 (v : mword 64) :
  bv_unsigned (subrange_vec_dec v 7 0 : mword 8) = bv_unsigned v mod 256.
Proof. apply (subrange_dec_unsigned_lo0 v 7 256); [lia | reflexivity]. Qed.
Local Lemma pb_sub_0_0 (v : mword 8) :
  bv_unsigned (subrange_vec_dec v 0 0 : mword 1) = bv_unsigned v mod 2.
Proof. apply (subrange_dec_unsigned_lo0 v 0 2); [lia | reflexivity]. Qed.
Local Lemma pb_sub_4_4 (v : mword 8) :
  bv_unsigned (subrange_vec_dec v 4 4 : mword 1) = bv_unsigned v / 16 mod 2.
Proof. apply (subrange_dec_unsigned v 4 4 16 2); [lia | lia | reflexivity | reflexivity]. Qed.

Lemma pte_vu_bits (w : mword 64) :
  and_vec w (sign_extend' 64 (mword_of_int 17 : mword 12)) = (mword_of_int 17 : mword 64) ->
  pte_vu w.
Proof.
  intros Hand.
  apply (f_equal bv_unsigned) in Hand.
  rewrite andi17_unsigned in Hand.
  assert (H17 : bv_unsigned (mword_of_int 17 : mword 64) = 17) by (vm_compute; reflexivity).
  rewrite H17 in Hand.
  destruct (pb_z_land_17 _ Hand) as [Hb0 Hb4].
  unfold pte_vu, _get_PTE_Flags_V, _get_PTE_Flags_U, Mk_PTE_Flags.
  assert (H1 : bv_unsigned ('b"1" : mword 1) = 1) by (vm_compute; reflexivity).
  split; apply bv_eq; rewrite H1.
  - rewrite pb_sub_0_0. rewrite pb_sub_7_0. apply pb_z_bit0_of. exact Hb0.
  - rewrite pb_sub_4_4. rewrite pb_sub_7_0. apply pb_z_bit4_of. exact Hb4.
Qed.

(* ---------------------------------------------------------------------- *)
(* THE R|W|X MASK TEST -- the third member of the family.                  *)
(*                                                                         *)
(*   freewalk's [( *pte & (PTE_R|PTE_W|PTE_X)) == 0] is an [andi a4,a5,14]  *)
(*   against bits 1..3, so it is the same bridge as [pte_valid_bit0] (the   *)
(*   V bit) and [pte_vu_bits] (the V|U pair) one more field over: a         *)
(*   NON-LEAF word masks to zero.                                          *)
(* ---------------------------------------------------------------------- *)

Local Lemma pb_sub_1_1 (v : mword 8) :
  bv_unsigned (subrange_vec_dec v 1 1 : mword 1) = bv_unsigned v / 2 ^ 1 mod 2.
Proof. apply (subrange_dec_unsigned v 1 1 (2 ^ 1) 2); [lia | lia | reflexivity | reflexivity]. Qed.
Local Lemma pb_sub_2_2 (v : mword 8) :
  bv_unsigned (subrange_vec_dec v 2 2 : mword 1) = bv_unsigned v / 2 ^ 2 mod 2.
Proof. apply (subrange_dec_unsigned v 2 2 (2 ^ 2) 2); [lia | lia | reflexivity | reflexivity]. Qed.
Local Lemma pb_sub_3_3 (v : mword 8) :
  bv_unsigned (subrange_vec_dec v 3 3 : mword 1) = bv_unsigned v / 2 ^ 3 mod 2.
Proof. apply (subrange_dec_unsigned v 3 3 (2 ^ 3) 2); [lia | lia | reflexivity | reflexivity]. Qed.

Local Lemma pb_z_bit_false (y : Z) : y mod 2 = 0 -> Z.odd y = false.
Proof. intros H. rewrite Zmod_odd in H. destruct (Z.odd y); [discriminate | reflexivity]. Qed.

(* a flag-byte bit read back as a bit of the whole word *)
Local Lemma pb_bitn (x n : Z) :
  0 <= n -> n < 8 -> (x mod 256) / 2 ^ n mod 2 = 0 -> Z.testbit x n = false.
Proof.
  intros Hn0 Hn8 H.
  change 256 with (2 ^ 8) in H.
  apply pb_z_bit_false in H.
  rewrite <- Z.bit0_odd in H.
  rewrite (Z.div_pow2_bits (x mod 2 ^ 8) n 0 Hn0 ltac:(lia)) in H.
  replace (0 + n) with n in H by lia.
  rewrite (Z.mod_pow2_bits_low x 8 n ltac:(lia)) in H.
  exact H.
Qed.

Local Lemma pb_z_land14 (x : Z) :
  Z.testbit x 1 = false -> Z.testbit x 2 = false -> Z.testbit x 3 = false ->
  Z.land x 14 = 0.
Proof.
  intros H1 H2 H3. apply Z.bits_inj_0. intros n.
  destruct (Z_lt_le_dec n 0) as [Hn | Hn].
  { apply Z.testbit_neg_r. exact Hn. }
  rewrite Z.land_spec.
  destruct (Z.eq_dec n 0) as [-> | Hn0].
  { replace (Z.testbit 14 0) with false by (vm_compute; reflexivity). apply andb_false_r. }
  destruct (Z.eq_dec n 1) as [-> | Hn1]. { rewrite H1. reflexivity. }
  destruct (Z.eq_dec n 2) as [-> | Hn2]. { rewrite H2. reflexivity. }
  destruct (Z.eq_dec n 3) as [-> | Hn3]. { rewrite H3. reflexivity. }
  replace (Z.testbit 14 n) with false; [apply andb_false_r |].
  symmetry. apply Z.bits_above_log2; [lia |].
  replace (Z.log2 14) with 3 by (vm_compute; reflexivity). lia.
Qed.

Lemma andi14_unsigned (w : mword 64) :
  bv_unsigned (and_vec w (sign_extend' 64 (mword_of_int 14 : mword 12)) : mword 64)
  = Z.land (bv_unsigned w) 14.
Proof.
  unfold and_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  match goal with |- context [Z.land _ (bv_unsigned ?mm)] =>
    replace (bv_unsigned mm) with 14 by (vm_compute; reflexivity) end.
  reflexivity.
Qed.

(* the C's [(pte & (PTE_R|PTE_W|PTE_X)) == 0] test on a NON-LEAF word *)
Lemma fw_ptr_and14 (w : mword 64) :
  pte_ptr w ->
  and_vec w (sign_extend' 64 (mword_of_int 14 : mword 12)) = (mword_of_int 0 : mword 64).
Proof.
  intros Hp.
  unfold pte_ptr, pte_is_non_leaf, Mk_PTE_Flags in Hp.
  apply andb_prop in Hp. destruct Hp as [HX Hp].
  apply andb_prop in Hp. destruct Hp as [HW HR].
  apply eq_vec_true_iff in HX. apply eq_vec_true_iff in HW. apply eq_vec_true_iff in HR.
  unfold _get_PTE_Flags_X in HX. unfold _get_PTE_Flags_W in HW. unfold _get_PTE_Flags_R in HR.
  apply (f_equal bv_unsigned) in HX.
  apply (f_equal bv_unsigned) in HW.
  apply (f_equal bv_unsigned) in HR.
  rewrite pb_sub_3_3 pb_sub_7_0 in HX.
  rewrite pb_sub_2_2 pb_sub_7_0 in HW.
  rewrite pb_sub_1_1 pb_sub_7_0 in HR.
  replace (bv_unsigned ('b"0" : mword 1)) with 0 in HX by (vm_compute; reflexivity).
  replace (bv_unsigned ('b"0" : mword 1)) with 0 in HW by (vm_compute; reflexivity).
  replace (bv_unsigned ('b"0" : mword 1)) with 0 in HR by (vm_compute; reflexivity).
  apply bv_eq. rewrite andi14_unsigned.
  rewrite (pb_z_land14 (bv_unsigned w)
             (pb_bitn (bv_unsigned w) 1 ltac:(lia) ltac:(lia) HR)
             (pb_bitn (bv_unsigned w) 2 ltac:(lia) ltac:(lia) HW)
             (pb_bitn (bv_unsigned w) 3 ltac:(lia) ltac:(lia) HX)).
  vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(* §8 mappages bridges: the pure facts wp_mappages' loop body needs.      *)
(* ===================================================================== *)



Local Lemma pb_add_vec_int27_wrap (a : mword 27) (j : Z) :
  0 <= j < 134217728 ->
  bv_unsigned (add_vec_int a j) = bv_wrap 27 (bv_unsigned a + j).
Proof.
  intros Hj.
  unfold add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hjv : bv_unsigned (mword_of_int j : mword 27) = j).
  { unfold mword_of_int, Values.to_word, get_word. cbn.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus. cbn. lia. }
  rewrite Hjv. reflexivity.
Qed.

(* walk returned the L0 slot of an UNMAPPED vpn: the slot word is the
   literal zero (pt_rep0's blocks0 arm against the level0 path) *)
Lemma pt_rep0_level0_zero (t : ptree) (m : gmap (mword 27) (mword 64))
    (vpn : mword 27) (p2 p1 w0 : mword 64) :
  pt_rep0 t m -> m !! vpn = None -> ptree_level0 t vpn p2 p1 w0 ->
  w0 = mword_of_int 0.
Proof.
  intros (Hmap & Hblk) Hnone
    (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 & Hv2 & Hp2 & Hv1 & Hp1).
  destruct (Hblk vpn Hnone) as
    [ (Hk2n & _)
    | [ (c1' & Hk2' & Hk1' & _)
      | (c1' & c0' & Hk2' & Hk1' & _ & _ & _ & _ & _ & _ & He0z) ] ].
  - rewrite Hk2n in Hk2. discriminate.
  - rewrite Hk2' in Hk2. injection Hk2 as ->. rewrite Hk1' in Hk1. discriminate.
  - rewrite Hk2' in Hk2. injection Hk2 as ->.
    rewrite Hk1' in Hk1. injection Hk1 as ->.
    rewrite He0z in He0. exact (eq_sym He0).
Qed.

(* distinct pages of a run have distinct vpns (the indices fit in 2^27) *)
Lemma vpn_at_ne (vpn0 : mword 27) (j k : nat) :
  (j < k)%nat -> (Z.of_nat k < 134217728)%Z ->
  vpn_at vpn0 j <> vpn_at vpn0 k.
Proof.
  intros Hjk Hk Heq.
  unfold vpn_at in Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (pb_add_vec_int27_wrap vpn0 (Z.of_nat j) ltac:(lia)) in Heq.
  rewrite (pb_add_vec_int27_wrap vpn0 (Z.of_nat k) ltac:(lia)) in Heq.
  unfold bv_wrap in Heq.
  assert (HM : bv_modulus 27 = 134217728) by (vm_compute; reflexivity).
  rewrite HM in Heq.
  assert (Hz : (Z.of_nat k - Z.of_nat j) `mod` 134217728 = 0).
  { replace (Z.of_nat k - Z.of_nat j)
      with ((bv_unsigned vpn0 + Z.of_nat k) - (bv_unsigned vpn0 + Z.of_nat j)) by lia.
    rewrite Zminus_mod. rewrite Heq. rewrite Z.sub_diag. reflexivity. }
  rewrite Z.mod_small in Hz; lia.
Qed.

(* the current page's vpn stays unmapped after the previous inserts *)
Lemma pt_insert_run_lookup_None (m : gmap (mword 27) (mword 64))
    (vpn0 : mword 27) (ppn0 : mword 44) (perm : Z) (j k : nat) :
  (k <= j)%nat -> (Z.of_nat j < 134217728)%Z ->
  m !! vpn_at vpn0 j = None ->
  pt_insert_run m vpn0 ppn0 perm k !! vpn_at vpn0 j = None.
Proof.
  intros Hkj Hj Hnone.
  induction k as [| k' IH]; [exact Hnone |].
  cbn.
  assert (Hne : vpn_at vpn0 k' <> vpn_at vpn0 j)
    by (apply vpn_at_ne; lia).
  assert (Hstep : <[vpn_at vpn0 k' := mappages_pte ppn0 perm k']>
                    (pt_insert_run m vpn0 ppn0 perm k') !! vpn_at vpn0 j
                  = pt_insert_run m vpn0 ppn0 perm k' !! vpn_at vpn0 j).
  { apply lookup_insert_ne. exact Hne. }
  rewrite Hstep. apply IH. lia.
Qed.


(* ---- 64-bit run arithmetic ---------------------------------------- *)

Local Lemma pb_subrange64_unsigned_11_0 (x : mword 64) :
  bv_unsigned (subrange_vec_dec x 11 0) = bv_unsigned x `mod` 2 ^ 12.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0.
  rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (11 - 0 + 1)) with 12%N.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma aligned12_unsigned (a : mword 64) :
  subrange_vec_dec a 11 0 = (zeros' 12 : mword 12) ->
  bv_unsigned a `mod` 4096 = 0.
Proof.
  intros Hs. apply (f_equal bv_unsigned) in Hs.
  rewrite pb_subrange64_unsigned_11_0 in Hs.
  change (2 ^ 12) with 4096 in Hs.
  replace (bv_unsigned (zeros' 12 : mword 12)) with 0 in Hs by (vm_compute; reflexivity).
  exact Hs.
Qed.

Local Lemma pb_wrap64_add_inj (x A B : Z) :
  0 <= A < 18446744073709551616 -> 0 <= B < 18446744073709551616 ->
  bv_wrap 64 (x + A) = bv_wrap 64 (x + B) -> A = B.
Proof.
  intros HA HB Heq.
  unfold bv_wrap in Heq.
  assert (HM : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite HM in Heq.
  destruct (Z.le_gt_cases B A) as [Hle | Hgt].
  - assert (HzA : (A - B) `mod` 18446744073709551616 = 0).
    { replace (A - B) with ((x + A) - (x + B)) by lia.
      rewrite Zminus_mod. rewrite Heq. rewrite Z.sub_diag. reflexivity. }
    rewrite Z.mod_small in HzA; lia.
  - assert (HzB : (B - A) `mod` 18446744073709551616 = 0).
    { replace (B - A) with ((x + B) - (x + A)) by lia.
      rewrite Zminus_mod. rewrite Heq. rewrite Z.sub_diag. reflexivity. }
    rewrite Z.mod_small in HzB; lia.
Qed.

Lemma pb_va_k_unsigned (va : mword 64) (k : nat) :
  (bv_unsigned va + 4096 * Z.of_nat k < 18446744073709551616)%Z ->
  bv_unsigned (add_vec va (mword_of_int (4096 * Z.of_nat k)))
  = bv_unsigned va + 4096 * Z.of_nat k.
Proof.
  intros Hb.
  rewrite add_vec64_unsigned. rewrite moi64_unsigned.
  rewrite bv_wrap_add_idemp_r.
  apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  pose proof (bv_unsigned_in_range _ va) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616 in Hr.
  lia.
Qed.

(* the vpn of page [k] of the run *)
Lemma svpn_of_run (va : mword 64) (k : nat) :
  (bv_unsigned va + 4096 * Z.of_nat k < 274877906944)%Z ->
  svpn_of (add_vec va (mword_of_int (4096 * Z.of_nat k))) = vpn_at (svpn_of va) k.
Proof.
  intros Hb.
  pose proof (bv_unsigned_in_range _ va) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616 in Hr.
  assert (Hu : bv_unsigned (add_vec va (mword_of_int (4096 * Z.of_nat k)))
               = bv_unsigned va + 4096 * Z.of_nat k)
    by (apply pb_va_k_unsigned; lia).
  apply bv_eq.
  rewrite (svpn_of_unsigned_lo (add_vec va (mword_of_int (4096 * Z.of_nat k)))
             ltac:(rewrite uint_unsigned; rewrite Hu; lia)).
  rewrite uint_unsigned. rewrite Hu.
  unfold vpn_at.
  rewrite (pb_add_vec_int27_wrap (svpn_of va) (Z.of_nat k) ltac:(lia)).
  rewrite (svpn_of_unsigned_lo va ltac:(rewrite uint_unsigned; lia)).
  rewrite uint_unsigned.
  rewrite Z.shiftr_div_pow2; [| lia].
  rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 12) with 4096.
  replace (bv_unsigned va + 4096 * Z.of_nat k)
    with (bv_unsigned va + Z.of_nat k * 4096) by lia.
  rewrite Z.div_add; [| lia].
  assert (Hdiv : bv_unsigned va `div` 4096 + Z.of_nat k < 134217728).
  { pose proof (Z.div_lt_upper_bound (bv_unsigned va) 4096 67108864
                  ltac:(lia) ltac:(lia)). lia. }
  rewrite bv_wrap_small; [reflexivity |].
  split.
  - pose proof (Z.div_pos (bv_unsigned va) 4096 ltac:(lia) ltac:(lia)). lia.
  - unfold bv_modulus. change (2 ^ Z.of_N 27) with 134217728. exact Hdiv.
Qed.

(* stepping s1 by PGSIZE *)
Lemma mappages_va_step (va : mword 64) (k : nat) (w : mword 64) :
  bv_unsigned w = 4096 ->
  add_vec (add_vec va (mword_of_int (4096 * Z.of_nat k))) w
  = add_vec va (mword_of_int (4096 * Z.of_nat (S k))).
Proof.
  intros Hw. apply bv_eq.
  rewrite !add_vec64_unsigned. rewrite !moi64_unsigned. rewrite Hw.
  rewrite bv_wrap_add_idemp_l.
  replace (bv_unsigned va + bv_wrap 64 (4096 * Z.of_nat k) + 4096)
    with (bv_unsigned va + 4096 + bv_wrap 64 (4096 * Z.of_nat k)) by lia.
  rewrite !bv_wrap_add_idemp_r.
  f_equal. lia.
Qed.

(* the beq loop-exit dichotomy *)
Lemma mappages_va_eq_iff (va : mword 64) (j k : nat) :
  (4096 * Z.of_nat j < 18446744073709551616)%Z ->
  (4096 * Z.of_nat k < 18446744073709551616)%Z ->
  add_vec va (mword_of_int (4096 * Z.of_nat j)) = add_vec va (mword_of_int (4096 * Z.of_nat k))
  <-> j = k.
Proof.
  intros Hj Hk. split; [| intros ->; reflexivity].
  intros Heq. apply (f_equal bv_unsigned) in Heq.
  rewrite !add_vec64_unsigned in Heq. rewrite !moi64_unsigned in Heq.
  rewrite !bv_wrap_add_idemp_r in Heq.
  apply pb_wrap64_add_inj in Heq; lia.
Qed.

(* the entry alignment probe: an aligned address shifted 52 left is zero *)
Lemma mappages_align_probe (x : mword 64) :
  bv_unsigned x `mod` 4096 = 0 ->
  shift_bits_left x (subrange_vec_dec (mword_of_int 52 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int 0 : mword 64).
Proof.
  intros Hal.
  assert (Hred : shift_bits_left x (subrange_vec_dec (mword_of_int 52 : mword 6) (Z.sub log2_xlen 1) 0)
                 = shiftl x 52).
  { unfold shift_bits_left.
    f_equal.
    all: try (vm_compute; reflexivity).
    all: f_equal; vm_compute; reflexivity. }
  rewrite Hred. apply bv_eq.
  unfold shiftl, with_word, get_word,
    MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 52))) with 52
    by (vm_compute; reflexivity).
  replace (bv_unsigned (mword_of_int 0 : mword 64)) with 0 by (vm_compute; reflexivity).
  rewrite Z.shiftl_mul_pow2; [| lia].
  rewrite (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)).
  rewrite Hal. rewrite Z.add_0_r.
  replace (4096 * (bv_unsigned x `div` 4096) * 2 ^ 52)
    with ((bv_unsigned x `div` 4096) * 18446744073709551616) by lia.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616.
  apply Z.mod_mul. lia.
Qed.


(* ---- pa-side run arithmetic ---------------------------------------- *)

Local Lemma pb_subrange_55_12_unsigned (a : mword 64) :
  bv_unsigned a < 72057594037927936 ->
  bv_unsigned (autocast (T := mword) (subrange_vec_dec a 55 12) : mword 44)
  = bv_unsigned a / 4096.
Proof.
  intros Hlt.
  rewrite autocast_id.
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
  - apply Z.div_pos; [exact (proj1 (bv_unsigned_in_range _ a)) | reflexivity].
  - apply Z.div_lt_upper_bound; [reflexivity |].
    change (4096 * 17592186044416) with 72057594037927936.
    exact Hlt.
Qed.

Local Lemma pb_add_vec_int44_wrap (a : mword 44) (j : Z) :
  0 <= j < 17592186044416 ->
  bv_unsigned (add_vec_int a j) = bv_wrap 44 (bv_unsigned a + j).
Proof.
  intros Hj.
  unfold add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hjv : bv_unsigned (mword_of_int j : mword 44) = j).
  { unfold mword_of_int, Values.to_word, get_word. cbn.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus. cbn. lia. }
  rewrite Hjv. reflexivity.
Qed.

(* the ppn of page [k] of the run *)
Lemma run_ppn (pa : mword 64) (k : nat) :
  (bv_unsigned pa + 4096 * Z.of_nat k < 72057594037927936)%Z ->
  (autocast (T := mword) (subrange_vec_dec (add_vec pa (mword_of_int (4096 * Z.of_nat k))) 55 12) : mword 44)
  = add_vec_int (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44) (Z.of_nat k).
Proof.
  intros Hb.
  pose proof (bv_unsigned_in_range _ pa) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616 in Hr.
  assert (Hu : bv_unsigned (add_vec pa (mword_of_int (4096 * Z.of_nat k)))
               = bv_unsigned pa + 4096 * Z.of_nat k)
    by (apply pb_va_k_unsigned; lia).
  apply bv_eq.
  rewrite pb_subrange_55_12_unsigned; [| rewrite Hu; lia].
  rewrite Hu.
  rewrite (pb_add_vec_int44_wrap _ (Z.of_nat k) ltac:(lia)).
  rewrite pb_subrange_55_12_unsigned; [| lia].
  replace (bv_unsigned pa + 4096 * Z.of_nat k)
    with (bv_unsigned pa + Z.of_nat k * 4096) by lia.
  rewrite Z.div_add; [| lia].
  rewrite bv_wrap_small; [reflexivity |].
  split.
  - pose proof (Z.div_pos (bv_unsigned pa) 4096 ltac:(lia) ltac:(lia)). lia.
  - unfold bv_modulus. change (2 ^ Z.of_N 44) with 17592186044416.
    pose proof (Z.div_lt_upper_bound (bv_unsigned pa) 4096
                  (17592186044416 - Z.of_nat k) ltac:(lia) ltac:(lia)).
    lia.
Qed.

(* ---- the leaf PTE the loop stores ----------------------------------- *)

Lemma pb_lor1_range (perm : Z) :
  0 <= perm < 1024 -> 0 <= Z.lor perm 1 < 1024.
Proof.
  intros Hp.
  split; [apply Z.lor_nonneg; lia |].
  assert (Hpos : 0 < Z.lor perm 1).
  { assert (Hn : 0 <= Z.lor perm 1) by (apply Z.lor_nonneg; lia).
    destruct (Z.eq_dec (Z.lor perm 1) 0) as [He | Hne]; [| lia].
    apply (f_equal (fun z => Z.testbit z 0)) in He.
    rewrite Z.lor_spec in He.
    change (Z.testbit 1 0) with true in He.
    rewrite orb_true_r in He.
    rewrite Z.bits_0 in He.
    discriminate He. }
  change 1024 with (2 ^ 10).
  apply (proj2 (Z.log2_lt_pow2 _ 10 Hpos)).
  rewrite Z.log2_lor; [| lia | lia].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec perm 0) as [-> | Hnz]; [vm_compute; reflexivity |].
    apply (proj1 (Z.log2_lt_pow2 perm 10 ltac:(lia))).
    change (2 ^ 10) with 1024. lia.
  - vm_compute. reflexivity.
Qed.

(* the srli/slli/or/ori chain computes exactly [mk_pte] of the page *)
Lemma mappages_pte_compute (p : mword 64) (perm : Z) (w5 : mword 64) :
  bv_unsigned w5 = perm ->
  0 <= perm < 1024 ->
  bv_unsigned p `mod` 4096 = 0 ->
  bv_unsigned p < 72057594037927936 ->
  or_vec (or_vec
    (shift_bits_left
       (shift_bits_right p (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
       (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
    w5)
    (sign_extend' 64 (mword_of_int 1 : mword 12))
  = mk_pte (autocast (T := mword) (subrange_vec_dec p 55 12) : mword 44) (Z.lor perm 1).
Proof.
  intros Hw5 Hperm Hal Hlt.
  assert (Hred : shift_bits_left
      (shift_bits_right p (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
      (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0)
    = shiftl (shiftr p 12) 10).
  { unfold shift_bits_left, shift_bits_right.
    f_equal.
    all: try (vm_compute; reflexivity).
    all: f_equal; vm_compute; reflexivity. }
  rewrite Hred.
  pose proof (pb_lor1_range perm Hperm) as Hf.
  apply bv_eq.
  rewrite (mk_pte_unsigned _ (Z.lor perm 1) Hf).
  rewrite pb_subrange_55_12_unsigned; [| exact Hlt].
  unfold or_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.or.
  rewrite !bv_or_unsigned.
  replace (bv_unsigned (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)) with 1
    by (vm_compute; reflexivity).
  rewrite Hw5.
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
  assert (Hq : 0 <= bv_unsigned p / 4096 < 17592186044416)
    by (split; [apply Z.div_pos; pose proof (bv_unsigned_in_range _ p); lia
               | apply Z.div_lt_upper_bound; lia]).
  replace (Z.shiftl (bv_unsigned p / 4096) 10) with (bv_unsigned p / 4096 * 1024)
    by (rewrite Z.shiftl_mul_pow2; [reflexivity | lia]).
  rewrite bv_wrap_small.
  2:{ unfold bv_modulus.
      change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616.
      lia. }
  rewrite <- Z.lor_assoc.
  rewrite <- Z_lor_disjoint_add.
  - reflexivity.
  - change 1024 with (2 ^ 10).
    apply Z_land_shift_low.
    + apply Z.leb_le; reflexivity.
    + change (2 ^ 10) with 1024.
      split; [apply Z.lor_nonneg; lia | lia].
Qed.

(* ---- classification of the stored leaf ------------------------------ *)

(* everything walk/mappages needs of the flag bits, checked once at the
   ZERO ppn (the predicates read only the flag byte and the ext field,
   both ppn-independent) *)
Definition mappages_perm_ok (perm : Z) : Prop :=
  (0 <= perm < 1024)%Z /\
  pte_valid (mk_pte (zeros' 44) (Z.lor perm 1)) /\
  pte_leaf (mk_pte (zeros' 44) (Z.lor perm 1)) /\
  pte_no_napot (mk_pte (zeros' 44) (Z.lor perm 1)) /\
  pte_pbmt0 (mk_pte (zeros' 44) (Z.lor perm 1)).

Lemma mappages_pte_class (ppn : mword 44) (perm : Z) :
  mappages_perm_ok perm ->
  pte_valid (mk_pte ppn (Z.lor perm 1)) /\
  pte_leaf (mk_pte ppn (Z.lor perm 1)) /\
  pte_no_napot (mk_pte ppn (Z.lor perm 1)) /\
  pte_pbmt0 (mk_pte ppn (Z.lor perm 1)).
Proof.
  intros (Hr & Hv & Hl & Hn & Hp).
  pose proof (pb_lor1_range perm Hr) as Hf.
  pose proof (mk_pte_flags1024 ppn (Z.lor perm 1) Hf) as Hfl.
  pose proof (mk_pte_flags1024 (zeros' 44) (Z.lor perm 1) Hf) as Hfl0.
  pose proof (mk_pte_ext_word ppn (Z.lor perm 1) Hf) as He.
  split; [| split; [| split]].
  - intros s. rewrite Hfl. rewrite He.
    specialize (Hv s). rewrite Hfl0 in Hv. exact Hv.
  - unfold pte_leaf in Hl |- *. rewrite Hfl. rewrite Hfl0 in Hl. exact Hl.
  - unfold pte_no_napot in Hn |- *. rewrite He. exact Hn.
  - unfold pte_pbmt0 in Hp |- *. rewrite He. exact Hp.
Qed.


(* ---- prologue / loop-body glue -------------------------------------- *)


(* adding [pa - va] to the k-th va lands on the k-th pa *)
Lemma mappages_pa_of_va (va pa : mword 64) (k : nat) :
  add_vec (add_vec va (mword_of_int (4096 * Z.of_nat k))) (sub_vec pa va)
  = add_vec pa (mword_of_int (4096 * Z.of_nat k)).
Proof.
  apply bv_eq.
  rewrite !add_vec64_unsigned. rewrite !moi64_unsigned.
  rewrite bv_wrap_add_idemp_l.
  replace (bv_unsigned va + bv_wrap 64 (4096 * Z.of_nat k)
           + bv_wrap 64 (bv_unsigned pa - bv_unsigned va))
    with (bv_wrap 64 (bv_unsigned pa - bv_unsigned va)
          + (bv_unsigned va + bv_wrap 64 (4096 * Z.of_nat k))) by lia.
  rewrite bv_wrap_add_idemp_l.
  replace (bv_unsigned pa - bv_unsigned va + (bv_unsigned va + bv_wrap 64 (4096 * Z.of_nat k)))
    with (bv_unsigned pa + bv_wrap 64 (4096 * Z.of_nat k)) by lia.
  rewrite bv_wrap_add_idemp_r.
  reflexivity.
Qed.

(* the prologue's s2: size - PGSIZE added to va is the LAST page's va *)
Lemma mappages_s2_val (va a2v : mword 64) (npages : nat) :
  bv_unsigned a2v = Z.of_nat npages * 4096 ->
  (1 <= npages)%nat ->
  add_vec (add_vec (add_vec a2v (sign_extend' 64 (mword_of_int 2048 : mword 12)))
             (sign_extend' 64 (mword_of_int 2048 : mword 12))) va
  = add_vec va (mword_of_int (4096 * Z.of_nat (npages - 1))).
Proof.
  intros Ha2 Hn.
  apply bv_eq.
  rewrite !add_vec64_unsigned. rewrite !moi64_unsigned.
  rewrite Ha2.
  rewrite bv_wrap_add_idemp_l.
  replace (bv_wrap 64 (bv_signed (get_word (mword_of_int 2048 : mword 12))))
    with 18446744073709549568 by (vm_compute; reflexivity).
  replace (bv_wrap 64 (Z.of_nat npages * 4096 + 18446744073709549568)
             + 18446744073709549568 + bv_unsigned va)
    with (bv_unsigned va + 18446744073709549568
            + bv_wrap 64 (Z.of_nat npages * 4096 + 18446744073709549568)) by lia.
  rewrite bv_wrap_add_idemp_r.
  rewrite bv_wrap_add_idemp_r.
  replace (bv_unsigned va + 18446744073709549568
             + (Z.of_nat npages * 4096 + 18446744073709549568))
    with (bv_unsigned va + 4096 * Z.of_nat (npages - 1) + 2 * 18446744073709551616) by lia.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite (Z.mod_add (bv_unsigned va + 4096 * Z.of_nat (npages - 1)) 2
             18446744073709551616); [reflexivity | lia].
Qed.

(* the size word is nonzero (the beqz size-check falls through) *)
Lemma mappages_size_nonzero (npages : nat) :
  (1 <= npages)%nat ->
  (Z.of_nat npages * 4096 < 18446744073709551616)%Z ->
  bv_unsigned (mword_of_int (Z.of_nat npages * 4096) : mword 64) <> 0.
Proof.
  intros Hn Hb.
  rewrite moi64_unsigned.
  rewrite bv_wrap_small; [lia |].
  unfold bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. lia.
Qed.

(* entering the loop: page 0's va is va itself *)
Lemma mappages_va0 (va : mword 64) :
  add_vec va (mword_of_int (4096 * Z.of_nat 0)) = va.
Proof.
  apply bv_eq.
  rewrite add_vec64_unsigned. rewrite moi64_unsigned.
  change (4096 * Z.of_nat 0) with 0.
  replace (bv_wrap 64 0) with 0 by (vm_compute; reflexivity).
  rewrite Z.add_0_r.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.



(* ===================================================================== *)
(* pt_nodes: the number of allocated TABLE PAGES in a ptree (kalloc     *)
(* consumption during walks).  Level-indexed like ptree_own, since the  *)
(* function-typed [kids] field precludes structural tree recursion      *)
(* (rwx-kmap kvm-spec worklist (i).1).                                   *)
(* ===================================================================== *)
(* generic list helpers *)
Lemma sum_list_with_ext' {A} (f g : A -> nat) (l : list A) :
  (forall x, x ∈ l -> f x = g x) -> sum_list_with f l = sum_list_with g l.
Proof.
  induction l as [|a l IH]; [reflexivity|]. intro H. cbn.
  rewrite (H a); [| apply elem_of_cons; left; reflexivity].
  rewrite IH; [reflexivity|]. intros x Hx. apply H, elem_of_cons; right; exact Hx.
Qed.

Lemma sum_list_with_0 {A} (l : list A) : sum_list_with (fun _ => 0%nat) l = 0%nat.
Proof. induction l; [reflexivity | cbn; lia]. Qed.

Lemma sum_list_with_override {A} `{EqDecision A} (g : A -> nat) (l : list A) (x0 : A) (v : nat) :
  base.NoDup l -> x0 ∈ l ->
  (sum_list_with (fun k => if decide (k = x0) then v else g k) l + g x0)%nat
  = (sum_list_with g l + v)%nat.
Proof.
  induction l as [|a l IH]; intros Hnd Hin; [by apply elem_of_nil in Hin |].
  pose proof (@NoDup_cons_1_1 _ _ _ Hnd) as Ha. pose proof (@NoDup_cons_1_2 _ _ _ Hnd) as Hnd'. cbn.
  destruct (decide (a = x0)) as [->|Hne].
  - rewrite (sum_list_with_ext' (fun k => if decide (k = x0) then v else g k) g l).
    2:{ intros k Hk. destruct (decide (k = x0)) as [->|]; [exfalso; exact (Ha Hk) | reflexivity]. }
    lia.
  - apply elem_of_cons in Hin as [->|Hin]; [contradiction|].
    pose proof (IH Hnd' Hin) as HIH. lia.
Qed.

(* ===== the node count ===== *)
Fixpoint pt_nodes_lvl (lvl : nat) (t : ptree) {struct lvl} : nat :=
  S (match lvl with
     | O => 0%nat
     | S lvl' => sum_list_with (fun k => match pt_kids t (mword_of_int k) with
                                         | Some c => pt_nodes_lvl lvl' c
                                         | None => 0%nat end)
                               (seqZ 0 512)
     end).

Definition pt_nodes (t : ptree) : nat := pt_nodes_lvl 2 t.

Definition pt_kid_nodes (lvl : nat) (oc : option ptree) : nat :=
  match oc with Some c => pt_nodes_lvl lvl c | None => 0%nat end.

Lemma pt_nodes_lvl_S (lvl' : nat) (t : ptree) :
  pt_nodes_lvl (S lvl') t
  = S (sum_list_with (fun k => pt_kid_nodes lvl' (pt_kids t (mword_of_int k))) (seqZ 0 512)).
Proof. reflexivity. Qed.

Lemma pt_nodes_lvl_empty (lvl : nat) (b : mword 44) : pt_nodes_lvl lvl (pt_empty_node b) = 1%nat.
Proof.
  destruct lvl; [reflexivity|]. rewrite pt_nodes_lvl_S.
  rewrite (sum_list_with_ext' _ (fun _ => 0%nat)).
  - rewrite sum_list_with_0. reflexivity.
  - intros k _. reflexivity.
Qed.

Lemma pt_nodes_lvl_kids_ext (lvl : nat) (t t' : ptree) :
  (forall i : mword 9, pt_kids t i = pt_kids t' i) -> pt_nodes_lvl lvl t = pt_nodes_lvl lvl t'.
Proof.
  destruct lvl; [reflexivity|]. intro H. rewrite !pt_nodes_lvl_S. f_equal.
  apply sum_list_with_ext'. intros k _. unfold pt_kid_nodes. rewrite H. reflexivity.
Qed.

Lemma pt_nodes_lvl_kids_upd (lvl' : nat) (t : ptree) (i : mword 9) (c : option ptree) :
  (pt_nodes_lvl (S lvl') (pt_upd_kid t i c) + pt_kid_nodes lvl' (pt_kids t i))%nat
  = (pt_nodes_lvl (S lvl') t + pt_kid_nodes lvl' c)%nat.
Proof.
  rewrite !pt_nodes_lvl_S.
  pose (F := fun k : Z => pt_kid_nodes lvl' (pt_kids t (mword_of_int k))).
  assert (Hx0 : (0 <= bv_unsigned i < 512)%Z).
  { pose proof (bv_unsigned_in_range 9 i) as [Hlo Hhi].
    match type of Hhi with _ < ?m => assert (m = 512) as EM by (vm_compute; reflexivity) end.
    rewrite EM in Hhi. split; [exact Hlo | exact Hhi]. }
  rewrite (sum_list_with_ext'
             (fun k => pt_kid_nodes lvl' (pt_kids (pt_upd_kid t i c) (mword_of_int k)))
             (fun k => if decide (k = bv_unsigned i) then pt_kid_nodes lvl' c else F k)
             (seqZ 0 512)).
  2:{ intros k Hk. apply elem_of_seqZ in Hk.
      destruct (decide (mword_of_int k = i)) as [He | Hne].
      - assert (k = bv_unsigned i) as Hk0.
        { rewrite <- He. symmetry. apply pt_mword9_unsigned.
          change (0 + 512)%Z with 512%Z in Hk; exact Hk. }
        rewrite Hk0. rewrite pt_mword9_id.
        destruct (decide (bv_unsigned i = bv_unsigned i)) as [_ | Hcon];
          [| exfalso; apply Hcon; reflexivity].
        rewrite pt_upd_kid_same. reflexivity.
      - rewrite decide_False.
        + unfold F. rewrite (pt_upd_kid_other t i c (mword_of_int k) Hne). reflexivity.
        + intro Hk0. apply Hne. rewrite Hk0. apply pt_mword9_id. }
  pose proof (sum_list_with_override F (seqZ 0 512) (bv_unsigned i) (pt_kid_nodes lvl' c)
                (NoDup_seqZ 0 512)
                (proj2 (elem_of_seqZ 0 512 (bv_unsigned i))
                       ltac:(change (0 + 512)%Z with 512%Z; exact Hx0))) as Hov.
  assert (HFx0 : F (bv_unsigned i) = pt_kid_nodes lvl' (pt_kids t i)).
  { unfold F. rewrite pt_mword9_id. reflexivity. }
  rewrite HFx0 in Hov. rewrite !Nat.add_succ_l. rewrite Hov. reflexivity.
Qed.

Lemma pt_nodes_lvl_upd_kid_eq (lvl' : nat) (t : ptree) (i : mword 9) (c : option ptree) :
  pt_kid_nodes lvl' c = pt_kid_nodes lvl' (pt_kids t i) ->
  pt_nodes_lvl (S lvl') (pt_upd_kid t i c) = pt_nodes_lvl (S lvl') t.
Proof. intro H. pose proof (pt_nodes_lvl_kids_upd lvl' t i c). lia. Qed.

Lemma pt_nodes_lvl_upd_ent (lvl : nat) (t : ptree) (i : mword 9) (w : mword 64) :
  pt_nodes_lvl lvl (pt_upd_ent t i w) = pt_nodes_lvl lvl t.
Proof. apply pt_nodes_lvl_kids_ext. intro j. rewrite pt_upd_ent_kids. reflexivity. Qed.

(* fresh-slot graft: +1 at any level that reaches the slot *)
Lemma pt_nodes_lvl_graft (lvl' : nat) (t : ptree) (i : mword 9) (b : mword 44) :
  pt_kids t i = None ->
  pt_nodes_lvl (S lvl') (pt_graft t i b) = S (pt_nodes_lvl (S lvl') t).
Proof.
  intro H. unfold pt_graft.
  pose proof (pt_nodes_lvl_kids_upd lvl' (pt_upd_ent t i (pt_ptr_pte b)) i (Some (pt_empty_node b))) as Hm.
  rewrite pt_upd_ent_kids in Hm. rewrite H in Hm. cbn [pt_kid_nodes] in Hm.
  rewrite (pt_nodes_lvl_upd_ent (S lvl') t i (pt_ptr_pte b)) in Hm.
  cbn [pt_kid_nodes] in Hm. rewrite (pt_nodes_lvl_empty lvl' b) in Hm. lia.
Qed.

Lemma pt_nodes_graft2 (t : ptree) (vpn : mword 27) (b : mword 44) :
  pt_kids t (vpn_idx 2 vpn) = None ->
  pt_nodes (pt_graft2 t vpn b) = S (pt_nodes t).
Proof.
  intro H. unfold pt_nodes, pt_graft2.
  exact (pt_nodes_lvl_graft 1 t (vpn_idx 2 vpn) b H).
Qed.

Lemma pt_nodes_graft1 (t : ptree) (vpn : mword 27) (b : mword 44) (c1 : ptree) :
  pt_kids t (vpn_idx 2 vpn) = Some c1 ->
  pt_kids c1 (vpn_idx 1 vpn) = None ->
  pt_nodes (pt_graft1 t vpn b) = S (pt_nodes t).
Proof.
  intros H1 H0. unfold pt_nodes, pt_graft1. rewrite H1.
  pose proof (pt_nodes_lvl_kids_upd 1 t (vpn_idx 2 vpn) (Some (pt_graft1_kid c1 vpn b))) as Hm.
  rewrite H1 in Hm. cbn [pt_kid_nodes] in Hm.
  assert (Hgk : pt_nodes_lvl 1 (pt_graft1_kid c1 vpn b) = S (pt_nodes_lvl 1 c1))
    by exact (pt_nodes_lvl_graft 0 c1 (vpn_idx 1 vpn) b H0).
  rewrite Hgk in Hm. cbn [pt_kid_nodes] in Hm. lia.
Qed.

Lemma pt_nodes_set_leaf (t : ptree) (vpn : mword 27) (w : mword 64) :
  pt_nodes (ptree_set_leaf t vpn w) = pt_nodes t.
Proof.
  unfold pt_nodes, ptree_set_leaf.
  destruct (pt_kids t (vpn_idx 2 vpn)) as [c1|] eqn:H1; [| reflexivity].
  destruct (pt_kids c1 (vpn_idx 1 vpn)) as [c0|] eqn:H0; [| reflexivity].
  apply (pt_nodes_lvl_upd_kid_eq 1 t (vpn_idx 2 vpn)).
  rewrite H1. cbn [pt_kid_nodes].
  apply (pt_nodes_lvl_upd_kid_eq 0 c1 (vpn_idx 1 vpn)).
  rewrite H0. cbn [pt_kid_nodes].
  apply pt_nodes_lvl_upd_ent.
Qed.

(* ===================================================================== *)
(* §10 pt_missing: the SHARP upper bound on the table pages a run's walks *)
(*    would graft.  A run [vpn0, vpn0+npages) touches a CONTIGUOUS range   *)
(*    of l0-groups (18-bit index [vpn>>9]) and l1-groups (9-bit index      *)
(*    [vpn>>18]).  Each DISTINCT touched l0-group whose L0 node is absent   *)
(*    costs one L0 table; each distinct touched l1-group whose root kid is  *)
(*    absent costs one L1 table.  Counting per GROUP (not per page) both    *)
(*    DEDUPS the grafts (sharp -- 2*npages is uselessly loose) and stays    *)
(*    computable on kvm-scale runs (#groups ~ npages/512, not #pages).      *)
(*    The telescope [pt_missing_tel_gen] matches how [wp_mappages]'s loop   *)
(*    consumes it: growing then missing-of-the-tail <= missing-of-the-whole *)
(*    (with equality, hence sharp).                                         *)
(* ===================================================================== *)

(* [q] an l0-group index (0 <= q < 2^18): L1 index [q/512], L0 index [q mod 512].
   [1] iff the group's L0 node is absent in [t] (walk would graft it). *)
Definition l0_absent (t : ptree) (q : Z) : nat :=
  match pt_kids t (mword_of_int (q / 512) : mword 9) with
  | None => 1%nat
  | Some c1 => match pt_kids c1 (mword_of_int (q mod 512) : mword 9) with
               | None => 1%nat | Some _ => 0%nat end
  end.

(* [r] an l1-group index (0 <= r < 512): [1] iff the root kid at [r] is absent. *)
Definition l1_absent (t : ptree) (r : Z) : nat :=
  match pt_kids t (mword_of_int r : mword 9) with None => 1%nat | Some _ => 0%nat end.

Definition l0count (t : ptree) (lo hi : Z) : nat :=
  sum_list_with (l0_absent t) (seqZ lo (hi - lo + 1)).
Definition l1count (t : ptree) (lo hi : Z) : nat :=
  sum_list_with (l1_absent t) (seqZ lo (hi - lo + 1)).

Definition pt_missing (t : ptree) (vpn0 : mword 27) (npages : nat) : nat :=
  match npages with
  | O => 0%nat
  | S _ =>
      let lo := bv_unsigned vpn0 in
      let hi := (lo + Z.of_nat npages - 1)%Z in
      (l0count t (lo / 512) (hi / 512) + l1count t (lo / 262144) (hi / 262144))%nat
  end.

(* ------ generic sum-over-interval facts ------------------------------- *)

Lemma sum_seqZ_cons (f : Z -> nat) (lo hi : Z) :
  (lo <= hi)%Z ->
  sum_list_with f (seqZ lo (hi - lo + 1))
  = (f lo + sum_list_with f (seqZ (lo + 1) (hi - (lo + 1) + 1)))%nat.
Proof.
  intros H.
  rewrite (seqZ_cons lo (hi - lo + 1) ltac:(lia)). cbn [sum_list_with].
  replace (Z.succ lo) with (lo + 1)%Z by lia.
  replace (Z.pred (hi - lo + 1)) with (hi - (lo + 1) + 1)%Z by lia.
  reflexivity.
Qed.

(* Front point [lo] flips to [0] in [f']; [f'] agrees with [f] above [lo].
   Whether the tail sum starts at [lo] or [lo+1], [f lo] fits under the whole. *)
Lemma countA_le (f f' : Z -> nat) (lo hi lo' : Z) :
  (lo <= hi)%Z -> (lo' = lo \/ lo' = lo + 1)%Z ->
  f' lo = 0%nat ->
  (forall z, (lo + 1 <= z <= hi)%Z -> f' z = f z) ->
  (f lo + sum_list_with f' (seqZ lo' (hi - lo' + 1))
   <= sum_list_with f (seqZ lo (hi - lo + 1)))%nat.
Proof.
  intros Hle Hlo' Hf'0 Hagree.
  rewrite (sum_seqZ_cons f lo hi Hle).
  assert (Htail : sum_list_with f' (seqZ (lo + 1) (hi - (lo + 1) + 1))
                  = sum_list_with f (seqZ (lo + 1) (hi - (lo + 1) + 1))).
  { apply sum_list_with_ext'. intros z Hz. apply elem_of_seqZ in Hz. apply Hagree. lia. }
  destruct Hlo' as [-> | ->].
  - rewrite (sum_seqZ_cons f' lo hi Hle). rewrite Hf'0. rewrite Htail. lia.
  - rewrite Htail. lia.
Qed.

Lemma div_succ_between (a d : Z) :
  (0 < d)%Z -> ((a + 1) / d = a / d \/ (a + 1) / d = a / d + 1)%Z.
Proof.
  intros Hd.
  pose proof (Z.div_le_mono a (a + 1) d Hd ltac:(lia)) as Hlo.
  assert (Hhi : ((a + 1) / d <= a / d + 1)%Z).
  { pose proof (Z.div_le_mono (a + 1) (a + 1 * d) d Hd ltac:(lia)) as H.
    rewrite (Z.div_add a 1 d ltac:(lia)) in H. lia. }
  lia.
Qed.

Lemma l0count_single (t : ptree) (a : Z) : l0count t a a = l0_absent t a.
Proof.
  unfold l0count. replace (a - a + 1)%Z with 1%Z by lia.
  rewrite (seqZ_cons a 1 ltac:(lia)). rewrite (seqZ_nil (Z.succ a) (Z.pred 1) ltac:(lia)). cbn [sum_list_with]. lia.
Qed.

Lemma l1count_single (t : ptree) (a : Z) : l1count t a a = l1_absent t a.
Proof.
  unfold l1count. replace (a - a + 1)%Z with 1%Z by lia.
  rewrite (seqZ_cons a 1 ltac:(lia)). rewrite (seqZ_nil (Z.succ a) (Z.pred 1) ltac:(lia)). cbn [sum_list_with]. lia.
Qed.

(* ------ vpn walk-index <-> group-index arithmetic --------------------- *)

Lemma vpn_range (vpn : mword 27) : (0 <= bv_unsigned vpn < 134217728)%Z.
Proof.
  pose proof (bv_unsigned_in_range 27 vpn) as [Hlo Hhi].
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 27) = 134217728)
    by (vm_compute; reflexivity).
  rewrite Hm in Hhi. split; [exact Hlo | exact Hhi].
Qed.

Lemma vpn_idx2_div (vpn : mword 27) :
  bv_unsigned (vpn_idx 2 vpn) = (bv_unsigned vpn / 262144)%Z.
Proof.
  pose proof (vpn_range vpn) as [Hlo Hhi].
  cbn [vpn_idx]. rewrite pt_sub27_26_18.
  rewrite (Z.shiftr_div_pow2 _ 18 ltac:(lia)). change (2 ^ 18)%Z with 262144%Z. change (2 ^ 9)%Z with 512%Z.
  rewrite Z.mod_small; [reflexivity |].
  split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ].
Qed.

Lemma vpn_idx1_mod (vpn : mword 27) :
  bv_unsigned (vpn_idx 1 vpn) = ((bv_unsigned vpn / 512) mod 512)%Z.
Proof.
  cbn [vpn_idx]. rewrite pt_sub27_17_9.
  rewrite (Z.shiftr_div_pow2 _ 9 ltac:(lia)). change (2 ^ 9)%Z with 512%Z. reflexivity.
Qed.

(* the l1-group index of [vpn] is [bv/262144]; the l0-group index is [bv/512] *)
Lemma group_i2 (vpn : mword 27) :
  (mword_of_int (bv_unsigned vpn / 262144) : mword 9) = vpn_idx 2 vpn.
Proof. rewrite <- vpn_idx2_div. apply pt_mword9_id. Qed.

Lemma group_i2_of_q0 (vpn : mword 27) :
  (mword_of_int ((bv_unsigned vpn / 512) / 512) : mword 9) = vpn_idx 2 vpn.
Proof.
  rewrite (Z.div_div (bv_unsigned vpn) 512 512 ltac:(lia) ltac:(lia)).
  change (512 * 512)%Z with 262144%Z. apply group_i2.
Qed.

Lemma group_i1_of_q0 (vpn : mword 27) :
  (mword_of_int ((bv_unsigned vpn / 512) mod 512) : mword 9) = vpn_idx 1 vpn.
Proof. rewrite <- vpn_idx1_mod. apply pt_mword9_id. Qed.

(* ------ pt_missing is a function of [bv_unsigned vpn0] ----------------- *)

Lemma pt_missing_bv_eq (t : ptree) (v v' : mword 27) (np : nat) :
  bv_unsigned v = bv_unsigned v' -> pt_missing t v np = pt_missing t v' np.
Proof.
  intros Hbv. destruct np as [| n]; [reflexivity |]. unfold pt_missing. rewrite Hbv. reflexivity.
Qed.

Lemma pt_missing_0 (t : ptree) (v : mword 27) : pt_missing t v 0 = 0%nat.
Proof. reflexivity. Qed.

(* ------ set_leaf preserves absent-ness (only ENTS change) ------------- *)

Lemma l0_absent_set_leaf (t : ptree) (vpn : mword 27) (w : mword 64) (q : Z) :
  l0_absent (ptree_set_leaf t vpn w) q = l0_absent t q.
Proof.
  unfold l0_absent, ptree_set_leaf.
  destruct (pt_kids t (vpn_idx 2 vpn)) as [c1|] eqn:H1; [| reflexivity].
  destruct (pt_kids c1 (vpn_idx 1 vpn)) as [c0|] eqn:H0; [| reflexivity].
  destruct (decide (mword_of_int (q / 512) = vpn_idx 2 vpn)) as [E2 | N2].
  - rewrite E2. rewrite pt_upd_kid_same. rewrite H1.
    destruct (decide (mword_of_int (q mod 512) = vpn_idx 1 vpn)) as [E1 | N1].
    + rewrite E1. rewrite pt_upd_kid_same. rewrite H0. reflexivity.
    + rewrite (pt_upd_kid_other _ _ _ _ N1). reflexivity.
  - rewrite (pt_upd_kid_other _ _ _ _ N2). reflexivity.
Qed.

Lemma l1_absent_set_leaf (t : ptree) (vpn : mword 27) (w : mword 64) (r : Z) :
  l1_absent (ptree_set_leaf t vpn w) r = l1_absent t r.
Proof.
  unfold l1_absent, ptree_set_leaf.
  destruct (pt_kids t (vpn_idx 2 vpn)) as [c1|] eqn:H1; [| reflexivity].
  destruct (pt_kids c1 (vpn_idx 1 vpn)) as [c0|] eqn:H0; [| reflexivity].
  destruct (decide (mword_of_int r = vpn_idx 2 vpn)) as [E2 | N2].
  - rewrite E2. rewrite pt_upd_kid_same. rewrite H1. reflexivity.
  - rewrite (pt_upd_kid_other _ _ _ _ N2). reflexivity.
Qed.

Lemma pt_missing_set_leaf (t : ptree) (vpn : mword 27) (w : mword 64) (v0 : mword 27) (np : nat) :
  pt_missing (ptree_set_leaf t vpn w) v0 np = pt_missing t v0 np.
Proof.
  destruct np as [| n]; [reflexivity |]. unfold pt_missing, l0count, l1count.
  f_equal; apply sum_list_with_ext'; intros x _;
    [ apply l0_absent_set_leaf | apply l1_absent_set_leaf ].
Qed.

(* ===================================================================== *)
(* §11 The TELESCOPE: growing the tree along [vpn]'s path (as walk does)   *)
(*    then taking the missing count of the [n]-page TAIL is bounded by the *)
(*    missing count of the whole [S n]-page run.  Stated generically over  *)
(*    the four "flip" facts a graft along [vpn]'s path induces, so each     *)
(*    walk arm supplies the flips its concrete graft satisfies.            *)
(* ===================================================================== *)

Lemma pt_missing_tel_gen (t t' : ptree) (vpn : mword 27) (n : nat) :
  (bv_unsigned vpn + Z.of_nat n + 1 <= 134217728)%Z ->
  l0_absent t' (bv_unsigned vpn / 512) = 0%nat ->
  (forall q, (0 <= q < 262144)%Z -> q <> (bv_unsigned vpn / 512)%Z ->
             l0_absent t' q = l0_absent t q) ->
  l1_absent t' (bv_unsigned vpn / 262144) = 0%nat ->
  (forall r, (0 <= r < 512)%Z -> r <> (bv_unsigned vpn / 262144)%Z ->
             l1_absent t' r = l1_absent t r) ->
  ((l0_absent t (bv_unsigned vpn / 512) + l1_absent t (bv_unsigned vpn / 262144))
     + pt_missing t' (add_vec_int vpn 1) n <= pt_missing t vpn (S n))%nat.
Proof.
  intros Hnw Hl0z Hl0o Hl1z Hl1o.
  pose proof (vpn_range vpn) as [Hvlo Hvhi].
  set (lo := bv_unsigned vpn) in *.
  set (q0 := (lo / 512)%Z). set (r0 := (lo / 262144)%Z).
  (* pt_missing t vpn (S n) : hi = lo + n *)
  assert (HSn : Z.of_nat (S n) = (Z.of_nat n + 1)%Z) by lia.
  assert (Hmt : pt_missing t vpn (S n)
                = (l0count t q0 ((lo + Z.of_nat n) / 512)
                   + l1count t r0 ((lo + Z.of_nat n) / 262144))%nat).
  { unfold pt_missing. rewrite HSn. fold lo. unfold q0, r0.
    replace (lo + (Z.of_nat n + 1) - 1)%Z with (lo + Z.of_nat n)%Z by lia. reflexivity. }
  rewrite Hmt.
  (* bounds *)
  assert (Hq0pos : (0 <= q0)%Z) by (unfold q0; apply Z.div_pos; lia).
  assert (Hr0pos : (0 <= r0)%Z) by (unfold r0; apply Z.div_pos; lia).
  assert (Hq0hi : (q0 <= (lo + Z.of_nat n) / 512)%Z)
    by (unfold q0; apply Z.div_le_mono; lia).
  assert (Hr0hi : (r0 <= (lo + Z.of_nat n) / 262144)%Z)
    by (unfold r0; apply Z.div_le_mono; lia).
  assert (Hhi512 : ((lo + Z.of_nat n) / 512 < 262144)%Z)
    by (apply Z.div_lt_upper_bound; lia).
  assert (Hhi262 : ((lo + Z.of_nat n) / 262144 < 512)%Z)
    by (apply Z.div_lt_upper_bound; lia).
  (* the l0 inequality *)
  assert (HL0 : (l0_absent t q0 + l0count t' ((lo + 1) / 512) ((lo + Z.of_nat n) / 512)
                 <= l0count t q0 ((lo + Z.of_nat n) / 512))%nat).
  { unfold l0count.
    apply (countA_le (l0_absent t) (l0_absent t') q0 ((lo + Z.of_nat n) / 512) ((lo + 1) / 512)).
    - exact Hq0hi.
    - unfold q0. apply div_succ_between; lia.
    - exact Hl0z.
    - intros z Hz. apply Hl0o; [ lia | lia ]. }
  (* the l1 inequality *)
  assert (HL1 : (l1_absent t r0 + l1count t' ((lo + 1) / 262144) ((lo + Z.of_nat n) / 262144)
                 <= l1count t r0 ((lo + Z.of_nat n) / 262144))%nat).
  { unfold l1count.
    apply (countA_le (l1_absent t) (l1_absent t') r0 ((lo + Z.of_nat n) / 262144) ((lo + 1) / 262144)).
    - exact Hr0hi.
    - unfold r0. apply div_succ_between; lia.
    - exact Hl1z.
    - intros z Hz. apply Hl1o; [ lia | lia ]. }
  (* pt_missing t' (add_vec_int vpn 1) n *)
  destruct n as [| n'].
  - (* single page: tail empty *)
    change (pt_missing t' (add_vec_int vpn 1) 0) with 0%nat.
    replace (lo + Z.of_nat 0)%Z with lo by lia.
    replace (lo / 512)%Z with q0 by reflexivity.
    replace (lo / 262144)%Z with r0 by reflexivity.
    rewrite (l0count_single t q0). rewrite (l1count_single t r0). lia.
  - (* n = S n' >= 1: no wrap, tail run starts at lo+1 *)
    assert (Hbv1 : bv_unsigned (add_vec_int vpn 1) = (lo + 1)%Z).
    { rewrite (pb_add_vec_int27_wrap vpn 1 ltac:(lia)). unfold lo.
      rewrite bv_wrap_small; [ reflexivity |].
      unfold bv_modulus. change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 27))%Z with 134217728%Z. lia. }
    assert (Hmt' : pt_missing t' (add_vec_int vpn 1) (S n')
                   = (l0count t' ((lo + 1) / 512) ((lo + Z.of_nat (S n')) / 512)
                      + l1count t' ((lo + 1) / 262144) ((lo + Z.of_nat (S n')) / 262144))%nat).
    { unfold pt_missing. rewrite Hbv1.
      replace (lo + 1 + Z.of_nat (S n') - 1)%Z with (lo + Z.of_nat (S n'))%Z by lia. reflexivity. }
    rewrite Hmt'. lia.
Qed.

(* ===================================================================== *)
(* §12 Per-arm flip facts: the grafts walk performs along [vpn]'s path.   *)
(*    graft2 adds an empty L1 node (flips the L1 group present, leaves     *)
(*    every L0 group's absent-ness unchanged); graft1 adds an L0 node      *)
(*    (flips [vpn]'s own L0 group present, leaves others unchanged).       *)
(* ===================================================================== *)

(* --- q/512 = i2, q mod 512 = i1 comparison bridges (0 <= q < 2^18) --- *)
Lemma q_i2_iff (vpn : mword 27) (q : Z) :
  (0 <= q < 262144)%Z ->
  (mword_of_int (q / 512) : mword 9) = vpn_idx 2 vpn <-> (q / 512 = bv_unsigned vpn / 262144)%Z.
Proof.
  intros Hq. split.
  - intros E. apply (f_equal bv_unsigned) in E.
    rewrite (pt_mword9_unsigned (q / 512) ltac:(split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia])) in E.
    rewrite vpn_idx2_div in E. exact E.
  - intros E. rewrite E. apply group_i2.
Qed.

Lemma q_i1_iff (vpn : mword 27) (q : Z) :
  (0 <= q < 262144)%Z ->
  (mword_of_int (q mod 512) : mword 9) = vpn_idx 1 vpn <-> (q mod 512 = (bv_unsigned vpn / 512) mod 512)%Z.
Proof.
  intros Hq. split.
  - intros E. apply (f_equal bv_unsigned) in E.
    rewrite (pt_mword9_unsigned (q mod 512) ltac:(pose proof (Z.mod_pos_bound q 512 ltac:(lia)); lia)) in E.
    rewrite vpn_idx1_mod in E. exact E.
  - intros E. rewrite E. apply group_i1_of_q0.
Qed.

(* graft2: given the root kid at [vpn]'s L1 slot is absent. *)
Lemma l0_absent_graft2 (t : ptree) (vpn : mword 27) (b : mword 44) (q : Z) :
  pt_kids t (vpn_idx 2 vpn) = None ->
  l0_absent (pt_graft2 t vpn b) q = l0_absent t q.
Proof.
  intros Hnone. unfold l0_absent.
  destruct (decide (mword_of_int (q / 512) = vpn_idx 2 vpn)) as [E2 | N2].
  - rewrite E2. rewrite pt_graft2_kid. rewrite Hnone. reflexivity.
  - rewrite (pt_graft2_kids_other t vpn b _ N2). reflexivity.
Qed.

Lemma l1_absent_graft2_z (t : ptree) (vpn : mword 27) (b : mword 44) :
  l1_absent (pt_graft2 t vpn b) (bv_unsigned vpn / 262144) = 0%nat.
Proof.
  unfold l1_absent. rewrite group_i2. rewrite pt_graft2_kid. reflexivity.
Qed.

Lemma l1_absent_graft2_o (t : ptree) (vpn : mword 27) (b : mword 44) (r : Z) :
  (0 <= r < 512)%Z -> r <> (bv_unsigned vpn / 262144)%Z ->
  l1_absent (pt_graft2 t vpn b) r = l1_absent t r.
Proof.
  intros Hr Hne. unfold l1_absent.
  assert (N2 : (mword_of_int r : mword 9) <> vpn_idx 2 vpn).
  { intro E. apply (f_equal bv_unsigned) in E.
    rewrite (pt_mword9_unsigned r ltac:(lia)) in E. rewrite vpn_idx2_div in E. lia. }
  rewrite (pt_graft2_kids_other t vpn b _ N2). reflexivity.
Qed.

(* graft1: given the root kid [c1] present and its L0 slot at [vpn] absent. *)
Lemma l0_absent_graft1_z (t c1 : ptree) (vpn : mword 27) (b : mword 44) :
  pt_kids t (vpn_idx 2 vpn) = Some c1 ->
  l0_absent (pt_graft1 t vpn b) (bv_unsigned vpn / 512) = 0%nat.
Proof.
  intros Hk2. unfold l0_absent.
  rewrite group_i2_of_q0. rewrite (pt_graft1_kid_at t c1 vpn b Hk2).
  rewrite group_i1_of_q0. rewrite pt_graft1_kid_kid. reflexivity.
Qed.

Lemma l0_absent_graft1_o (t c1 : ptree) (vpn : mword 27) (b : mword 44) (q : Z) :
  pt_kids t (vpn_idx 2 vpn) = Some c1 ->
  (0 <= q < 262144)%Z -> q <> (bv_unsigned vpn / 512)%Z ->
  l0_absent (pt_graft1 t vpn b) q = l0_absent t q.
Proof.
  intros Hk2 Hq Hne. unfold l0_absent.
  destruct (decide (mword_of_int (q / 512) = vpn_idx 2 vpn)) as [E2 | N2].
  - (* same L1 group as [vpn]: must differ in the L0 index, else q = q0 *)
    assert (Hq2 : (q / 512 = bv_unsigned vpn / 262144)%Z) by (apply (q_i2_iff vpn q Hq); exact E2).
    assert (N1 : (mword_of_int (q mod 512) : mword 9) <> vpn_idx 1 vpn).
    { intro E1. apply (q_i1_iff vpn q Hq) in E1. apply Hne.
      pose proof (Z.div_div (bv_unsigned vpn) 512 512 ltac:(lia) ltac:(lia)) as Hdd.
      change (512 * 512)%Z with 262144%Z in Hdd.
      rewrite <- Hdd in Hq2.
      pose proof (Z.div_mod q 512 ltac:(lia)) as Dq.
      pose proof (Z.div_mod (bv_unsigned vpn / 512) 512 ltac:(lia)) as Dv.
      lia. }
    rewrite E2. rewrite (pt_graft1_kid_at t c1 vpn b Hk2). rewrite Hk2.
    rewrite (pt_graft1_kid_kids_other c1 vpn b _ N1). reflexivity.
  - rewrite (pt_graft1_kids_other t vpn b _ N2). reflexivity.
Qed.

Lemma l1_absent_graft1 (t : ptree) (vpn : mword 27) (b : mword 44) (r : Z) :
  l1_absent (pt_graft1 t vpn b) r = l1_absent t r.
Proof.
  unfold l1_absent, pt_graft1.
  destruct (pt_kids t (vpn_idx 2 vpn)) as [c1|] eqn:Hk2; [| reflexivity].
  destruct (decide (mword_of_int r = vpn_idx 2 vpn)) as [E | N].
  - rewrite E. rewrite pt_upd_kid_same. rewrite Hk2. reflexivity.
  - rewrite (pt_upd_kid_other _ _ _ _ N). reflexivity.
Qed.

(* ------ the three walk-arm telescope corollaries ---------------------- *)

(* arm g=0: both nodes present -- the run's tail is a sub-run (no graft) *)
Lemma pt_missing_tel_present (t : ptree) (vpn : mword 27) (c1 c0 : ptree) (n : nat) :
  (bv_unsigned vpn + Z.of_nat n + 1 <= 134217728)%Z ->
  pt_kids t (vpn_idx 2 vpn) = Some c1 ->
  pt_kids c1 (vpn_idx 1 vpn) = Some c0 ->
  (0 + pt_missing t (add_vec_int vpn 1) n <= pt_missing t vpn (S n))%nat.
Proof.
  intros Hnw Hk2 Hk1.
  assert (Hl0z : l0_absent t (bv_unsigned vpn / 512) = 0%nat).
  { unfold l0_absent. rewrite group_i2_of_q0. rewrite Hk2.
    rewrite group_i1_of_q0. rewrite Hk1. reflexivity. }
  assert (Hl1z : l1_absent t (bv_unsigned vpn / 262144) = 0%nat).
  { unfold l1_absent. rewrite group_i2. rewrite Hk2. reflexivity. }
  pose proof (pt_missing_tel_gen t t vpn n Hnw Hl0z (fun q _ _ => eq_refl) Hl1z (fun r _ _ => eq_refl)) as H.
  rewrite Hl0z Hl1z in H. change (0 + 0)%nat with 0%nat in H. exact H.
Qed.

(* arm g=1: root kid present, L0 node absent -- graft1 *)
Lemma pt_missing_tel_graft1 (t c1 : ptree) (vpn : mword 27) (b : mword 44) (n : nat) :
  (bv_unsigned vpn + Z.of_nat n + 1 <= 134217728)%Z ->
  pt_kids t (vpn_idx 2 vpn) = Some c1 ->
  pt_kids c1 (vpn_idx 1 vpn) = None ->
  (1 + pt_missing (pt_graft1 t vpn b) (add_vec_int vpn 1) n <= pt_missing t vpn (S n))%nat.
Proof.
  intros Hnw Hk2 Hk1.
  assert (Hl0t : l0_absent t (bv_unsigned vpn / 512) = 1%nat).
  { unfold l0_absent. rewrite group_i2_of_q0. rewrite Hk2. rewrite group_i1_of_q0. rewrite Hk1. reflexivity. }
  assert (Hl1t : l1_absent t (bv_unsigned vpn / 262144) = 0%nat).
  { unfold l1_absent. rewrite group_i2. rewrite Hk2. reflexivity. }
  pose proof (pt_missing_tel_gen t (pt_graft1 t vpn b) vpn n Hnw
                (l0_absent_graft1_z t c1 vpn b Hk2)
                (fun q Hq Hne => l0_absent_graft1_o t c1 vpn b q Hk2 Hq Hne)
                ltac:(rewrite l1_absent_graft1; exact Hl1t)
                (fun r _ _ => l1_absent_graft1 t vpn b r)) as H.
  rewrite Hl0t Hl1t in H. change (1 + 0)%nat with 1%nat in H. exact H.
Qed.

(* arm g=2: root kid absent -- graft2 (empty L1) then graft1 (L0) *)
Lemma pt_missing_tel_graft2 (t : ptree) (vpn : mword 27) (b1 b0 : mword 44) (n : nat) :
  (bv_unsigned vpn + Z.of_nat n + 1 <= 134217728)%Z ->
  pt_kids t (vpn_idx 2 vpn) = None ->
  (2 + pt_missing (pt_graft1 (pt_graft2 t vpn b1) vpn b0) (add_vec_int vpn 1) n
     <= pt_missing t vpn (S n))%nat.
Proof.
  intros Hnw Hnone.
  set (t2 := pt_graft2 t vpn b1).
  set (t' := pt_graft1 t2 vpn b0).
  assert (Hk2' : pt_kids t2 (vpn_idx 2 vpn) = Some (pt_empty_node b1)) by apply pt_graft2_kid.
  (* coefficients in [t]: both nodes absent *)
  assert (Hl0t : l0_absent t (bv_unsigned vpn / 512) = 1%nat).
  { unfold l0_absent. rewrite group_i2_of_q0. rewrite Hnone. reflexivity. }
  assert (Hl1t : l1_absent t (bv_unsigned vpn / 262144) = 1%nat).
  { unfold l1_absent. rewrite group_i2. rewrite Hnone. reflexivity. }
  (* the four combined flips of t' = graft1 (graft2 t) relative to t *)
  assert (F0z : l0_absent t' (bv_unsigned vpn / 512) = 0%nat)
    by exact (l0_absent_graft1_z t2 (pt_empty_node b1) vpn b0 Hk2').
  assert (F0o : forall q, (0 <= q < 262144)%Z -> q <> (bv_unsigned vpn / 512)%Z ->
                          l0_absent t' q = l0_absent t q).
  { intros q Hq Hne. unfold t'.
    rewrite (l0_absent_graft1_o t2 (pt_empty_node b1) vpn b0 q Hk2' Hq Hne).
    exact (l0_absent_graft2 t vpn b1 q Hnone). }
  assert (F1z : l1_absent t' (bv_unsigned vpn / 262144) = 0%nat).
  { unfold t'. rewrite l1_absent_graft1. exact (l1_absent_graft2_z t vpn b1). }
  assert (F1o : forall r, (0 <= r < 512)%Z -> r <> (bv_unsigned vpn / 262144)%Z ->
                          l1_absent t' r = l1_absent t r).
  { intros r Hr Hne. unfold t'. rewrite l1_absent_graft1.
    exact (l1_absent_graft2_o t vpn b1 r Hr Hne). }
  pose proof (pt_missing_tel_gen t t' vpn n Hnw F0z F0o F1z F1o) as H.
  rewrite Hl0t Hl1t in H. unfold t' in H. change (1 + 1)%nat with 2%nat in H. exact H.
Qed.

(* ===================================================================== *)
(* §13 ptree_offpath_eq: the KID-level off-path agreement walk exports so  *)
(*    mappages can discharge the telescope's flip hypotheses.  walk edits  *)
(*    only vpn's path, so the l2 kids off [vpn_idx 2] are preserved, and    *)
(*    within vpn's l1 kid the kids off [vpn_idx 1] are preserved (a freshly *)
(*    grafted l1 kid has all-None other slots).  The DERIVATION lemmas turn *)
(*    this + walk's present-facts into [pt_missing_tel_gen]'s two off-path  *)
(*    flip hypotheses.                                                      *)
(* ===================================================================== *)

Definition ptree_offpath_eq (vpn : mword 27) (t t' : ptree) : Prop :=
  (forall j, j <> vpn_idx 2 vpn -> pt_kids t' j = pt_kids t j) /\
  (forall c c', pt_kids t (vpn_idx 2 vpn) = Some c ->
                pt_kids t' (vpn_idx 2 vpn) = Some c' ->
                forall j, j <> vpn_idx 1 vpn -> pt_kids c' j = pt_kids c j) /\
  (forall c', pt_kids t (vpn_idx 2 vpn) = None ->
              pt_kids t' (vpn_idx 2 vpn) = Some c' ->
              forall j, j <> vpn_idx 1 vpn -> pt_kids c' j = None).

Lemma ptree_offpath_eq_refl (vpn : mword 27) (t : ptree) : ptree_offpath_eq vpn t t.
Proof.
  split; [intros; reflexivity | split].
  - intros c c' Hc Hc' j _. rewrite Hc' in Hc. injection Hc as ->. reflexivity.
  - intros c' Hnone Hsome. rewrite Hnone in Hsome. discriminate.
Qed.

(* ------ the LEVEL-GENERIC threading predicate --------------------------
   walk descends levels 2,1,0; [ptree_offpath_eq] only constrains the l2
   kids (level 2) and vpn's l1 kid's kids (level 1).  The zipper's restore,
   built up as walk descends, plugs a rebuilt level-[L] subtree back in.
   The hypothesis it needs of that subtree is level-dependent: at level 2 it
   is the full [ptree_offpath_eq]; at level 1 the single-level kid agreement
   off [vpn_idx 1]; at level 0 there is nothing to constrain (True). *)
Definition ptree_offpath_eq_lvl (L : nat) (vpn : mword 27) (cur curf : ptree) : Prop :=
  match L with
  | O => True
  | S O => forall j, j <> vpn_idx 1 vpn -> pt_kids curf j = pt_kids cur j
  | S (S _) => ptree_offpath_eq vpn cur curf
  end.

Lemma ptree_offpath_eq_lvl_refl (L : nat) (vpn : mword 27) (cur : ptree) :
  ptree_offpath_eq_lvl L vpn cur cur.
Proof.
  destruct L as [| [| l]]; cbn.
  - exact I.
  - intros; reflexivity.
  - apply ptree_offpath_eq_refl.
Qed.

Lemma ptree_offpath_eq_lvl_2 (vpn : mword 27) (cur curf : ptree) :
  ptree_offpath_eq_lvl 2 vpn cur curf = ptree_offpath_eq vpn cur curf.
Proof. reflexivity. Qed.

(* the zipper's descend wrap: plugging [curf] under [vpn_idx (S l)]'s (present)
   kid slot preserves off-path agreement one level up. *)
Lemma ptree_offpath_eq_lvl_upd_kid (l : nat) (vpn : mword 27) (cur curf c : ptree) :
  (S l <= 2)%nat ->
  pt_kids cur (vpn_idx (S l) vpn) = Some c ->
  ptree_offpath_eq_lvl l vpn c curf ->
  ptree_offpath_eq_lvl (S l) vpn cur (pt_upd_kid cur (vpn_idx (S l) vpn) (Some curf)).
Proof.
  intros HL Hk Hoff. destruct l as [| [| l]]; [| | exfalso; lia].
  - (* S l = 1 *)
    cbn. intros j Hj. apply (pt_upd_kid_other cur (vpn_idx 1 vpn) (Some curf) j Hj).
  - (* S l = 2 *)
    cbn in Hoff |- *. split; [| split].
    + intros j Hj. apply (pt_upd_kid_other cur (vpn_idx 2 vpn) (Some curf) j Hj).
    + intros c0 c' Hc0 Hc'. rewrite pt_upd_kid_same in Hc'. injection Hc' as <-.
      rewrite Hk in Hc0. injection Hc0 as <-. exact Hoff.
    + intros c' Hnone. rewrite Hk in Hnone. discriminate.
Qed.

(* the zipper's graft wrap: grafting a fresh empty page under [vpn_idx (S l)]'s
   (absent) slot then descending preserves off-path agreement. *)
Lemma ptree_offpath_eq_lvl_graft (l : nat) (vpn : mword 27) (cur curf : ptree) (b : mword 44) :
  (S l <= 2)%nat ->
  pt_kids cur (vpn_idx (S l) vpn) = None ->
  ptree_offpath_eq_lvl l vpn (pt_empty_node b) curf ->
  ptree_offpath_eq_lvl (S l) vpn cur
    (pt_upd_kid (pt_graft cur (vpn_idx (S l) vpn) b) (vpn_idx (S l) vpn) (Some curf)).
Proof.
  intros HL Hk Hoff. destruct l as [| [| l]]; [| | exfalso; lia].
  - (* S l = 1 *)
    intros j Hj.
    rewrite (pt_upd_kid_other (pt_graft cur (vpn_idx 1 vpn) b) (vpn_idx 1 vpn) (Some curf) j Hj).
    apply (pt_graft_kids_other cur (vpn_idx 1 vpn) j b Hj).
  - (* S l = 2 *)
    unfold ptree_offpath_eq_lvl in Hoff. split; [| split].
    + intros j Hj. rewrite (pt_upd_kid_other (pt_graft cur (vpn_idx 2 vpn) b) (vpn_idx 2 vpn) (Some curf) j Hj).
      apply (pt_graft_kids_other cur (vpn_idx 2 vpn) j b Hj).
    + intros c0 c' Hc0. rewrite Hk in Hc0. discriminate.
    + intros c' _ Hc'. rewrite pt_upd_kid_same in Hc'. injection Hc' as <-.
      intros j Hj. rewrite (Hoff j Hj). reflexivity.
Qed.

(* ------ derivation: offpath + present-facts => the tel_gen flips -------- *)

Lemma offpath_l1_flip (vpn : mword 27) (t t' : ptree) :
  ptree_offpath_eq vpn t t' ->
  forall r, (0 <= r < 512)%Z -> r <> (bv_unsigned vpn / 262144)%Z ->
    l1_absent t' r = l1_absent t r.
Proof.
  intros (Hi & _ & _) r Hr Hne. unfold l1_absent.
  assert (N2 : (mword_of_int r : mword 9) <> vpn_idx 2 vpn).
  { intro E. apply (f_equal bv_unsigned) in E.
    rewrite (pt_mword9_unsigned r ltac:(lia)) in E. rewrite vpn_idx2_div in E. lia. }
  rewrite (Hi (mword_of_int r) N2). reflexivity.
Qed.

Lemma offpath_l0_flip (vpn : mword 27) (t t' : ptree) :
  ptree_offpath_eq vpn t t' ->
  l0_absent t' (bv_unsigned vpn / 512) = 0%nat ->
  forall q, (0 <= q < 262144)%Z -> q <> (bv_unsigned vpn / 512)%Z ->
    l0_absent t' q = l0_absent t q.
Proof.
  intros (Hi & Hii & Hiii) Hz q Hq Hne.
  (* the present-fact gives t' a full l1 kid at [vpn_idx 2 vpn] *)
  assert (Hpres : exists c1', pt_kids t' (vpn_idx 2 vpn) = Some c1').
  { revert Hz. unfold l0_absent. rewrite group_i2_of_q0.
    destruct (pt_kids t' (vpn_idx 2 vpn)) as [c1'|] eqn:Ht'; [| discriminate].
    intros _. exists c1'. reflexivity. }
  destruct Hpres as [c1' Ht'2].
  unfold l0_absent.
  destruct (decide (mword_of_int (q / 512) = vpn_idx 2 vpn)) as [E2 | N2].
  - (* same l1 group as vpn: l0 index differs from vpn's *)
    assert (Hq2 : (q / 512 = bv_unsigned vpn / 262144)%Z) by (apply (q_i2_iff vpn q Hq); exact E2).
    assert (N1 : (mword_of_int (q mod 512) : mword 9) <> vpn_idx 1 vpn).
    { intro E1. apply (q_i1_iff vpn q Hq) in E1. apply Hne.
      pose proof (Z.div_div (bv_unsigned vpn) 512 512 ltac:(lia) ltac:(lia)) as Hdd.
      change (512 * 512)%Z with 262144%Z in Hdd.
      rewrite <- Hdd in Hq2.
      pose proof (Z.div_mod q 512 ltac:(lia)) as Dq.
      pose proof (Z.div_mod (bv_unsigned vpn / 512) 512 ltac:(lia)) as Dv.
      lia. }
    rewrite E2. rewrite Ht'2.
    destruct (pt_kids t (vpn_idx 2 vpn)) as [c1|] eqn:Ht2.
    + rewrite (Hii c1 c1' eq_refl Ht'2 (mword_of_int (q mod 512)) N1). reflexivity.
    + rewrite (Hiii c1' eq_refl Ht'2 (mword_of_int (q mod 512)) N1). reflexivity.
  - rewrite (Hi (mword_of_int (q / 512)) N2). reflexivity.
Qed.

(* ------ extract the present-facts from walk's [ptree_level0] output ----- *)

Lemma ptree_level0_l1_absent (t : ptree) (vpn : mword 27) (p2 p1 w0 : mword 64) :
  ptree_level0 t vpn p2 p1 w0 -> l1_absent t (bv_unsigned vpn / 262144) = 0%nat.
Proof.
  intros (c1 & c0 & Hk2 & _). unfold l1_absent. rewrite group_i2. rewrite Hk2. reflexivity.
Qed.

Lemma ptree_level0_l0_absent (t : ptree) (vpn : mword 27) (p2 p1 w0 : mword 64) :
  ptree_level0 t vpn p2 p1 w0 -> l0_absent t (bv_unsigned vpn / 512) = 0%nat.
Proof.
  intros (c1 & c0 & Hk2 & Hk1 & _). unfold l0_absent.
  rewrite group_i2_of_q0. rewrite Hk2. rewrite group_i1_of_q0. rewrite Hk1. reflexivity.
Qed.

(* ------ pt_missing at one page = the two absent counts along vpn -------- *)

Lemma pt_missing_1_eq (t : ptree) (vpn : mword 27) :
  pt_missing t vpn 1
  = (l0_absent t (bv_unsigned vpn / 512) + l1_absent t (bv_unsigned vpn / 262144))%nat.
Proof.
  unfold pt_missing.
  replace (bv_unsigned vpn + Z.of_nat 1 - 1)%Z with (bv_unsigned vpn) by lia.
  rewrite l0count_single l1count_single. reflexivity.
Qed.

(* ------ the COMBINED telescope lemma mappages calls each iteration ------
   offpath agreement + walk's present-facts telescope the tail's missing
   count under the whole run's, with the head accounted as [pt_missing t vpn 1]
   (= the tables the single-page walk grafts). *)
Lemma pt_missing_tel_offpath (t t' : ptree) (vpn : mword 27) (n : nat) :
  (bv_unsigned vpn + Z.of_nat n + 1 <= 134217728)%Z ->
  ptree_offpath_eq vpn t t' ->
  l0_absent t' (bv_unsigned vpn / 512) = 0%nat ->
  l1_absent t' (bv_unsigned vpn / 262144) = 0%nat ->
  (pt_missing t vpn 1 + pt_missing t' (add_vec_int vpn 1) n <= pt_missing t vpn (S n))%nat.
Proof.
  intros Hnw Hoff Hl0z Hl1z.
  pose proof (offpath_l0_flip vpn t t' Hoff Hl0z) as Hl0o.
  pose proof (offpath_l1_flip vpn t t' Hoff) as Hl1o.
  pose proof (pt_missing_tel_gen t t' vpn n Hnw Hl0z Hl0o Hl1z Hl1o) as H.
  rewrite <- pt_missing_1_eq in H. exact H.
Qed.

(* ------ pt_missing monotone in the page count (failure-arm bound) ------- *)

Lemma l0count_ge_first (t : ptree) (a b : Z) :
  (a <= b)%Z -> (l0_absent t a <= l0count t a b)%nat.
Proof. intros H. unfold l0count. rewrite (sum_seqZ_cons (l0_absent t) a b H). lia. Qed.

Lemma l1count_ge_first (t : ptree) (a b : Z) :
  (a <= b)%Z -> (l1_absent t a <= l1count t a b)%nat.
Proof. intros H. unfold l1count. rewrite (sum_seqZ_cons (l1_absent t) a b H). lia. Qed.

Lemma pt_missing_1_le (t : ptree) (v : mword 27) (n : nat) :
  (pt_missing t v 1 <= pt_missing t v (S n))%nat.
Proof.
  rewrite pt_missing_1_eq.
  pose proof (vpn_range v) as [Hlo Hhi].
  unfold pt_missing.
  set (lo := bv_unsigned v) in *.
  assert (Hle : (lo <= lo + Z.of_nat (S n) - 1)%Z) by lia.
  pose proof (Z.div_le_mono lo (lo + Z.of_nat (S n) - 1) 512 ltac:(lia) Hle) as H512.
  pose proof (Z.div_le_mono lo (lo + Z.of_nat (S n) - 1) 262144 ltac:(lia) Hle) as H262.
  pose proof (l0count_ge_first t (lo / 512) ((lo + Z.of_nat (S n) - 1) / 512) H512) as A.
  pose proof (l1count_ge_first t (lo / 262144) ((lo + Z.of_nat (S n) - 1) / 262144) H262) as B.
  lia.
Qed.

(* ===================================================================== *)
(* §13b pt_present_mono: kid-level node-presence monotonicity walk exports *)
(*    alongside ptree_offpath_eq.  [t' has (at least) every node t has]:    *)
(*    for each root kid of [t] there is a root kid of [t'] at the same slot *)
(*    whose kids cover [t]'s (L1 nodes are root kids; L0 nodes their kids). *)
(*    Threaded through walk (level-generically, mirroring                   *)
(*    ptree_offpath_eq_lvl) and used to push the [pt_missing] bound down a   *)
(*    monotonically-growing tree.                                           *)
(* ===================================================================== *)

Definition pt_present_mono (t t' : ptree) : Prop :=
  forall (i : mword 9) (c1 : ptree),
    pt_kids t i = Some c1 ->
    exists c1', pt_kids t' i = Some c1' /\
      forall (j : mword 9) (c0 : ptree),
        pt_kids c1 j = Some c0 -> exists c0', pt_kids c1' j = Some c0'.

Lemma pt_present_mono_refl (t : ptree) : pt_present_mono t t.
Proof.
  intros i c1 Hi. exists c1. split; [exact Hi |].
  intros j c0 Hj. exists c0. exact Hj.
Qed.

Lemma pt_present_mono_trans (t t' t'' : ptree) :
  pt_present_mono t t' -> pt_present_mono t' t'' -> pt_present_mono t t''.
Proof.
  intros H1 H2 i c1 Hi.
  destruct (H1 i c1 Hi) as (c1' & Hi' & Hkid1).
  destruct (H2 i c1' Hi') as (c1'' & Hi'' & Hkid2).
  exists c1''. split; [exact Hi'' |].
  intros j c0 Hj.
  destruct (Hkid1 j c0 Hj) as (c0' & Hj').
  destruct (Hkid2 j c0' Hj') as (c0'' & Hj'').
  exists c0''. exact Hj''.
Qed.

Lemma pt_present_mono_set_leaf (t : ptree) (vpn : mword 27) (w : mword 64) :
  pt_present_mono t (ptree_set_leaf t vpn w).
Proof.
  unfold ptree_set_leaf.
  destruct (pt_kids t (vpn_idx 2 vpn)) as [c1|] eqn:H1; [| apply pt_present_mono_refl].
  destruct (pt_kids c1 (vpn_idx 1 vpn)) as [c0|] eqn:H0; [| apply pt_present_mono_refl].
  intros i ci Hi.
  destruct (decide (i = vpn_idx 2 vpn)) as [E2 | N2].
  - subst i. rewrite Hi in H1. injection H1 as <-.
    exists (pt_upd_kid ci (vpn_idx 1 vpn)
              (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))).
    split; [ rewrite pt_upd_kid_same; reflexivity |].
    intros j cj Hj.
    destruct (decide (j = vpn_idx 1 vpn)) as [E1 | N1].
    + subst j. rewrite pt_upd_kid_same. eexists. reflexivity.
    + rewrite (pt_upd_kid_other _ _ _ _ N1). exists cj. exact Hj.
  - rewrite (pt_upd_kid_other _ _ _ _ N2). exists ci. split; [exact Hi |].
    intros j cj Hj. exists cj. exact Hj.
Qed.

(* ------ the LEVEL-GENERIC threading predicate (mirrors                    *)
(*        ptree_offpath_eq_lvl): at level 2 the full [pt_present_mono], at   *)
(*        level 1 the single-level present-kid clause, at level 0 nothing.   *)
Definition pt_present_mono_lvl (L : nat) (cur curf : ptree) : Prop :=
  match L with
  | O => True
  | S O => forall (j : mword 9) (c0 : ptree),
             pt_kids cur j = Some c0 -> exists c0', pt_kids curf j = Some c0'
  | S (S _) => pt_present_mono cur curf
  end.

Lemma pt_present_mono_lvl_refl (L : nat) (cur : ptree) :
  pt_present_mono_lvl L cur cur.
Proof.
  destruct L as [| [| l]]; cbn.
  - exact I.
  - intros j c0 Hj. exists c0. exact Hj.
  - apply pt_present_mono_refl.
Qed.

Lemma pt_present_mono_lvl_upd_kid (l : nat) (vpn : mword 27) (cur curf c : ptree) :
  (S l <= 2)%nat ->
  pt_kids cur (vpn_idx (S l) vpn) = Some c ->
  pt_present_mono_lvl l c curf ->
  pt_present_mono_lvl (S l) cur (pt_upd_kid cur (vpn_idx (S l) vpn) (Some curf)).
Proof.
  intros HL Hk Hpm. destruct l as [| [| l]]; [| | exfalso; lia].
  - (* S l = 1 *)
    cbn [pt_present_mono_lvl]. intros j c0 Hj.
    destruct (decide (j = vpn_idx 1 vpn)) as [E1 | N1].
    + subst j. rewrite pt_upd_kid_same. eexists. reflexivity.
    + rewrite (pt_upd_kid_other _ _ _ _ N1). exists c0. exact Hj.
  - (* S l = 2 *)
    cbn [pt_present_mono_lvl] in Hpm |- *. unfold pt_present_mono.
    intros i ci Hi.
    destruct (decide (i = vpn_idx 2 vpn)) as [E2 | N2].
    + subst i. rewrite Hi in Hk. injection Hk as <-.
      exists curf. split; [ rewrite pt_upd_kid_same; reflexivity |]. exact Hpm.
    + rewrite (pt_upd_kid_other _ _ _ _ N2). exists ci. split; [exact Hi |].
      intros j c0 Hj. exists c0. exact Hj.
Qed.

Lemma pt_present_mono_lvl_graft (l : nat) (vpn : mword 27) (cur curf : ptree) (b : mword 44) :
  (S l <= 2)%nat ->
  pt_kids cur (vpn_idx (S l) vpn) = None ->
  pt_present_mono_lvl l (pt_empty_node b) curf ->
  pt_present_mono_lvl (S l) cur
    (pt_upd_kid (pt_graft cur (vpn_idx (S l) vpn) b) (vpn_idx (S l) vpn) (Some curf)).
Proof.
  intros HL Hk Hpm. destruct l as [| [| l]]; [| | exfalso; lia].
  - (* S l = 1: the on-path slot of [cur] is absent (Hk), so nothing on-path
       needs preserving; every present kid is off-path and grafted through. *)
    cbn [pt_present_mono_lvl]. intros j c0 Hj.
    destruct (decide (j = vpn_idx 1 vpn)) as [E1 | N1].
    + subst j. rewrite Hk in Hj. discriminate.
    + rewrite (pt_upd_kid_other _ _ _ _ N1).
      rewrite (pt_graft_kids_other cur (vpn_idx 1 vpn) j b N1).
      exists c0. exact Hj.
  - (* S l = 2 *)
    cbn [pt_present_mono_lvl] in Hpm |- *. unfold pt_present_mono.
    intros i ci Hi.
    destruct (decide (i = vpn_idx 2 vpn)) as [E2 | N2].
    + subst i. rewrite Hk in Hi. discriminate.
    + rewrite (pt_upd_kid_other _ _ _ _ N2).
      rewrite (pt_graft_kids_other cur (vpn_idx 2 vpn) i b N2).
      exists ci. split; [exact Hi |].
      intros j c0 Hj. exists c0. exact Hj.
Qed.

(* ------ absence-counter monotonicity ---------------------------------- *)

Lemma l1_absent_present_mono (t t' : ptree) :
  pt_present_mono t t' -> forall r, (l1_absent t' r <= l1_absent t r)%nat.
Proof.
  intros Hpm r. unfold l1_absent.
  destruct (pt_kids t (mword_of_int r : mword 9)) as [c|] eqn:Ht.
  - destruct (Hpm (mword_of_int r) c Ht) as (c' & Ht' & _).
    rewrite Ht'. lia.
  - destruct (pt_kids t' (mword_of_int r : mword 9)); lia.
Qed.

Lemma l0_absent_present_mono (t t' : ptree) :
  pt_present_mono t t' -> forall q, (l0_absent t' q <= l0_absent t q)%nat.
Proof.
  intros Hpm q. unfold l0_absent.
  destruct (pt_kids t (mword_of_int (q / 512) : mword 9)) as [c1|] eqn:Ht1.
  - destruct (Hpm (mword_of_int (q / 512)) c1 Ht1) as (c1' & Ht1' & Hkid).
    rewrite Ht1'.
    destruct (pt_kids c1 (mword_of_int (q mod 512) : mword 9)) as [c0|] eqn:Ht0.
    + destruct (Hkid (mword_of_int (q mod 512)) c0 Ht0) as (c0' & Ht0').
      rewrite Ht0'. lia.
    + destruct (pt_kids c1' (mword_of_int (q mod 512) : mword 9)); lia.
  - destruct (pt_kids t' (mword_of_int (q / 512) : mword 9)) as [c1'|].
    + destruct (pt_kids c1' (mword_of_int (q mod 512) : mword 9)); lia.
    + lia.
Qed.

(* ------ pointwise-bounded sum (no [_le] variant exists in §10/stdpp) ---- *)

Lemma sum_list_with_le {A} (f f' : A -> nat) (l : list A) :
  (forall x, x ∈ l -> (f' x <= f x)%nat) ->
  (sum_list_with f' l <= sum_list_with f l)%nat.
Proof.
  induction l as [| a l IH]; cbn; intros Hle.
  - lia.
  - assert (f' a <= f a)%nat by (apply Hle, elem_of_list_here).
    assert (sum_list_with f' l <= sum_list_with f l)%nat as IHl
      by (apply IH; intros x Hx; apply Hle, elem_of_list_further, Hx).
    lia.
Qed.

(* ------ the payoff: [pt_missing] is antitone in the growing tree -------- *)

Lemma pt_missing_present_mono (t t' : ptree) :
  pt_present_mono t t' -> forall v np, (pt_missing t' v np <= pt_missing t v np)%nat.
Proof.
  intros Hpm v np. destruct np as [| n].
  { rewrite (pt_missing_0 t' v) (pt_missing_0 t v). lia. }
  unfold pt_missing, l0count, l1count.
  apply Nat.add_le_mono.
  - apply sum_list_with_le. intros x _. apply l0_absent_present_mono, Hpm.
  - apply sum_list_with_le. intros x _. apply l1_absent_present_mono, Hpm.
Qed.

(* ===================================================================== *)
(* §14 grafts_lvl: the number of table pages walk grafts descending from a  *)
(*    level-[L] node along [vpn].  Threaded through the walk loop as the     *)
(*    invariant [g + grafts_lvl L cur vpn = pt_missing t vpn 1], it bounds   *)
(*    walk's node growth [g] by the sharp per-page missing count.           *)
(* ===================================================================== *)

Fixpoint grafts_lvl (L : nat) (cur : ptree) (vpn : mword 27) : nat :=
  match L with
  | O => O
  | S l => match pt_kids cur (vpn_idx (S l) vpn) with
           | Some c => grafts_lvl l c vpn
           | None => S l
           end
  end.

Lemma grafts_lvl_empty (L : nat) (b : mword 44) (vpn : mword 27) :
  grafts_lvl L (pt_empty_node b) vpn = L.
Proof. destruct L; reflexivity. Qed.

Lemma grafts_lvl_descend (l : nat) (cur c : ptree) (vpn : mword 27) :
  pt_kids cur (vpn_idx (S l) vpn) = Some c ->
  grafts_lvl (S l) cur vpn = grafts_lvl l c vpn.
Proof. intros H. cbn [grafts_lvl]. rewrite H. reflexivity. Qed.

Lemma grafts_lvl_none (l : nat) (cur : ptree) (vpn : mword 27) :
  pt_kids cur (vpn_idx (S l) vpn) = None -> grafts_lvl (S l) cur vpn = S l.
Proof. intros H. cbn [grafts_lvl]. rewrite H. reflexivity. Qed.

Lemma grafts_lvl_2_missing (t : ptree) (vpn : mword 27) :
  grafts_lvl 2 t vpn = pt_missing t vpn 1.
Proof.
  rewrite pt_missing_1_eq. cbn [grafts_lvl].
  unfold l0_absent, l1_absent.
  rewrite group_i2 group_i2_of_q0 group_i1_of_q0.
  destruct (pt_kids t (vpn_idx 2 vpn)) as [c1|] eqn:Hk2.
  - cbn [grafts_lvl]. destruct (pt_kids c1 (vpn_idx 1 vpn)) as [c0|] eqn:Hk1; reflexivity.
  - reflexivity.
Qed.

(* ------ run-index no-wrap bounds (mappages' telescope side conditions) -- *)

(* [bv_unsigned _ >= 0] confuses the bv zify hook here, so the range side
   conditions are discharged with explicit monotonicity, not [lia]. *)
Lemma vpn_at_unsigned (vpn0 : mword 27) (k : nat) :
  (bv_unsigned vpn0 + Z.of_nat k < 134217728)%Z ->
  bv_unsigned (vpn_at vpn0 k) = (bv_unsigned vpn0 + Z.of_nat k)%Z.
Proof.
  intros H. pose proof (bv_unsigned_in_range 27 vpn0) as [Hlo _].
  pose proof (Nat2Z.is_nonneg k) as Hk0.
  assert (Hkb : (0 <= Z.of_nat k < 134217728)%Z).
  { split; [ exact Hk0 |].
    apply (Z.le_lt_trans (Z.of_nat k) (bv_unsigned vpn0 + Z.of_nat k) 134217728); [| exact H].
    rewrite <- (Z.add_0_l (Z.of_nat k)) at 1. apply Z.add_le_mono_r. exact Hlo. }
  unfold vpn_at. rewrite (pb_add_vec_int27_wrap vpn0 (Z.of_nat k) Hkb).
  assert (HM : bv_modulus 27 = 134217728) by (vm_compute; reflexivity).
  apply bv_wrap_small. rewrite HM.
  split; [| exact H].
  rewrite <- (Z.add_0_l 0). apply Z.add_le_mono; [exact Hlo | exact Hk0].
Qed.

Lemma vpn_at_step_bv (vpn0 : mword 27) (k : nat) :
  (bv_unsigned vpn0 + Z.of_nat (S k) < 134217728)%Z ->
  bv_unsigned (vpn_at vpn0 (S k)) = bv_unsigned (add_vec_int (vpn_at vpn0 k) 1).
Proof.
  intros H. pose proof (bv_unsigned_in_range 27 vpn0) as [Hlo _].
  pose proof (Nat2Z.is_nonneg k) as Hk0.
  assert (Hk1 : (bv_unsigned vpn0 + Z.of_nat k < 134217728)%Z).
  { rewrite Nat2Z.inj_succ in H. lia. }
  rewrite (vpn_at_unsigned vpn0 (S k) H).
  rewrite (pb_add_vec_int27_wrap (vpn_at vpn0 k) 1 ltac:(lia)).
  rewrite (vpn_at_unsigned vpn0 k Hk1).
  assert (HM : bv_modulus 27 = 134217728) by (vm_compute; reflexivity).
  assert (Hrange : (0 <= bv_unsigned vpn0 + Z.of_nat k + 1 < bv_modulus 27)%Z).
  { rewrite HM. split.
    - apply Z.add_nonneg_nonneg; [ apply Z.add_nonneg_nonneg; [exact Hlo | exact Hk0] | apply Z.le_0_1 ].
    - rewrite Nat2Z.inj_succ in H. lia. }
  rewrite (bv_wrap_small 27 (bv_unsigned vpn0 + Z.of_nat k + 1)%Z Hrange).
  rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma vpn_at_0_bv (vpn0 : mword 27) : bv_unsigned (vpn_at vpn0 0) = bv_unsigned vpn0.
Proof.
  pose proof (bv_unsigned_in_range 27 vpn0) as [_ Hhi].
  assert (HM : bv_modulus 27 = 134217728) by (vm_compute; reflexivity).
  rewrite HM in Hhi.
  rewrite (vpn_at_unsigned vpn0 0
             ltac:(change (Z.of_nat 0) with 0%Z; rewrite Z.add_0_r; exact Hhi)).
  change (Z.of_nat 0) with 0%Z. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma svpn_run_bound (va : mword 64) (npages : nat) :
  (1 <= npages)%nat ->
  (bv_unsigned va + Z.of_nat npages * 4096 <= 274877906944)%Z ->
  (bv_unsigned (svpn_of va) + Z.of_nat npages <= 134217728)%Z.
Proof.
  intros Hnp Hb.
  pose proof (bv_unsigned_in_range 64 va) as [Hlo _].
  pose proof (Nat2Z.is_nonneg npages) as Hnn.
  assert (Hnp1 : (1 <= Z.of_nat npages)%Z) by lia.
  assert (Hvalt : uint va < 274877906944).
  { rewrite uint_unsigned. assert (4096 <= Z.of_nat npages * 4096)%Z by lia. lia. }
  rewrite (svpn_of_unsigned_lo va Hvalt). rewrite uint_unsigned.
  rewrite (Z.shiftr_div_pow2 (bv_unsigned va) 12 ltac:(lia)).
  change (2 ^ 12)%Z with 4096%Z.
  assert (Hup : (bv_unsigned va <= 4096 * (67108864 - Z.of_nat npages))%Z) by lia.
  assert (H1 : (bv_unsigned va / 4096 <= 67108864 - Z.of_nat npages)%Z)
    by (apply Z.div_le_upper_bound; [lia | exact Hup]).
  lia.
Qed.

