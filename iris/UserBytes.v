(* ====================================================================== *)
(* UserBytes.v -- THE BYTE-MAP VIEW OF THE USER PAGE TABLE.                *)
(*                                                                        *)
(* [UserPtTree.user_pt_inv] is what a user hart owns of memory: the tree   *)
(* ([UptTree.utlb_inv_pt]'s [ptree_own]) and the mapped data pages         *)
(* ([udata_own]).  Under whole-cycle stepping that was the right shape --  *)
(* every memory composer consumed [gen_heap_interp] and read what it       *)
(* needed out of the authority.  Under per-node stepping the hart HOLDS    *)
(* the bytes and every certified access is checked against ONE             *)
(* [gmap pa (bv 8)] ([HartMemRun.hmrun]'s map, [goodmb]'s [bytes_owned]),  *)
(* so the same ownership has to be presentable as a single byte map.       *)
(* This file is that presentation.                                        *)
(*                                                                        *)
(*   section 1  the tree's bytes: [pt_maps] / [ptree_bytes] and the        *)
(*              equivalence [ptree_own_maps].  The [pt_node_claim] ghosts  *)
(*              are NOT bytes and are kept aside as [pt_claims], which is  *)
(*              persistent, so the round trip costs nothing.               *)
(*   section 2  SHAPE: two trees differing only in their slot WORDS have   *)
(*              byte maps with the same domains, node for node.  That is   *)
(*              what makes an A/D write-back a step of the owned map       *)
(*              rather than a re-shaping of it, and it is what carries     *)
(*              the disjointness across a step.                            *)
(*   section 3  [u_mem_wf] / [u_mem_step] -- the pure well-formedness of   *)
(*              the hart's owned map and the relation a user cycle may     *)
(*              move it by.  Every memory [goodmb] twin in the port takes  *)
(*              [u_mem_wf] as a premise and returns [u_mem_step].          *)
(*   section 4  [user_pt_inv_bytes], the accessor: the invariant in, the   *)
(*              byte map plus a closing wand out.                          *)
(*                                                                        *)
(* WHY DISJOINTNESS IS DERIVED AND NOT ASSUMED (risk R7 of the port plan): *)
(* that a user store cannot corrupt a PTE is today implicit in the         *)
(* separating conjunction between [ptree_own] and [udata_own].  A pure     *)
(* [goodmb] certificate cannot see a separating conjunction, so the fact   *)
(* has to be EXTRACTED once -- [PtBytes.bytes_own_disj] does it -- and     *)
(* then CARRIED, as a conjunct of [u_mem_wf].  If it is ever violated the  *)
(* step relation fails and the port fails loudly rather than silently.     *)
(*                                                                        *)
(* IMPORT SET: mirrors [HartMemRun]'s, for [PtBytes]'s reason (a second    *)
(* [Countable Arch.pa] instance makes [gmap Arch.pa (bv 8)] a DIFFERENT    *)
(* type that prints identically).  Where the type has to be named, name it *)
(* [PtBytes.pamap].                                                        *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes VirtioQueue.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import HartMemRun PtBytes.
Require Import PtreeType CommonWalk Pt4kWalk PtTree.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* 1. THE TREE'S BYTES.                                                   *)
(* ===================================================================== *)

(* the 512 slot maps of ONE node page, in index order -- the same order
   [PtTree.pt_page_own] folds its [->p8] slots in *)
Definition pt_page_maps (t : ptree) : list pamap :=
  (fun i : Z => word_bytes (u_pte_addr (pt_base t) (mword_of_int i))
                           (pt_ents t (mword_of_int i))) <$> seqZ 0 512.

(* ...and of a whole subtree, node by node.  A LIST and not a union: the
   union needs disjointness, which only the OWNERSHIP knows (section 3 of
   PtBytes), so the list is what the structural equivalence is stated over
   and the union is taken exactly once, where the ownership is in hand. *)
Fixpoint pt_maps (lvl : nat) (t : ptree) : list pamap :=
  match lvl with
  | O => pt_page_maps t
  | S lvl' =>
      pt_page_maps t ++
      concat ((fun i : Z => match pt_kids t (mword_of_int i) with
                            | Some c => pt_maps lvl' c
                            | None => []
                            end) <$> seqZ 0 512)
  end.

(* the two reduction equations, spelled out.  NEVER [cbn] these definitions:
   their bodies mention [seqZ 0 512] and a whitelisted [cbn] still fires the
   beta/iota that computes the 512-element list (measured: does not finish). *)
Lemma pt_maps_O (t : ptree) : pt_maps 0 t = pt_page_maps t.
Proof. reflexivity. Qed.

Lemma pt_maps_S (lvl : nat) (t : ptree) :
  pt_maps (S lvl) t =
  (pt_page_maps t ++
   concat ((fun i : Z => match pt_kids t (mword_of_int i) with
                         | Some c => pt_maps lvl c
                         | None => []
                         end) <$> seqZ 0 512))%list.
Proof. reflexivity. Qed.

Definition ptree_bytes (lvl : nat) (t : ptree) : pamap := ⋃ (pt_maps lvl t).

Section UserBytesTree.
  Context `{!riscvGS Σ}.

  (* the node-identity ghosts, which are NOT bytes.  Persistent, so keeping
     them aside across the byte view costs nothing. *)
  Fixpoint pt_claims (lvl : nat) (t : ptree) : iProp Σ :=
    match lvl with
    | O => pt_node_claim (pt_base t)
    | S lvl' =>
        (pt_node_claim (pt_base t) ∗
         [∗ list] i ∈ seqZ 0 512,
           match pt_kids t (mword_of_int i) with
           | Some c => pt_claims lvl' c
           | None => emp
           end)%I
    end.

  Lemma pt_claims_O (t : ptree) : pt_claims 0 t = pt_node_claim (pt_base t).
  Proof. reflexivity. Qed.

  Lemma pt_claims_S (lvl : nat) (t : ptree) :
    pt_claims (S lvl) t =
    (pt_node_claim (pt_base t) ∗
     [∗ list] i ∈ seqZ 0 512,
       match pt_kids t (mword_of_int i) with
       | Some c => pt_claims lvl c
       | None => emp
       end)%I.
  Proof. reflexivity. Qed.

  Global Instance pt_claims_persistent lvl t : Persistent (pt_claims lvl t).
  Proof.
    revert t. induction lvl as [| lvl IH]; intros t.
    - rewrite pt_claims_O. apply _.
    - rewrite pt_claims_S. apply bi.sep_persistent; [apply _ |].
      apply big_sepL_persistent. intros k i Hk.
      destruct (pt_kids t (mword_of_int i)); [apply IH | apply _].
  Qed.

  (* one node page: the [->p8] slots ARE the slot maps *)
  Lemma pt_page_own_maps (t : ptree) :
    pt_page_own (DfracOwn 1) t ⊣⊢
    pt_node_claim (pt_base t) ∗ [∗ list] m ∈ pt_page_maps t, bytes_own m.
  Proof.
    rewrite /pt_page_own /pt_page_maps big_sepL_fmap.
    apply bi.sep_proper; [reflexivity |].
    apply big_sepL_proper. intros k i _.
    rewrite phys_word_bytes_own_full.
    rewrite (bi.pure_True _ (pte_addr_at_aligned8 (pt_base t) (mword_of_int i))).
    by rewrite left_id.
  Qed.

  (* the flattening lemma the recursive step needs *)
  Lemma big_sepL_bytes_concat (ls : list (list pamap)) :
    ([∗ list] m ∈ concat ls, bytes_own m) ⊣⊢
    [∗ list] l ∈ ls, [∗ list] m ∈ l, bytes_own m.
  Proof.
    induction ls as [| l ls IH]; [reflexivity |].
    rewrite concat_cons big_sepL_app big_sepL_cons IH. reflexivity.
  Qed.

  (* ...at the exact shape [pt_maps]'s recursive arm has.  Spelled with the
     inner [big_sepL] left UNDER the match on both sides: pulling it out
     would need a [big_sepL_proper] whose higher-order unification picks the
     INNER big op and fails with an unreadable "cannot unify list ... with
     nat". *)
  Lemma big_sepL_bytes_kids (f : ptree -> list pamap) (t : ptree) :
    ([∗ list] m ∈ concat (fmap (M := list)
                            (fun i : Z => match pt_kids t (mword_of_int i) with
                                          | Some c => f c
                                          | None => @nil pamap end)
                            (seqZ 0 512)), bytes_own m)
    ⊣⊢ [∗ list] i ∈ seqZ 0 512,
          [∗ list] m ∈ (match pt_kids t (mword_of_int i) with
                        | Some c => f c
                        | None => @nil pamap end), bytes_own m.
  Proof. by rewrite big_sepL_bytes_concat big_sepL_fmap. Qed.

  (* THE STRUCTURAL EQUIVALENCE.  [ptree_own] IS the claims plus the slot
     maps; nothing is lost and nothing is assumed. *)
  Lemma ptree_own_maps (lvl : nat) (t : ptree) :
    ptree_own lvl (DfracOwn 1) t ⊣⊢
    pt_claims lvl t ∗ [∗ list] m ∈ pt_maps lvl t, bytes_own m.
  Proof.
    revert t. induction lvl as [| lvl IH]; intros t.
    - rewrite /ptree_own pt_page_own_maps pt_maps_O pt_claims_O.
      apply bi.sep_emp.
    - rewrite ptree_own_S pt_page_own_maps /pt_kids_own.
      rewrite pt_claims_S pt_maps_S.
      rewrite big_sepL_app big_sepL_bytes_kids.
      assert (Hkid : ([∗ list] i ∈ seqZ 0 512,
                        match pt_kids t (mword_of_int i) with
                        | Some c => ptree_own lvl (DfracOwn 1) c
                        | None => emp
                        end)%I
                     ⊣⊢ ([∗ list] i ∈ seqZ 0 512,
                           (match pt_kids t (mword_of_int i) with
                            | Some c => pt_claims lvl c | None => emp end ∗
                            [∗ list] m ∈ (match pt_kids t (mword_of_int i) with
                                          | Some c => pt_maps lvl c
                                          | None => @nil pamap end),
                              bytes_own m))%I).
      { apply big_sepL_proper. intros k i _.
        destruct (pt_kids t (mword_of_int i)) as [c |].
        - apply IH.
        - by rewrite left_id. }
      rewrite Hkid big_sepL_sep.
      (* the remaining step is pure AC rearrangement,
         (A * B) * (C * D) <-> (A * C) * (B * D).  Done in the proofmode:
         the [assoc]/[comm] setoid rewrites at this shape -- big ops on both
         sides -- do not terminate (measured: killed at 2 min). *)
      apply bi.equiv_entails_2.
      + iIntros "[[HA HB] [HC HD]]". iFrame.
      + iIntros "[[HA HC] [HB HD]]". iFrame.
  Qed.

  (* ...and the union, taken where the ownership is in hand *)
  Lemma ptree_own_bytes (lvl : nat) (t : ptree) :
    ptree_own lvl (DfracOwn 1) t ⊢
    pt_claims lvl t ∗ ⌜maps_disj (pt_maps lvl t)⌝ ∗ bytes_own (ptree_bytes lvl t).
  Proof.
    rewrite ptree_own_maps. iIntros "[#Hc Hm]".
    iDestruct (bytes_own_list_disj with "Hm") as %Hd.
    iFrame "Hc". iSplitR; [done |].
    rewrite /ptree_bytes -(bytes_own_list_union _ Hd). iExact "Hm".
  Qed.

  Lemma ptree_own_of_bytes (lvl : nat) (t : ptree) :
    maps_disj (pt_maps lvl t) ->
    pt_claims lvl t -∗ bytes_own (ptree_bytes lvl t) -∗
    ptree_own lvl (DfracOwn 1) t.
  Proof.
    intros Hd. iIntros "Hc Hb". rewrite ptree_own_maps /ptree_bytes.
    rewrite (bytes_own_list_union _ Hd). iFrame.
  Qed.

End UserBytesTree.

(* ===================================================================== *)
(* 2. SHAPE: what an A/D WRITE-BACK may and may not do.                   *)
(*                                                                       *)
(* A page walk may set the A and D bits of the leaf it used; it never     *)
(* moves a node, adds one, or removes one.  [pt_same_shape] is exactly    *)
(* that: same node bases, same child structure, slot WORDS free.  Two     *)
(* consequences, and they are the whole reason the relation exists:       *)
(* the byte maps have the same domains node for node (so the hart's owned *)
(* map does not change shape across a cycle), and the DISJOINTNESS -- a   *)
(* fact about domains only -- carries across.                             *)
(* ===================================================================== *)

Fixpoint pt_same_shape (lvl : nat) (t t' : ptree) : Prop :=
  pt_base t = pt_base t' /\
  match lvl with
  | O => True
  | S lvl' =>
      forall i : mword 9,
        match pt_kids t i, pt_kids t' i with
        | Some c, Some c' => pt_same_shape lvl' c c'
        | None, None => True
        | _, _ => False
        end
  end.

Lemma pt_same_shape_refl (lvl : nat) (t : ptree) : pt_same_shape lvl t t.
Proof.
  revert t. induction lvl as [| lvl IH]; intros t; split; [reflexivity | done | reflexivity |].
  intros i. by destruct (pt_kids t i).
Qed.

Lemma Forall2_refl_list {A} (Q : A -> A -> Prop) (l : list A) :
  (forall x, x ∈ l -> Q x x) -> Forall2 Q l l.
Proof.
  induction l as [| x l IH]; intros H; constructor.
  - apply H, elem_of_list_here.
  - apply IH. intros y Hy. apply H, elem_of_list_further, Hy.
Qed.

Lemma Forall2_concat {A B} (Q : A -> B -> Prop)
    (ls1 : list (list A)) (ls2 : list (list B)) :
  Forall2 (Forall2 Q) ls1 ls2 -> Forall2 Q (concat ls1) (concat ls2).
Proof.
  induction 1 as [| l1 l2 ls1 ls2 Hl Hls IH]; [constructor |].
  rewrite !concat_cons. by apply Forall2_app.
Qed.

(* the byte maps of two same-shaped trees agree on DOMAINS, node for node *)
Lemma pt_page_maps_dom_shape (t t' : ptree) :
  pt_base t = pt_base t' ->
  Forall2 (fun m m' => (dom m : gset Arch.pa) = dom m')
    (pt_page_maps t) (pt_page_maps t').
Proof.
  intros Hb. rewrite /pt_page_maps. apply Forall2_fmap, Forall2_refl_list.
  intros i _. rewrite Hb. apply word_bytes_dom_eq.
Qed.

Lemma pt_maps_dom_shape (lvl : nat) (t t' : ptree) :
  pt_same_shape lvl t t' ->
  Forall2 (fun m m' => (dom m : gset Arch.pa) = dom m')
    (pt_maps lvl t) (pt_maps lvl t').
Proof.
  revert t t'. induction lvl as [| lvl IH]; intros t t' [Hb Hk].
  - rewrite !pt_maps_O. by apply pt_page_maps_dom_shape.
  - rewrite !pt_maps_S. apply Forall2_app; [by apply pt_page_maps_dom_shape |].
    apply Forall2_concat, Forall2_fmap, Forall2_refl_list.
    intros i _. specialize (Hk (mword_of_int i)).
    destruct (pt_kids t (mword_of_int i)) as [c |];
      destruct (pt_kids t' (mword_of_int i)) as [c' |]; try done.
    by apply IH.
Qed.

Lemma pt_maps_disj_shape (lvl : nat) (t t' : ptree) :
  pt_same_shape lvl t t' -> maps_disj (pt_maps lvl t) -> maps_disj (pt_maps lvl t').
Proof.
  intros Hs. apply maps_disj_dom, pt_maps_dom_shape, Hs.
Qed.

Section UserBytesShape.
  Context `{!riscvGS Σ}.

  (* the node-identity ghosts depend on the BASES only, so a write-back does
     not disturb them -- which is what lets a caller hand the SAME persistent
     claims back with the new tree *)
  Lemma pt_claims_shape (lvl : nat) (t t' : ptree) :
    pt_same_shape lvl t t' -> pt_claims lvl t ⊣⊢ pt_claims lvl t'.
  Proof.
    revert t t'. induction lvl as [| lvl IH]; intros t t' [Hb Hk].
    - rewrite !pt_claims_O. by rewrite Hb.
    - rewrite !pt_claims_S Hb. apply bi.sep_proper; [reflexivity |].
      apply big_sepL_proper. intros k i _.
      specialize (Hk (mword_of_int i)).
      destruct (pt_kids t (mword_of_int i)) as [c |];
        destruct (pt_kids t' (mword_of_int i)) as [c' |]; try done.
      by apply IH.
  Qed.

End UserBytesShape.
