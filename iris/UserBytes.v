(* ====================================================================== *)
(* UserBytes.v -- THE BYTE-MAP VIEW OF THE USER PAGE TABLE.                *)
(*                                                                        *)
(* [UserPtTree.user_pt_any] is what a user hart owns of memory: the tree   *)
(* ([UptTree.utlb_inv_pt]'s [ptree_own]) and the process's own memory      *)
(* ([umem_own P M], keyed by USER VIRTUAL ADDRESS -- the abstract state,   *)
(* quantified here because a user cycle may write what it likes inside     *)
(* its own pages).  Under whole-cycle stepping the old shape (existential  *)
(* page contents at a flat pa-set) was right --                            *)
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
(*   section 3b the ADDRESS-SPACE re-keying: [umem_any] (va-keyed) <-> one *)
(*              [pamap] (pa-keyed), a BIJECTION by [uva_pa_inj].           *)
(*   section 4  [user_pt_inv_bytes], the accessor: the invariant in, the   *)
(*              byte map plus a closing wand out.                          *)
(*                                                                        *)
(* WHY DISJOINTNESS IS DERIVED AND NOT ASSUMED (risk R7 of the port plan): *)
(* that a user store cannot corrupt a PTE is today implicit in the         *)
(* separating conjunction between [ptree_own] and [umem_own].  A pure      *)
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
Require Import SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes VirtioQueue.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import HartMemRun PtBytes.
Require Import PtreeType CommonWalk Pt4kWalk PtTree.
Require Import RiscvFetchExec PtTreeAdue SmodePte UptTree UserPtTree.
Require Import UserBits.
Require Import TsoCtx.
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
  Context `{XI : CurCtx}.

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
    (* the USER tier's slot IS [ctx_phys_word_pointsto] (PtTree's tiered
       [pt_slot_own] at [Some ξ]); one iota step exposes it. *)
    rewrite /pt_slot_own. cbn match.
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

(* TRANSITIVITY, which is what a composer running TWO walks needs: each walk
   may write back its own leaf's A/D bits, and the two shapes must compose.
   Both the page-straddling data accesses (UserMemCert section 8) and the
   2-aligned straddling FETCH (UserFetchCert section 8) stand on it. *)
Lemma pt_same_shape_trans (lvl : nat) (t1 t2 t3 : ptree) :
  pt_same_shape lvl t1 t2 -> pt_same_shape lvl t2 t3 -> pt_same_shape lvl t1 t3.
Proof.
  revert t1 t2 t3. induction lvl as [| lvl IH]; intros t1 t2 t3 [Hb1 Hk1] [Hb2 Hk2].
  - split; [ by rewrite Hb1 | exact I ].
  - split; [ by rewrite Hb1 |]. intros i.
    specialize (Hk1 i). specialize (Hk2 i).
    destruct (pt_kids t1 i) as [c1|]; destruct (pt_kids t2 i) as [c2|];
      destruct (pt_kids t3 i) as [c3|]; try contradiction; try exact I.
    exact (IH c1 c2 c3 Hk1 Hk2).
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

(* ===================================================================== *)
(* 3. [u_mem_wf] / [u_mem_step] -- THE HART'S OWNED MAP.                  *)
(*                                                                       *)
(* [u_mem_wf P t mm] says: [mm] is the tree [t]'s bytes together with the *)
(* mapped data pages' bytes, the two halves are DISJOINT, every address   *)
(* in it is RAM, and the pure page-table facts [user_pt_inv] carries hold *)
(* of [t].  It is the premise every memory [goodmb] twin in the port      *)
(* takes; [goodmb]'s two obligations at a RAM access -- the footprint is  *)
(* inside the owned map, and the address is not a device -- are           *)
(* projections of it ([PtBytes] section 2, and the [addr_is_ram]          *)
(* conjunct with [RiscvPtsto.addr_is_ram_not_dev]).                        *)
(*                                                                       *)
(* [u_mem_step P t t' mm mm'] is what a user cycle may do to it: the      *)
(* data half is ARBITRARY at the same domain (a user store writes what it *)
(* likes inside its own pages), and the tree half moves only to a         *)
(* SAME-SHAPED tree that still satisfies [upt_tree_spec] -- which is      *)
(* exactly the A/D write-back, since [upt_tree_spec] already quantifies   *)
(* its leaves as [pte_set_ad w a d].  Re-establishing the invariant is    *)
(* therefore the pure content of the existing ADUE absorption and not new *)
(* reasoning.                                                             *)
(* ===================================================================== *)

Definition u_mem_wf (P : uptd) (t : ptree) (mm : pamap) : Prop :=
  exists md : pamap,
    maps_disj (pt_maps 2 t) /\
    ptree_bytes 2 t ##ₘ md /\
    mm = ptree_bytes 2 t ∪ md /\
    (forall a : Arch.pa, u_data_pa P a <-> is_Some (md !! a)) /\
    (forall a : Arch.pa, a ∈ (dom mm : gset Arch.pa) -> addr_is_ram a) /\
    upt_acc_wf (ud_um P) /\
    upt_map_wf (ud_um P) /\
    upt_tree_spec (ud_root P) (ud_tfp P) (ud_um P) t.

Definition u_mem_step (P : uptd) (t t' : ptree) (mm mm' : pamap) : Prop :=
  pt_same_shape 2 t t' /\
  upt_tree_spec (ud_root P) (ud_tfp P) (ud_um P) t' /\
  exists md' : pamap,
    ptree_bytes 2 t' ##ₘ md' /\
    mm' = ptree_bytes 2 t' ∪ md' /\
    (forall a : Arch.pa, u_data_pa P a <-> is_Some (md' !! a)).

(* the domains agree along a step -- which is what [HartMemRun]'s
   [dom mm' = dom mm] obligation wants, and what makes a stretch's
   certificate re-usable at the next node *)
Lemma union_list_dom_shape (l l' : list pamap) :
  Forall2 (fun m m' => (dom m : gset Arch.pa) = dom m') l l' ->
  (dom (⋃ l) : gset Arch.pa) = dom (⋃ l').
Proof.
  induction 1 as [| m m' l l' Hm Hl IH]; [reflexivity |].
  rewrite !union_list_cons !dom_union_L. by f_equal.
Qed.

Lemma ptree_bytes_dom_shape (lvl : nat) (t t' : ptree) :
  pt_same_shape lvl t t' ->
  (dom (ptree_bytes lvl t) : gset Arch.pa) = dom (ptree_bytes lvl t').
Proof.
  intros Hs. rewrite /ptree_bytes.
  apply union_list_dom_shape, pt_maps_dom_shape, Hs.
Qed.

Lemma u_mem_step_dom (P : uptd) (t t' : ptree) (mm mm' : pamap) :
  u_mem_wf P t mm -> u_mem_step P t t' mm mm' ->
  (dom mm' : gset Arch.pa) = dom mm.
Proof.
  intros (md & _ & _ & -> & Hdm & _) (Hshape & _ & md' & _ & -> & Hdm').
  assert (Hd : (dom md' : gset Arch.pa) = dom md).
  { apply set_eq. intros a. rewrite !elem_of_dom. split; intros H.
    - apply (proj1 (Hdm a)), (proj2 (Hdm' a)), H.
    - apply (proj1 (Hdm' a)), (proj2 (Hdm a)), H. }
  rewrite (dom_union_L (ptree_bytes 2 t') md') (dom_union_L (ptree_bytes 2 t) md).
  rewrite Hd -(ptree_bytes_dom_shape 2 t t' Hshape). reflexivity.
Qed.

(* ...and so a step lands back in [u_mem_wf], at the new tree *)
Lemma u_mem_step_wf (P : uptd) (t t' : ptree) (mm mm' : pamap) :
  u_mem_wf P t mm -> u_mem_step P t t' mm mm' -> u_mem_wf P t' mm'.
Proof.
  intros Hwf Hstep.
  pose proof (u_mem_step_dom P t t' mm mm' Hwf Hstep) as Hdom.
  destruct Hwf as (md & Hdisj & Hdj & Hmm & Hdm & Hram & Hacc & Hwfm & Hspec).
  destruct Hstep as (Hshape & Hspec' & md' & Hdj' & Hmm' & Hdm').
  (* explicit, never [try done]: [done] on a [maps_disj (pt_maps 2 t')] goal
     tries to evaluate the 512-way [seqZ] and does not come back *)
  exists md'. split_and!.
  - apply (pt_maps_disj_shape 2 t t' Hshape Hdisj).
  - exact Hdj'.
  - exact Hmm'.
  - exact Hdm'.
  - intros a Ha. apply Hram. rewrite <- Hdom. exact Ha.
  - exact Hacc.
  - exact Hwfm.
  - exact Hspec'.
Qed.

(* a stretch that changes nothing is a step *)
Lemma u_mem_step_refl (P : uptd) (t : ptree) (mm : pamap) :
  u_mem_wf P t mm -> u_mem_step P t t mm mm.
Proof.
  intros (md & _ & Hdj & Hmm & Hdm & _ & _ & _ & Hspec).
  split_and!; [ apply pt_same_shape_refl | exact Hspec |].
  exists md. split_and!; [ exact Hdj | exact Hmm | exact Hdm ].
Qed.

(* ...and two stretches in a row compose.  Only the SHAPE conjunct needs
   work; the tree spec and the data-half witness both come from the second
   step alone.  Every composer that translates TWICE -- the page-straddling
   load/store and the 2-aligned straddling fetch -- ends on this. *)
Lemma u_mem_step_trans (P : uptd) (t1 t2 t3 : ptree) (mm1 mm2 mm3 : pamap) :
  u_mem_step P t1 t2 mm1 mm2 -> u_mem_step P t2 t3 mm2 mm3 ->
  u_mem_step P t1 t3 mm1 mm3.
Proof.
  intros (Hs1 & _ & _) (Hs2 & Hspec & md & Hrest).
  split_and!; [ exact (pt_same_shape_trans 2 t1 t2 t3 Hs1 Hs2) | exact Hspec |].
  exists md. exact Hrest.
Qed.

(* THE SLOT VIEW.  A page-table slot of ANY node of the tree is readable
   out of the owned map -- which is what turns the walk's [ptree_own_path_mem]
   (an Iris accessor over the authority) into a PURE premise. *)
Lemma pt_page_map_mem (t : ptree) (i : Z) :
  0 <= i < 512 ->
  word_bytes (u_pte_addr (pt_base t) (mword_of_int i))
             (pt_ents t (mword_of_int i)) ∈ pt_page_maps t.
Proof.
  intros Hi. rewrite /pt_page_maps. apply elem_of_list_fmap.
  exists i. split; [reflexivity |]. apply elem_of_seqZ. lia.
Qed.

Lemma pt_maps_page (lvl : nat) (t : ptree) (m : pamap) :
  m ∈ pt_page_maps t -> m ∈ pt_maps lvl t.
Proof.
  intros Hm. destruct lvl as [| lvl]; [ by rewrite pt_maps_O |].
  rewrite pt_maps_S elem_of_app. by left.
Qed.

Lemma pt_maps_kid (lvl : nat) (t c : ptree) (i : Z) (m : pamap) :
  0 <= i < 512 -> pt_kids t (mword_of_int i) = Some c ->
  m ∈ pt_maps lvl c -> m ∈ pt_maps (S lvl) t.
Proof.
  intros Hi Hk Hm. rewrite pt_maps_S elem_of_app. right.
  apply elem_of_list_In, in_concat.
  exists (pt_maps lvl c). split.
  - apply elem_of_list_In, elem_of_list_fmap.
    exists i. rewrite Hk. split; [reflexivity |]. apply elem_of_seqZ. lia.
  - by apply elem_of_list_In.
Qed.


(* ====================================================================== *)
(* THE WEAKER MEMORY PREDICATE, and why it exists.                         *)
(*                                                                        *)
(* [u_mem_wf]'s fourth clause -- [forall a, a in ud_data P <-> is_Some     *)
(* (md !! a)] -- says the owned map covers the mapped data EXACTLY.  That  *)
(* is right for the SAFETY tier, whose arms must serve an arbitrary        *)
(* address, and it is unpayable for any caller that owns only PART of its  *)
(* address space.  The VERIFIED Umode tier is such a caller: its memory is *)
(* [UmodeMem.umem pt M], the process's NAMED image, a subset.              *)
(*                                                                        *)
(* [u_mem_ok] is [u_mem_wf] minus that clause (and minus the two pure      *)
(* facts about [ud_data]/[upt_acc_wf] that only exist to feed it).  What   *)
(* the coverage clause was USED for -- proving a particular access window  *)
(* owned -- becomes a per-access premise the caller supplies: the safety   *)
(* tier from [u_fetch_win_in], the verified tier from its own [umem].      *)
(*                                                                        *)
(* THIS IS THE THIRD INSTANCE OF THE SAME OVER-STRONG-COVERAGE DISEASE.    *)
(* [u_mem_wf] could not be instantiated by the table-only caller either,   *)
(* and [upt_tmem] is the worked precedent: drop the half the caller cannot *)
(* pay, keep the half it needs, and give the strong predicate a one-line   *)
(* implication into the weak one so no existing call site is re-proved.    *)
(* ====================================================================== *)

Definition u_mem_ok (P : uptd) (t : ptree) (mm : pamap) : Prop :=
  exists md : pamap,
    maps_disj (pt_maps 2 t) /\
    ptree_bytes 2 t ##ₘ md /\
    mm = ptree_bytes 2 t ∪ md /\
    (forall a : Arch.pa, a ∈ (dom mm : gset Arch.pa) -> addr_is_ram a) /\
    upt_map_wf (ud_um P) /\
    upt_tree_spec (ud_root P) (ud_tfp P) (ud_um P) t.

(* every safety-tier call site pays ONE lemma application, not a re-proof *)
Lemma u_mem_wf_ok (P : uptd) (t : ptree) (mm : pamap) :
  u_mem_wf P t mm -> u_mem_ok P t mm.
Proof.
  intros (md & Hdisj & Hdj & Hmm & _ & Hram & _ & Hwfm & Hspec).
  exists md. split_and!;
    [ exact Hdisj | exact Hdj | exact Hmm | exact Hram | exact Hwfm | exact Hspec ].
Qed.

(* --- the four TREE projections, at the weaker predicate.  None of them
       ever used the coverage clause, so each is its old proof verbatim and
       the [u_mem_wf] form becomes a one-line corollary. --- *)

Lemma u_mem_ok_sub (P : uptd) (t : ptree) (mm : pamap)
    (a : Arch.pa) (w : bv 64) :
  u_mem_ok P t mm -> word_bytes a w ∈ pt_maps 2 t -> word_bytes a w ⊆ mm.
Proof.
  intros (md & Hdisj & Hdj & -> & _) Hm.
  etrans; [ exact (maps_disj_subseteq _ _ Hdisj Hm) |].
  apply map_union_subseteq_l.
Qed.

Lemma u_mem_ok_read (P : uptd) (t : ptree) (mm : pamap)
    (a : Arch.pa) (w : bv 64) :
  u_mem_ok P t mm -> word_bytes a w ∈ pt_maps 2 t ->
  read_bytes mm a 8 = Some w.
Proof. intros Hok Hm. by apply read_bytes_word, (u_mem_ok_sub P t mm a w). Qed.

Lemma u_mem_ok_owned (P : uptd) (t : ptree) (mm : pamap)
    (a : Arch.pa) (w : bv 64) :
  u_mem_ok P t mm -> word_bytes a w ∈ pt_maps 2 t ->
  bytes_owned mm a 8 = true.
Proof.
  intros Hok Hm.
  apply (bytes_owned_word mm a w), (u_mem_ok_sub P t mm a w Hok Hm).
Qed.

Lemma u_mem_ok_not_dev (P : uptd) (t : ptree) (mm : pamap) (a : Arch.pa) :
  u_mem_ok P t mm -> a ∈ (dom mm : gset Arch.pa) -> dev_addr a = false.
Proof.
  intros (md & Hd1 & Hd2 & Hmm & Hram & Hwfm & Hspec) Ha.
  by apply addr_is_ram_not_dev, Hram.
Qed.

(* --- and the STEP, likewise.  [u_mem_step]'s own coverage clause is what
       proves [dom mm' = dom mm]; without it the domain equality has to be
       stated, which is exactly what [swp_hmrun_of_exec] hands back anyway. --- *)

Definition u_mem_step_ok (P : uptd) (t t' : ptree) (mm mm' : pamap) : Prop :=
  pt_same_shape 2 t t' /\
  upt_tree_spec (ud_root P) (ud_tfp P) (ud_um P) t' /\
  (dom mm' : gset Arch.pa) = dom mm /\
  exists md' : pamap,
    ptree_bytes 2 t' ##ₘ md' /\
    mm' = ptree_bytes 2 t' ∪ md'.

Lemma u_mem_step_ok_of (P : uptd) (t t' : ptree) (mm mm' : pamap) :
  u_mem_wf P t mm -> u_mem_step P t t' mm mm' -> u_mem_step_ok P t t' mm mm'.
Proof.
  intros Hwf Hstep.
  pose proof (u_mem_step_dom P t t' mm mm' Hwf Hstep) as Hdom.
  destruct Hstep as (Hshape & Hspec & md' & Hdj' & Hmm' & _).
  split_and!; [ exact Hshape | exact Hspec | exact Hdom |].
  exists md'. split; [ exact Hdj' | exact Hmm' ].
Qed.

Lemma u_mem_step_ok_refl (P : uptd) (t : ptree) (mm : pamap) :
  u_mem_ok P t mm -> u_mem_step_ok P t t mm mm.
Proof.
  intros (md & _ & Hdj & Hmm & _ & _ & Hspec).
  split_and!; [ apply pt_same_shape_refl | exact Hspec | reflexivity |].
  exists md. split; [ exact Hdj | exact Hmm ].
Qed.

Lemma u_mem_step_ok_trans (P : uptd) (t1 t2 t3 : ptree) (mm1 mm2 mm3 : pamap) :
  u_mem_step_ok P t1 t2 mm1 mm2 -> u_mem_step_ok P t2 t3 mm2 mm3 ->
  u_mem_step_ok P t1 t3 mm1 mm3.
Proof.
  intros (Hs1 & _ & Hd1 & _) (Hs2 & Hspec & Hd2 & md & Hrest).
  split_and!;
    [ exact (pt_same_shape_trans 2 t1 t2 t3 Hs1 Hs2) | exact Hspec
    | rewrite Hd2; exact Hd1 |].
  exists md. exact Hrest.
Qed.

(* ...and a step lands back in [u_mem_ok], at the new tree *)
Lemma u_mem_step_ok_wf (P : uptd) (t t' : ptree) (mm mm' : pamap) :
  u_mem_ok P t mm -> u_mem_step_ok P t t' mm mm' -> u_mem_ok P t' mm'.
Proof.
  intros Hok Hstep.
  (* NOT [_] for the map equation: an anonymous equation gets substituted,
     which would clear [mm] -- and [Hram] still mentions it. *)
  destruct Hok as (md & Hdisj & Hdj0 & Hmm0 & Hram & Hwfm & Hspec0).
  destruct Hstep as (Hshape & Hspec' & Hdom & md' & Hdj' & Hmm').
  exists md'. split_and!.
  - apply (pt_maps_disj_shape 2 t t' Hshape Hdisj).
  - exact Hdj'.
  - exact Hmm'.
  - intros a Ha. apply Hram. rewrite <- Hdom. exact Ha.
  - exact Hwfm.
  - exact Hspec'.
Qed.

Lemma u_mem_wf_sub (P : uptd) (t : ptree) (mm : pamap)
    (a : Arch.pa) (w : bv 64) :
  u_mem_wf P t mm -> word_bytes a w ∈ pt_maps 2 t -> word_bytes a w ⊆ mm.
Proof.
  intros (md & Hdisj & Hdj & -> & _) Hm.
  etrans; [ exact (maps_disj_subseteq _ _ Hdisj Hm) |].
  apply map_union_subseteq_l.
Qed.

Lemma u_mem_wf_read (P : uptd) (t : ptree) (mm : pamap)
    (a : Arch.pa) (w : bv 64) :
  u_mem_wf P t mm -> word_bytes a w ∈ pt_maps 2 t ->
  read_bytes mm a 8 = Some w.
Proof. intros Hwf Hm. by apply read_bytes_word, (u_mem_wf_sub P t mm a w). Qed.

Lemma u_mem_wf_owned (P : uptd) (t : ptree) (mm : pamap)
    (a : Arch.pa) (w : bv 64) :
  u_mem_wf P t mm -> word_bytes a w ∈ pt_maps 2 t ->
  bytes_owned mm a 8 = true.
Proof.
  intros Hwf Hm.
  apply (bytes_owned_word mm a w), (u_mem_wf_sub P t mm a w Hwf Hm).
Qed.

(* every access inside the owned map is RAM, hence NOT a device -- the
   conjunct that lets the tier have no MMIO arm at all *)
Lemma u_mem_wf_not_dev (P : uptd) (t : ptree) (mm : pamap) (a : Arch.pa) :
  u_mem_wf P t mm -> a ∈ (dom mm : gset Arch.pa) -> dev_addr a = false.
Proof.
  intros (_ & _ & _ & _ & _ & Hram & _) Ha. by apply addr_is_ram_not_dev, Hram.
Qed.

(* ---------------------------------------------------------------------- *)
(* THE DATA-PAGE COUNTERPART OF [u_mem_wf_owned].                          *)
(*                                                                        *)
(* [u_mem_wf_owned] answers the PTE side (an 8-byte slot that is one of    *)
(* the tree's own maps).  A data access is the other half, and the memory  *)
(* arms need it at EVERY width: a [k]-byte access at an aligned [va] whose *)
(* vpn is MAPPED lands inside the mapped page, and every offset of that    *)
(* page is in [ud_data P] by [udata_cov] -- which [u_mem_wf]'s data        *)
(* clause says is exactly the domain of the non-tree half of [mm].  The    *)
(* window step is [UserBits.pa_window] under [off_bound_div], i.e. the     *)
(* pure content of [UserMemPt.udata_read_word_g]'s coverage half, which    *)
(* until now was only available inside an Iris proof.                      *)
(* ---------------------------------------------------------------------- *)
Lemma u_walk_pa_window_wf (k : Z) (pte0 va : mword 64) (j : nat) :
  0 < k -> (k | 4096) ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  (j < Z.to_nat k)%nat ->
  pa_add (u_walk_pa pte0 va) j = u_walk_pa pte0 (add_vec_int va (Z.of_nat j)).
Proof.
  intros Hk Hdvd Hal Hj.
  pose proof (off_bound_div va k Hk Hdvd Hal) as Hb.
  exact (pa_window _ va j ltac:(lia)).
Qed.

Lemma u_mem_wf_owned_data (P : uptd) (t : ptree) (mm : pamap)
    (k : Z) (w va : mword 64) :
  0 < k -> (k | 4096) ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  u_mem_wf P t mm ->
  ud_um P !! svpn_of va = Some w ->
  bytes_owned mm (u_walk_pa w va) (Z.to_N k) = true.
Proof.
  intros Hk Hdvd Hal (md & _ & _ & Hmm & Hdm & _ & _ & Hwfm & _) Hl.
  apply bytes_owned_of_dom. intros j Hj.
  assert (Hjk : (j < Z.to_nat k)%nat) by lia.
  rewrite (u_walk_pa_window_wf k w va j Hk Hdvd Hal Hjk).
  apply elem_of_dom. rewrite Hmm.
  apply lookup_union_is_Some. right.
  apply (proj1 (Hdm _)).
  exact (u_data_pa_cov P (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hwfm Hl).
Qed.

(* and the device half at a data address, so an arm gets BOTH pure
   obligations from one [u_mem_wf] and one [udata_cov] hit *)
Lemma u_mem_wf_not_dev_data (P : uptd) (t : ptree) (mm : pamap)
    (w va : mword 64) :
  u_mem_wf P t mm ->
  ud_um P !! svpn_of va = Some w ->
  dev_addr (u_walk_pa w va) = false.
Proof.
  intros Hwf Hl.
  apply (u_mem_wf_not_dev P t mm _ Hwf).
  destruct Hwf as (md & _ & _ & Hmm & Hdm & _ & _ & Hwfm & _).
  apply elem_of_dom. rewrite Hmm. apply lookup_union_is_Some. right.
  apply (proj1 (Hdm _)). exact (u_data_pa_cov P (svpn_of va) w va Hwfm Hl).
Qed.

(* ===================================================================== *)
(* 3b. THE DATA PAGES -- AND A TYPE DIVIDE THAT HAS TO BE CROSSED.        *)
(*                                                                       *)
(* The hart's map is a [PtBytes.pamap]; the process's memory is keyed by *)
(* USER VIRTUAL ADDRESS ([UserPtTree.umem_own], a [gmap Z (bv 8)]).  The *)
(* two bridges below are the conversion, and they are BIJECTIVE on       *)
(* addresses: the va -> pa view is injective on the mapped vas           *)
(* ([uva_pa_inj], carried by [user_pt_inv]), and its image is exactly    *)
(* the covered pas ([u_data_pa]).                                        *)
(*                                                                       *)
(* WHY THE CONVERSION IS STATED WITH A PREDICATE AND NOT A [gset]: the   *)
(* two byte maps of this tree live at DIFFERENT [Countable Arch.pa]      *)
(* instances, and the difference is invisible at the printed syntax.     *)
(* [RiscvModelBytes] / [HartMemRun] (and hence [read_bytes],             *)
(* [bytes_own], [gen_heap_interp]) elaborate [gmap Arch.pa (bv 8)] with  *)
(* stdpp's [bv_countable]; [UserPtTree] imports [SailStdpp.Base] /       *)
(* [Values], where [Instances.Countable_mword] wins.  The two records    *)
(* differ in their [decode_encode] PROOF field, so the resulting [gmap]  *)
(* types are NOT convertible -- [exact] refuses them -- while both print *)
(* as [gmap Arch.pa (bv 8)].  The old [udata_own] bridges crossed the    *)
(* divide by a [list_to_map (map_to_list _)] round trip; the new ones do *)
(* not have to, because [UserPtTree.bigset_gather_reindex] is            *)
(* POLYMORPHIC in the address type and mentions the image only through   *)
(* [is_Some (m !! a)] and the predicate [u_data_pa] -- so each side      *)
(* elaborates at ITS OWN instance and nothing has to be transported.     *)
(* ===================================================================== *)

Section UserBytesData.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* THE PROCESS'S MEMORY AS THE HART'S BYTE MAP.  The CONTENTS survive
     (the two maps hold the same bytes, re-keyed); only the KEYING moves.
     Contents are dropped on the way in here because the accessor below
     re-establishes [umem_own] at a FRESH [M] on the way out -- which is
     what user execution is entitled to (arbitrary stores). *)
  Lemma umem_any_bytes (P : uptd) :
    uva_pa_inj P ->
    umem_any P -∗
    ∃ md : pamap, ⌜forall a : Arch.pa, u_data_pa P a <-> is_Some (md !! a)⌝ ∗
                  bytes_own md.
  Proof.
    intros Hinj. iIntros "H".
    rewrite umem_any_set.
    rewrite (bigset_gather_reindex (uva_pa P) (uva_dom P) (u_data_pa P)
               (fun (a : Arch.pa) (b : bv 8) =>
                  TsoCtx.ctx_phys_pointsto XI a (DfracOwn 1) b)
               (uva_dom_inj P Hinj) (u_data_pa_img P)).
    iDestruct "H" as (md) "[%Hdom Hmd]".
    iExists md. rewrite /bytes_own. iFrame "Hmd". done.
  Qed.

  Lemma umem_any_of_bytes (P : uptd) (md : pamap) :
    uva_pa_inj P ->
    (forall a : Arch.pa, u_data_pa P a <-> is_Some (md !! a)) ->
    bytes_own md -∗ umem_any P.
  Proof.
    intros Hinj Hdom. iIntros "Hmd".
    rewrite umem_any_set.
    rewrite (bigset_gather_reindex (uva_pa P) (uva_dom P) (u_data_pa P)
               (fun (a : Arch.pa) (b : bv 8) =>
                  TsoCtx.ctx_phys_pointsto XI a (DfracOwn 1) b)
               (uva_dom_inj P Hinj) (u_data_pa_img P)).
    iExists md. rewrite /bytes_own. iFrame "Hmd". done.
  Qed.

End UserBytesData.

(* ===================================================================== *)
(* 4. THE ACCESSOR.                                                       *)
(*                                                                       *)
(* [user_pt_inv] in, ONE byte map out -- plus the register cells, the     *)
(* persistent node claims, and a closing wand that takes a map back.      *)
(* This is the shape every memory-facing rule of the ported tier sits on: *)
(* the hart holds [bytes_own mm] across its whole cycle, each model call  *)
(* is one [swp_hmrun_of_exec] at [MState rs mm dev0_state], and the       *)
(* invariant is re-sealed once at the end.                                *)
(*                                                                       *)
(* WHAT THE CLOSING WAND ASKS FOR, and why each piece is unavoidable:     *)
(*   [u_mem_step]  -- the new map is a same-shaped tree's bytes plus      *)
(*                    arbitrary data bytes at the same domain, and the    *)
(*                    new tree still satisfies [upt_tree_spec].  That is  *)
(*                    the A/D absorption, and it is the caller's to       *)
(*                    discharge because only the walk knows which leaf    *)
(*                    it touched.                                         *)
(*   [tlb_ok_pt]   -- a fill installs an entry, so the TLB/tree agreement *)
(*                    is re-established by whoever filled it; the cell    *)
(*                    comes back at a FRESH value for the same reason     *)
(*                    [HartRunGen]'s fetch obligation lets the fetch land *)
(*                    on a different file.                                *)
(* Everything else -- the node claims, the satp facts, the pma clause --  *)
(* is carried across untouched.                                           *)
(* ===================================================================== *)

Section UserPtInvBytes.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the register cells [utlb_inv_pt] owns, as one bundle *)
  Definition upt_regs (P : uptd) (usatp : mword 64)
      (tlbvec : type_of_register tlb) : iProp Σ :=
    (satp ↦ᵣ usatp ∗ tlb ↦ᵣ tlbvec ∗ pmp_config (ud_root P))%I.

  (* ...and the pure facts about satp and the PMAs that ride with them *)
  Definition upt_satp_ok (P : uptd) (usatp : mword 64) : Prop :=
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) /\
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64))
      = (mword_of_int 0 : mword 16) /\
    autocast (T := mword)
      (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = ud_root P /\
    (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0).

  (* [user_pt_any], not [user_pt_inv M]: what a user cycle does to the
     process's memory is exactly "arbitrary bytes inside its own pages",
     which is what [u_mem_step]'s data half already says, so the accessor
     takes the memory quantified and hands it back quantified.  Pinning
     [M] across a step would owe every arm a statement about the bytes it
     wrote; that is the NEXT increment, and it belongs with the arms, not
     here. *)
  Lemma user_pt_inv_bytes (P : uptd) :
    user_pt_any P -∗
    ∃ (t : ptree) (mm : pamap) (usatp : mword 64)
      (tlbvec : type_of_register tlb),
      ⌜u_mem_wf P t mm⌝ ∗ ⌜upt_satp_ok P usatp⌝ ∗
      ⌜tlb_ok_pt (mword_of_int 0) t tlbvec⌝ ∗
      upt_regs P usatp tlbvec ∗ pt_claims 2 t ∗ bytes_own mm ∗
      (∀ (t' : ptree) (mm' : pamap) (tlbvec' : type_of_register tlb),
         ⌜u_mem_step P t t' mm mm'⌝ -∗
         ⌜tlb_ok_pt (mword_of_int 0) t' tlbvec'⌝ -∗
         upt_regs P usatp tlbvec' -∗ bytes_own mm' -∗ user_pt_any P).
  Proof.
    (* [iEval … in], not a bare [rewrite]: [user_pt_any P] occurs TWICE in
       this statement (premise and closing wand), and the wand's occurrence
       must stay folded. *)
    iIntros "Hup". iEval (rewrite user_pt_any_unfold) in "Hup".
    iDestruct "Hup" as "(Htlb & Hdata & %Hinj & %Hacc)".
    iDestruct "Htlb" as (usatp tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlbc & %Hok & %Hspec & %Hwfm &
        %Hpmaw & Htree & Hpmp)".
    iDestruct (umem_any_bytes P Hinj with "Hdata") as (md) "[%Hdm Hmd]".
    iDestruct (ptree_own_bytes with "Htree") as "(#Hc & %Hdisj & Hmt)".
    iDestruct (bytes_own_disj with "Hmt Hmd") as %Hdj.
    iAssert (bytes_own (ptree_bytes 2 t ∪ md)) with "[Hmt Hmd]" as "Hmm".
    { rewrite (bytes_own_union _ _ Hdj). iFrame. }
    iDestruct (bytes_own_ram with "Hmm") as %Hram.
    iExists t, (ptree_bytes 2 t ∪ md), usatp, tlbvec.
    iSplitR.
    { iPureIntro. exists md. split_and!.
      - exact Hdisj.
      - exact Hdj.
      - reflexivity.
      - exact Hdm.
      - exact Hram.
      - exact Hacc.
      - exact Hwfm.
      - exact Hspec. }
    iSplitR.
    { iPureIntro. rewrite /upt_satp_ok. split_and!;
        [ exact Hmode | exact Hasid | exact Hppn | exact Hpmaw ]. }
    iSplitR; [ iPureIntro; exact Hok |].
    rewrite /upt_regs. iFrame "Hsatp Htlbc Hpmp Hc Hmm".
    (* the closing wand *)
    iIntros (t' mm' tlbvec') "%Hstep %Hok' (Hsatp & Htlbc & Hpmp) Hmm'".
    destruct Hstep as (Hshape & Hspec' & md' & Hdj' & -> & Hdm').
    rewrite (bytes_own_union _ _ Hdj'). iDestruct "Hmm'" as "[Hmt' Hmd']".
    rewrite user_pt_any_unfold.
    iSplitR "Hmd'".
    - iApply (utlb_inv_pt_intro (ud_root P) (ud_tfp P) (ud_um P)
                usatp tlbvec' t' Hmode Hasid Hppn Hok' Hspec' Hwfm Hpmaw
                with "Hsatp Htlbc [Hmt'] Hpmp").
      iApply (ptree_own_of_bytes 2 t'
                (pt_maps_disj_shape 2 t t' Hshape Hdisj) with "[] Hmt'").
      by iApply (pt_claims_shape 2 t t' Hshape).
    - iSplitL "Hmd'".
      + iApply (umem_any_of_bytes P md' Hinj Hdm' with "Hmd'").
      + iPureIntro. split; [ exact Hinj | exact Hacc ].
  Qed.

End UserPtInvBytes.
