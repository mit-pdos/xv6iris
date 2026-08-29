(* ===================================================================== *)
(* UsysMemOkSpec.v -- [UsysMemOk.usys_mem_ok] IS [SpecSyscall.sysc_mem_ok] *)
(* read on the trapframe word list: the lemmas that let the kernel        *)
(* discharge the user-side table from the dispatcher's own post           *)
(* (milestone J).  Above SpecSyscall.v on purpose; nothing below it may   *)
(* import this file.                                                      *)
(*                                                                        *)
(* THE PERMISSION-MAP HALF.  The user-side table now also says how the    *)
(* permission view moves.  The kernel's [sysc_mem_ok] is about the IMAGE  *)
(* only, so each bridge takes the permission fact it needs as a PREMISE:  *)
(*   - every entry but exec and sbrk: the projection is UNCHANGED         *)
(*     ([perm_of (pv_upt V') (pv_sz V') = perm_of (pv_upt V) (pv_sz V)]) -- *)
(*     which is the kernel's to show from each arm's [P' = P] / [sz' = sz] *)
(*     (the sixteen quiet entries and the four windows touch neither);    *)
(*   - sbrk: the row's [usys_sbrk_perm π π'], with [perm_of_grow] proving  *)
(*     the GROW arm's shape from [growproc_ok]'s own facts (table          *)
(*     unchanged, size up) and the shrink arm left as the premise it is   *)
(*     -- its exact page set is [uvmdealloc]'s [um_del_run] window, which  *)
(*     [sysc_mem_ok] does not carry (see the project file: the kernel's   *)
(*     spec would have to expose the run to close it here).               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap sets bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvLang.
Require Import ProcGeom ProcDefs.
Require Import UserPtTree ProcPtOwn.
Require Import SpecSyscall.
Require Import UserPerm UsysMemOk.
Local Open Scope Z_scope.

(* the number the dispatcher reads is the number the table is keyed by *)
Lemma sysc_num_usys (V : pprivate) : sysc_num V = usys_num (pv_tf V).
Proof. reflexivity. Qed.

(* Every entry but exec and sbrk: the kernel's table implies the user's, at
   any return value, given the permission view did not move.  exec is
   excluded because its success arm never returns to this WP at all (the
   new program's WP is a kernel mint), and its failure arm's [r = -1] is
   the dispatcher's return-value fact, which [sysc_mem_ok] does not carry. *)
Lemma sysc_mem_ok_usys (V V' : pprivate) (M M' : gmap Z (bv 8)) (r : mword 64)
    (π π' : gmap (mword 27) uperm) :
  sysc_num V <> 7 -> sysc_num V <> 12 ->
  π' = π ->
  sysc_mem_ok V V' M M' ->
  usys_mem_ok (sysc_num V) (pv_tf V) r M π M' π'.
Proof.
  intros Hne Hns Hp H. unfold sysc_mem_ok in H. unfold usys_mem_ok, USYS_exec, USYS_sbrk.
  destruct (decide (sysc_num V = 7)); [ contradiction | ].
  destruct (decide (sysc_num V = 12)); [ contradiction | ].
  change usys_window with sysc_window.
  destruct (sysc_window (sysc_num V)); exact (conj H Hp).
Qed.

(* sbrk: the image half is the kernel's; the permission half is the row's
   own relation, supplied by the caller (see the header) *)
Lemma sysc_mem_ok_usys_sbrk (V V' : pprivate) (M M' : gmap Z (bv 8)) (r : mword 64)
    (π π' : gmap (mword 27) uperm) :
  sysc_num V = 12 ->
  usys_sbrk_perm π π' ->
  sysc_mem_ok V V' M M' ->
  usys_mem_ok (sysc_num V) (pv_tf V) r M π M' π'.
Proof.
  intros Hn Hp H. unfold sysc_mem_ok in H. unfold usys_mem_ok, USYS_exec, USYS_sbrk.
  rewrite Hn in H |- *.
  destruct (decide (12 = 7)) as [Hc | _]; [ discriminate Hc | ].
  destruct (decide (12 = 12)) as [_ | Hc]; [ | exfalso; exact (Hc eq_refl) ].
  split; [ exists (pv_sz V'); exact H | exact Hp ].
Qed.

(* ===================================================================== *)
(* The GROW arm's permission shape, from the kernel's facts: the table is  *)
(* the same and the size went up, so the projection gained exactly the     *)
(* newly-live pages at RW -- the [usys_sbrk_perm] grow disjunct.           *)
(* ===================================================================== *)

Lemma live_pages_mono (sz sz' : Z) :
  sz <= sz' -> live_pages sz ⊆ live_pages sz'.
Proof.
  intros Hle p. unfold live_pages. rewrite !elem_of_list_to_set, !elem_of_list_fmap.
  intros (k & -> & Hk). exists k. split; [ reflexivity | ].
  apply elem_of_seqZ in Hk. apply elem_of_seqZ.
  pose proof (UserPtTree.pgroundup_mono sz sz' Hle) as Hm.
  split; [ lia | ].
  apply Z.lt_le_trans with (UserPtTree.pgroundup sz / 4096); [ lia | ].
  apply Z.div_le_mono; lia.
Qed.

(* [UserPtTree.gset_to_gmap_union_Z] at the page type *)
Lemma gset_to_gmap_union_p {A : Type} (c : A) (X Y : gset (mword 27)) :
  gset_to_gmap c (X ∪ Y) = gset_to_gmap c X ∪ gset_to_gmap c Y.
Proof.
  apply map_eq. intros a.
  destruct (decide (a ∈ X)) as [HX | HX].
  - assert (Hl : gset_to_gmap c (X ∪ Y) !! a = Some c).
    { apply lookup_gset_to_gmap_Some.
      split; [apply elem_of_union; by left | reflexivity]. }
    rewrite Hl. symmetry.
    apply (lookup_union_Some_l (gset_to_gmap c X) (gset_to_gmap c Y) a c).
    apply lookup_gset_to_gmap_Some. split; [exact HX | reflexivity].
  - rewrite (lookup_union_r (gset_to_gmap c X) (gset_to_gmap c Y) a);
      [| apply lookup_gset_to_gmap_None; exact HX].
    destruct (decide (a ∈ Y)) as [HY | HY].
    + assert (Hl : gset_to_gmap c (X ∪ Y) !! a = Some c).
      { apply lookup_gset_to_gmap_Some.
        split; [apply elem_of_union; by right | reflexivity]. }
      rewrite Hl. symmetry.
      apply lookup_gset_to_gmap_Some. split; [exact HY | reflexivity].
    + assert (Hl : gset_to_gmap c (X ∪ Y) !! a = None).
      { apply lookup_gset_to_gmap_None.
        intros Hin. apply elem_of_union in Hin as [Hc | Hc];
          [exact (HX Hc) | exact (HY Hc)]. }
      rewrite Hl. symmetry.
      apply lookup_gset_to_gmap_None. exact HY.
Qed.

Lemma perm_of_grow (um : gmap (mword 27) (mword 64)) (sz sz' : Z) :
  sz <= sz' ->
  perm_of um sz'
  = perm_of um sz ∪ gset_to_gmap uperm_rw ((live_pages sz' ∖ live_pages sz) ∖ dom um).
Proof.
  intros Hle. unfold perm_of, perm_fill.
  rewrite <- map_union_assoc. f_equal.
  rewrite <- gset_to_gmap_union_p. f_equal.
  apply set_eq. intros p.
  rewrite elem_of_union, !elem_of_difference.
  pose proof (live_pages_mono sz sz' Hle p) as Hm.
  split.
  - intros [Hl' Hn].
    destruct (decide (p ∈ live_pages sz)) as [Hl | Hl].
    + left. exact (conj Hl Hn).
    + right. exact (conj (conj Hl' Hl) Hn).
  - intros [[Hl Hn] | [[Hl' _] Hn]].
    + exact (conj (Hm Hl) Hn).
    + exact (conj Hl' Hn).
Qed.

Lemma usys_sbrk_perm_grow (um : gmap (mword 27) (mword 64)) (sz sz' : Z) :
  sz <= sz' -> usys_sbrk_perm (perm_of um sz) (perm_of um sz').
Proof.
  intros Hle. right. left.
  exists ((live_pages sz' ∖ live_pages sz) ∖ dom um).
  exact (perm_of_grow um sz sz' Hle).
Qed.
