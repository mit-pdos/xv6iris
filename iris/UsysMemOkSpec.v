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
(*   - sbrk: the row's [usys_sbrk_perm π π' szv szv'], and it is no longer *)
(*     a premise anybody has to conjure.  The dispatcher's own sbrk row    *)
(*     ([SpecSyscall.sysc_sbrk_ok]) now names the descriptor's move and    *)
(*     the dealloc run's count, so BOTH arms are derivable here:           *)
(*     [usys_sbrk_perm_grow] out of [perm_of_grow] plus                    *)
(*     [perm_of_uptd_ext_sz], and [usys_sbrk_perm_shrink] out of           *)
(*     [UserPerm.perm_of_del_run].  What the caller supplies instead is    *)
(*     the two facts [ProcInv.proc_priv] already carries about the ENTRY   *)
(*     state: [um_below] and [uint sz <= uvm_maxsz].                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap sets bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvLang RiscvPtsto.
Require Import ProcDefs.
Require Import UserPtTree ProcPtOwn.
Require Import SpecSyscall.
Require Import UserPerm UsysMemOk.
Require Import UmodeArith.
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
    (π π' : gmap (mword 27) uperm) (szv szv' : Z) :
  sysc_num V <> 7 -> sysc_num V <> 12 ->
  π' = π ->
  szv' = szv ->
  sysc_mem_ok V V' M M' ->
  usys_mem_ok (sysc_num V) (pv_tf V) r M π szv M' π' szv'.
Proof.
  intros Hne Hns Hp Hs H. unfold sysc_mem_ok in H. unfold usys_mem_ok, USYS_exec, USYS_sbrk.
  destruct (decide (sysc_num V = 7)); [ contradiction | ].
  destruct (decide (sysc_num V = 12)); [ contradiction | ].
  change usys_window with sysc_window.
  destruct (sysc_window (sysc_num V)); exact (conj H (conj Hp Hs)).
Qed.

(* sbrk: the dispatcher's row, read at the two sizes it is keyed by.  The
   permission half is the row's own relation, and it is now DERIVABLE from
   the same dispatcher row -- [usys_sbrk_perm_of_row] below. *)
Lemma sysc_mem_ok_sbrk_row (V V' : pprivate) (M M' : gmap Z (bv 8)) :
  sysc_num V = 12 ->
  sysc_mem_ok V V' M M' ->
  sysc_sbrk_ok (pv_upt V) (pv_upt V') (pv_sz V) (pv_sz V') M M'.
Proof.
  intros Hn H. unfold sysc_mem_ok in H. rewrite Hn in H.
  destruct (decide (12 = 7)) as [Hc | _]; [ discriminate Hc | ].
  destruct (decide (12 = 12)) as [_ | Hc]; [ exact H | exfalso; exact (Hc eq_refl) ].
Qed.

(* the IMAGE half is the dispatcher's row with the descriptor forgotten *)
Lemma usys_sbrk_img_of_row (P P' : uptd) (szv szv' : mword 64)
    (M M' : gmap Z (bv 8)) :
  sysc_sbrk_ok P P' szv szv' M M' -> usys_sbrk_img M M' szv szv'.
Proof.
  unfold sysc_sbrk_ok, usys_sbrk_img.
  destruct (decide (uint szv <= uint szv')%Z); intros [_ H]; exact H.
Qed.

Lemma sysc_mem_ok_usys_sbrk (V V' : pprivate) (M M' : gmap Z (bv 8)) (r : mword 64)
    (π π' : gmap (mword 27) uperm) :
  sysc_num V = 12 ->
  usys_sbrk_perm π π' (pv_sz V) (pv_sz V') ->
  sysc_mem_ok V V' M M' ->
  usys_mem_ok (sysc_num V) (pv_tf V) r M π (uint (pv_sz V))
              M' π' (uint (pv_sz V')).
Proof.
  intros Hn Hp H.
  pose proof (sysc_mem_ok_sbrk_row V V' M M' Hn H) as Hrow.
  unfold usys_mem_ok, USYS_exec, USYS_sbrk. rewrite Hn.
  destruct (decide (12 = 7)) as [Hc | _]; [ discriminate Hc | ].
  destruct (decide (12 = 12)) as [_ | Hc]; [ | exfalso; exact (Hc eq_refl) ].
  (* the row's sizes are NAMED now, so this is no longer an [exists]: the
     two [mword_of_int (uint ...)] round-trips are the only work left *)
  rewrite !moi_of_uint.
  split; [ exact (usys_sbrk_img_of_row _ _ _ _ _ _ Hrow) | exact Hp ].
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

(* ===================================================================== *)
(* THE PERMISSION HALF, DERIVED FROM THE DISPATCHER'S ROW.                 *)
(*                                                                         *)
(* This is what closes stage S8b: [usys_sbrk_perm] is no longer a premise  *)
(* the caller has to conjure, it is a CONSEQUENCE of what the dispatcher   *)
(* says the address space did, plus the two facts [ProcInv.proc_priv]      *)
(* carries about the entry state ([um_below] and the TRAPFRAME bound).     *)
(* ===================================================================== *)

(* on the way UP the "minus the mapped pages" caveat is VACUOUS: [um_below]
   puts every mapped page inside the OLD live region, so no newly-live page
   is one of them.  This is the table-free reading of [perm_of_grow]. *)
Lemma perm_of_grow_below (um : gmap (mword 27) (mword 64)) (szv szv' : mword 64) :
  um_below szv um ->
  (uint szv <= uint szv')%Z ->
  perm_of um (uint szv')
  = perm_of um (uint szv)
    ∪ gset_to_gmap uperm_rw (live_pages (uint szv') ∖ live_pages (uint szv)).
Proof.
  intros Hb Hle.
  assert (Hset : ((live_pages (uint szv') ∖ live_pages (uint szv)) ∖ dom um)
                 = (live_pages (uint szv') ∖ live_pages (uint szv))).
  { apply set_eq. intros p. rewrite !elem_of_difference. split.
    - intros [H _]. exact H.
    - intros [Hl' Hl]. split; [ exact (conj Hl' Hl) | ].
      intros Hd. exact (Hl (um_below_dom_live szv um Hb p Hd)). }
  rewrite (perm_of_grow um (uint szv) (uint szv') Hle), Hset. reflexivity.
Qed.

(* GROW.  The eager path really does map the run -- but at vmfault's own
   RW-user leaf inside the new size, which is exactly what
   [perm_of_uptd_ext_sz] needs to see that the projection did not notice. *)
Lemma usys_sbrk_perm_grow (P P' : uptd) (szv szv' : mword 64) :
  um_below szv (ud_um P) ->
  (uint szv <= uint szv')%Z ->
  uptd_ext_sz szv' P P' ->
  usys_sbrk_perm (perm_of (ud_um P) (uint szv))
                 (perm_of (ud_um P') (uint szv')) szv szv'.
Proof.
  intros Hb Hle Hext. unfold usys_sbrk_perm.
  destruct (decide (uint szv <= uint szv')%Z) as [_ | Hc];
    [ | exfalso; exact (Hc Hle) ].
  rewrite (perm_of_uptd_ext_sz szv' P P' Hext).
  exact (perm_of_grow_below (ud_um P) szv szv' Hb Hle).
Qed.

(* SHRINK.  [UserPerm.perm_of_del_run], at the descriptor tier. *)
Lemma usys_sbrk_perm_shrink (P : uptd) (szv szv' : mword 64) :
  um_below szv (ud_um P) ->
  (uint szv <= uvm_maxsz)%Z ->
  (uint szv' < uint szv)%Z ->
  usys_sbrk_perm (perm_of (ud_um P) (uint szv))
    (perm_of (ud_um (uptd_del_run P (svpn_of (pgroundup szv'))
                       (uvmd_np szv szv'))) (uint szv')) szv szv'.
Proof.
  intros Hb Hmax Hlt. unfold usys_sbrk_perm.
  destruct (decide (uint szv <= uint szv')%Z) as [Hc | _];
    [ exfalso; exact (Z.lt_irrefl _ (Z.lt_le_trans _ _ _ Hlt Hc)) | ].
  unfold uptd_del_run. cbn [ud_um].
  exact (perm_of_del_run (ud_um P) szv szv' Hb Hmax Hlt).
Qed.

(* THE ROW.  Both arms at once, out of the dispatcher's own sbrk row. *)
Lemma usys_sbrk_perm_of_row (P P' : uptd) (szv szv' : mword 64)
    (M M' : gmap Z (bv 8)) :
  um_below szv (ud_um P) ->
  (uint szv <= uvm_maxsz)%Z ->
  sysc_sbrk_ok P P' szv szv' M M' ->
  usys_sbrk_perm (perm_of (ud_um P) (uint szv))
                 (perm_of (ud_um P') (uint szv')) szv szv'.
Proof.
  intros Hb Hmax H. unfold sysc_sbrk_ok in H.
  destruct (decide (uint szv <= uint szv')%Z) as [Hle | Hgt].
  - destruct H as [Hext _].
    exact (usys_sbrk_perm_grow P P' szv szv' Hb Hle Hext).
  - destruct H as [Hp _]. rewrite Hp.
    assert (Hgt' : (uint szv' < uint szv)%Z).
    { destruct (Z.le_gt_cases (uint szv) (uint szv')) as [Hc | Hc];
        [ exfalso; exact (Hgt Hc) | exact Hc ]. }
    apply usys_sbrk_perm_shrink; [ exact Hb | exact Hmax | exact Hgt' ].
Qed.
