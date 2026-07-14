(* WpUserMemStep.v -- the spatial-composed user-mode step (WORKLIST).

   Goal: a dispatcher [user_step_holds_full] that discharges
   [user_step_obligation] WITHOUT the pure premise [Hclass : ∀ frame,
   ustep_case] of [wp_user_exec_v1] -- because [ustep_case] (a pure-Prop
   44-way disjunction) has NO home for data-page loads, stores, or
   atomics (they need mutable-memory ownership).  The frame ALREADY owns
   [user_data] (WpUserBase.user_frame), so the dispatcher can, per step,
   unpack it and route a memory word to the frame-decomposed spatial arm
   ([ustep_ld_data]/[ustep_sw]/...) while non-memory words reuse the
   existing classification arms.  See iris/CLAUDE.md ("The FULL user-mode
   WP") for the full plan.

   This file collects the reusable BRICKS that plumbing needs.

   (1) Value derivation.  The spatial load arms take the loaded value [v]
   plus [∀ j<N, dm !! pa_add paD j = Some (nth_byte v j)].  Since [v] must
   be READ from the frame's existential data map [dm] (it cannot sit in an
   outer pure premise), the dispatcher gathers it with [read_bytes]
   (RiscvModelBytes) once the window lies in [dom dm].
   [read_bytes_is_Some_of_dom] provides that gathering; [read_bytes_spec]
   then yields the byte-content premise.

   (2) Window peel/restore.  The store arms take the target window ALREADY
   peeled ([∗ list] j ∈ seq 0 N, pa_add paD j ↦ₘ nth_byte vold j) plus a
   restore wand.  [data_window_acc_gen] peels an N-cell window out of the
   frame-owned [[∗ map] a↦b ∈ dm, a↦ₘ b] and hands back a restore wand
   that rebuilds the map after a [write_bytes]; [NoDup_pa_window] supplies
   the window-address distinctness and [dom_write_bytes] shows the store
   leaves [dom dm] (hence [user_data]'s [dom = data]) intact. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions list list_monad.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import SmodePte.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* (1) Value derivation: [read_bytes] succeeds on an in-domain window.     *)
(* ---------------------------------------------------------------------- *)

(* [mapM f l] succeeds when every element does. *)
Lemma mapM_is_Some {A B} (f : A -> option B) (l : list A) :
  (forall x, x ∈ l -> is_Some (f x)) -> is_Some (mapM f l).
Proof.
  induction l as [|a l IH]; intros Hall.
  - eexists; reflexivity.
  - destruct (Hall a (elem_of_list_here _ _)) as [y Hy].
    destruct IH as [ys Hys].
    { intros x Hx. apply Hall. apply elem_of_list_further. exact Hx. }
    exists (y :: ys). simpl. rewrite Hy. simpl. rewrite Hys. reflexivity.
Qed.

(* If the whole [pa..pa+n) window lies in [dom mm], the little-endian
   gather succeeds -- so the dispatcher can define the loaded value as its
   [Some]-witness and feed [read_bytes_spec] to the spatial arm. *)
Lemma read_bytes_is_Some_of_dom (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N) :
  (forall j : nat, (N.of_nat j < n)%N -> is_Some (mm !! pa_add pa j)) ->
  is_Some (read_bytes mm pa n).
Proof.
  intros Hdom. unfold read_bytes.
  destruct (mapM (fun j : nat => mm !! pa_add pa j) (seq 0 (N.to_nat n))) as [bs|] eqn:Hm.
  - eexists; reflexivity.
  - exfalso.
    assert (Hsome : is_Some (mapM (fun j : nat => mm !! pa_add pa j) (seq 0 (N.to_nat n)))).
    { apply mapM_is_Some. intros x Hx. apply elem_of_seq in Hx. apply Hdom. lia. }
    rewrite Hm in Hsome. destruct Hsome; discriminate.
Qed.

(* ---------------------------------------------------------------------- *)
(* (2) Window peel/restore: address distinctness + domain preservation.    *)
(* ---------------------------------------------------------------------- *)

(* window addresses are pairwise distinct when the window does not wrap *)
Lemma pa_add_inj_nowrap (paD : Arch.pa) (n : nat) (j j' : nat) :
  (uint paD + Z.of_nat n <= 18446744073709551616)%Z ->
  (j < n)%nat -> (j' < n)%nat ->
  pa_add paD j = pa_add paD j' -> j = j'.
Proof.
  intros Hnw Hj Hj' Heq.
  assert (Huj : uint (pa_add paD j) = uint paD + Z.of_nat j) by (apply uint_pa_add; lia).
  assert (Huj' : uint (pa_add paD j') = uint paD + Z.of_nat j') by (apply uint_pa_add; lia).
  rewrite Heq in Huj. rewrite Huj' in Huj. lia.
Qed.

Lemma NoDup_pa_window (paD : Arch.pa) (n : nat) :
  (uint paD + Z.of_nat n <= 18446744073709551616)%Z ->
  NoDup ((pa_add paD) <$> (seq 0 n)).
Proof.
  intro Hnw. apply NoDup_fmap_2_strong.
  - intros x y Hx Hy Heq. apply elem_of_seq in Hx; apply elem_of_seq in Hy.
    apply (pa_add_inj_nowrap paD n); [lia|lia|lia|exact Heq].
  - apply NoDup_seq.
Qed.

(* gmap: deleting a key commutes past inserts of OTHER keys *)
Lemma foldr_insert_delete_comm (paD : Arch.pa) (g : nat -> bv 8)
    (k : Arch.pa) (l : list nat) (m : gmap Arch.pa (bv 8)) :
  k ∉ ((pa_add paD) <$> l) ->
  foldr (fun j acc => <[pa_add paD j := g j]> acc) (delete k m) l
  = delete k (foldr (fun j acc => <[pa_add paD j := g j]> acc) m l).
Proof.
  induction l as [|x xs IH]; intro Hk; simpl.
  - reflexivity.
  - rewrite fmap_cons in Hk. apply not_elem_of_cons in Hk as [Hne Hk].
    rewrite (IH Hk).
    symmetry. apply delete_insert_ne. exact Hne.
Qed.

(* inserting keys already present preserves the domain *)
Lemma dom_foldr_insert_indom (g : nat -> bv 8) (paD : Arch.pa)
    (l : list nat) (m : gmap Arch.pa (bv 8)) :
  (forall j, j ∈ l -> pa_add paD j ∈ dom m) ->
  dom (foldr (fun j acc => <[pa_add paD j := g j]> acc) m l) = dom m.
Proof.
  induction l as [|x xs IH]; intro Hin; simpl.
  - reflexivity.
  - assert (Hin' : forall j, j ∈ xs -> pa_add paD j ∈ dom m).
    { intros j Hj. apply Hin. apply elem_of_list_further. exact Hj. }
    rewrite dom_insert_L. rewrite (IH Hin').
    assert (Hx : pa_add paD x ∈ dom m) by (apply Hin; apply elem_of_list_here).
    set_solver.
Qed.

Lemma dom_write_bytes {k : N} (m : gmap Arch.pa (bv 8)) (paD : Arch.pa) (n : N) (v : bv k) :
  (forall j : nat, (N.of_nat j < n)%N -> pa_add paD j ∈ dom m) ->
  dom (write_bytes m paD n v) = dom m.
Proof.
  intro Hin. unfold write_bytes. apply dom_foldr_insert_indom.
  intros j Hj. apply elem_of_seq in Hj. apply Hin. lia.
Qed.

Section peel.
  Context `{!riscvGS Σ}.

  (* Peel the [pa_add paD 0 .. paD (|l|-1)] cells out of a frame-owned byte
     map, keeping a restore wand.  [fold_new] is chosen by the caller at
     restore time (for a store: [fun j => nth_byte vNew j]); the rebuilt map
     is exactly [foldr insert m l], i.e. [write_bytes] over [seq 0 N]. *)
  Lemma data_window_acc_gen (paD : Arch.pa) (l : list nat)
      (fold_old : nat -> bv 8) (m : gmap Arch.pa (bv 8)) :
    NoDup ((pa_add paD) <$> l) ->
    (forall j, j ∈ l -> m !! pa_add paD j = Some (fold_old j)) ->
    ⊢@{iPropI Σ}
      ([∗ map] a↦b ∈ m, a ↦ₘ b) -∗
      ([∗ list] j ∈ l, pa_add paD j ↦ₘ fold_old j) ∗
      (∀ fold_new : nat -> bv 8,
        ([∗ list] j ∈ l, pa_add paD j ↦ₘ fold_new j) -∗
        [∗ map] a↦b ∈ (foldr (fun j acc => <[pa_add paD j := fold_new j]> acc) m l), a↦ₘ b).
  Proof.
    revert m. induction l as [|x xs IH]; intros m Hnd Hcont.
    - iIntros "Hm". iSplitR "Hm".
      { done. }
      iIntros (fn) "_". simpl. iFrame.
    - rewrite fmap_cons in Hnd. apply NoDup_cons in Hnd as [Hxni Hnd].
      assert (Hmx : m !! pa_add paD x = Some (fold_old x))
        by (apply Hcont; apply elem_of_list_here).
      assert (Hcont' : forall j, j ∈ xs ->
                 delete (pa_add paD x) m !! pa_add paD j = Some (fold_old j)).
      { intros j Hj.
        assert (Hne : pa_add paD x ≠ pa_add paD j).
        { intro Hc. apply Hxni. rewrite Hc. apply elem_of_list_fmap.
          exists j. split; [reflexivity|exact Hj]. }
        rewrite (lookup_delete_ne _ _ _ Hne). apply Hcont.
        apply elem_of_list_further. exact Hj. }
      iIntros "Hm".
      iDestruct (big_sepM_delete _ _ _ _ Hmx with "Hm") as "[Hx Hrest]".
      iDestruct (IH (delete (pa_add paD x) m) Hnd Hcont' with "Hrest") as "[Hwin Hback]".
      simpl. iSplitL "Hx Hwin".
      { iFrame. }
      iIntros (fn) "[Hxn Hwn]".
      iDestruct ("Hback" $! fn with "Hwn") as "Hmap".
      cbn [foldr].
      iApply big_sepM_insert_delete.
      iFrame "Hxn".
      rewrite (foldr_insert_delete_comm paD fn (pa_add paD x) xs m Hxni).
      iFrame "Hmap".
  Qed.
End peel.
