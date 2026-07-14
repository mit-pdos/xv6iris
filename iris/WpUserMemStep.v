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

   FIRST BRICK (this file): the value-derivation helpers.  The spatial
   load arms take the loaded value [v] plus the byte-content premise
   [∀ j<N, dm !! pa_add paD j = Some (nth_byte v j)].  Since [v] must be
   READ from the frame's existential data map [dm] (it cannot sit in an
   outer pure premise), the dispatcher gathers it with [read_bytes]
   (RiscvModelBytes) once the window is known to lie in [dom dm].
   [read_bytes_is_Some_of_dom] provides that gathering; [read_bytes_spec]
   (already in RiscvModelBytes) then yields the byte-content premise. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions list_monad.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Local Open Scope Z_scope.

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
