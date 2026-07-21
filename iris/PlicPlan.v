(* PlicPlan.v -- the KERNEL's plan for the PLIC, as a pure predicate on the
   device model's [plic_state].

   This is software, not hardware: the device model (DevModel.v) says what the
   PLIC *does*, and says nothing about which of its many legal configurations
   xv6 intends to put it in.  This file says what xv6 intends, and it is what
   the device invariant ([dev_inv_body], WpUart.v) maintains.

   [plicinithart] runs CONCURRENTLY on every hart, so no hart can own the whole
   PLIC state across its two MMIO writes: the shared [plic_frag] half lives in
   the device invariant and a hart borrows it by opening that invariant around
   each (atomic) write.  What survives is therefore not a hart's exact context
   but the invariant, and the invariant has to be weak enough that a hart can
   re-establish it from its OWN two writes alone, knowing nothing about what
   the other harts have written.  Hence:

     - the per-hart S-context PRIORITY THRESHOLD is left completely free (every
       32-bit value is a legal threshold, so there is nothing to maintain);
     - the per-hart S-context ENABLE word may only name interrupt sources this
       machine actually has -- the UART and the virtio disk.

   [plicinithart] writes exactly [(1 << uart_irq_id) | (1 << virtio_irq_id)],
   so its write lands inside the permitted set no matter what was there
   before. *)
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.definitions.
Require Import DevModel.
Import ListNotations.
Local Open Scope Z_scope.

(* the only S-context enable bits the kernel ever intends to set *)
Definition plic_dev_irq_mask : Z :=
  Z.lor (Z.shiftl 1 (Z.of_N uart_irq_id)) (Z.shiftl 1 (Z.of_N virtio_irq_id)).

Definition plic_senable_ok (w : bv 32) : Prop :=
  Z.land (bv_unsigned w) plic_dev_irq_mask = bv_unsigned w.

(* the kernel's PLIC plan: every hart's S-context enables only real sources. *)
Definition plic_ok (p : plic_state) : Prop :=
  forall h : nat, plic_senable_ok (p_enable p h).

(* A hart that overwrites its OWN enable word with a permitted value keeps the
   plan, whatever the other harts' words are -- this is the whole point of
   stating the plan per hart. *)
Lemma plic_ok_hupd_enable (p : plic_state) (h : nat) (w : bv 32) :
  plic_ok p -> plic_senable_ok w ->
  plic_ok (PlicState (p_prio p) (p_pending p) (p_claimed p)
                     (hupd (p_enable p) h w) (p_thresh p)).
Proof.
  intros Hp Hw k. cbn [p_enable]. unfold hupd.
  destruct (Nat.eqb k h); [ exact Hw | apply Hp ].
Qed.

(* Writing a priority threshold touches no enable word. *)
Lemma plic_ok_hupd_thresh (p : plic_state) (h : nat) (w : bv 32) :
  plic_ok p ->
  plic_ok (PlicState (p_prio p) (p_pending p) (p_claimed p)
                     (p_enable p) (hupd (p_thresh p) h w)).
Proof. intros Hp k. exact (Hp k). Qed.

(* Writing a source priority touches no enable word. *)
Lemma plic_ok_nupd_prio (p : plic_state) (i : N) (w : bv 32) :
  plic_ok p ->
  plic_ok (PlicState (nupd (p_prio p) i w) (p_pending p) (p_claimed p)
                     (p_enable p) (p_thresh p)).
Proof. intros Hp k. exact (Hp k). Qed.

(* the gateway latching a pending source touches no enable word *)
Lemma plic_ok_latch (p p' : plic_state) :
  plic_latch p = Some p' -> plic_ok p -> plic_ok p'.
Proof.
  unfold plic_latch.
  destruct (negb (p_pending p uart_irq_id) && negb (p_claimed p uart_irq_id));
    [ | discriminate ].
  intros Heq. injection Heq as <-. intros Hp k. exact (Hp k).
Qed.

(* the word [plicinithart] writes is permitted (it IS the mask) *)
Lemma plic_senable_ok_mask : plic_senable_ok (Z_to_bv 32 plic_dev_irq_mask).
Proof. unfold plic_senable_ok. vm_compute. reflexivity. Qed.

(* a reset PLIC (all enables clear) satisfies the plan *)
Lemma plic_senable_ok_zero : plic_senable_ok (Z_to_bv 32 0).
Proof. unfold plic_senable_ok. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  What the plan buys the CLAIM/COMPLETE pair.                           *)
(* ===================================================================== *)

(* A claim read returns the id of the source it took, or 0 for "nothing to
   serve".  Under the plan the only source a hart's context can ever have
   enabled is one of the machine's two, so those are the only ids a claim can
   hand back -- which is exactly what lets [devintr]'s three-way branch on the
   result be exhaustive. *)
Definition plic_claim_ret_ok (v : bv 32) : Prop :=
  v = Z_to_bv 32 0 \/
  v = Z_to_bv 32 (Z.of_N uart_irq_id) \/
  v = Z_to_bv 32 (Z.of_N virtio_irq_id).

(* [plic_best] is a fold that only ever returns an element of the list it
   folded over, and only a candidate one.  Generalised over the accumulator so
   the induction goes through. *)
Lemma plic_fold_best (p : plic_state) (h : nat) :
  forall (l : list N) (acc : option N) (i : N),
    incl l plic_srcs ->
    (forall j, acc = Some j -> In j plic_srcs /\ plic_cand p h j = true) ->
    fold_left (fun best k =>
                 if plic_cand p h k then
                   match best with
                   | None => Some k
                   | Some j => if plic_better p k j then Some k else Some j
                   end
                 else best) l acc = Some i ->
    In i plic_srcs /\ plic_cand p h i = true.
Proof.
  induction l as [|k l IH]; intros acc i Hincl Hacc Hfold; cbn [fold_left] in Hfold.
  - exact (Hacc i Hfold).
  - eapply IH; [ intros x Hx; apply Hincl; right; exact Hx | | exact Hfold ].
    destruct (plic_cand p h k) eqn:Hk; [ | exact Hacc ].
    intros j Hj. destruct acc as [j0|].
    + destruct (plic_better p k j0); injection Hj as <-.
      * split; [ apply Hincl; left; reflexivity | exact Hk ].
      * exact (Hacc j0 eq_refl).
    + injection Hj as <-. split; [ apply Hincl; left; reflexivity | exact Hk ].
Qed.


Lemma plic_best_spec (p : plic_state) (h : nat) (i : N) :
  plic_best p h = Some i -> In i plic_srcs /\ plic_cand p h i = true.
Proof.
  unfold plic_best. intro H.
  refine (plic_fold_best p h plic_srcs None i (incl_refl _) _ H).
  intros j Hj. discriminate Hj.
Qed.

(* the plan, read off one enabled source: an enabled real source IS one of the
   machine's two.  [i] ranges over [plic_srcs] (1..31), so the bit test is
   decided by case analysis on the thirty-one concrete ids. *)
Lemma plic_enabled_srcs (p : plic_state) (h : nat) (i : N) :
  plic_ok p -> In i plic_srcs -> plic_enabled p h i = true ->
  i = uart_irq_id \/ i = virtio_irq_id.
Proof.
  intros Hplan Hin Hen.
  assert (Hbit : Z.testbit plic_dev_irq_mask (Z.of_N i) = true).
  { unfold plic_enabled in Hen. unfold plic_ok, plic_senable_ok in Hplan.
    rewrite <- (Hplan h) in Hen. rewrite Z.land_spec in Hen.
    apply andb_prop in Hen as [_ Hen]. exact Hen. }
  vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]); try (exfalso; exact Hin);
    subst i; vm_compute in Hbit;
    first [ discriminate Hbit | left; reflexivity | right; reflexivity ].
Qed.

Lemma plic_claim_ret (p : plic_state) (h : nat) :
  plic_ok p -> plic_claim_ret_ok (fst (plic_claim p h)).
Proof.
  intro Hplan. unfold plic_claim.
  destruct (plic_best p h) as [i|] eqn:Hbest; cbn [fst]; [ | left; reflexivity ].
  destruct (plic_best_spec p h i Hbest) as [Hin Hcand].
  assert (Hen : plic_enabled p h i = true).
  { unfold plic_cand in Hcand.
    apply andb_prop in Hcand as [Hc _]. apply andb_prop in Hc as [_ Hc]. exact Hc. }
  destruct (plic_enabled_srcs p h i Hplan Hin Hen) as [-> | ->];
    [ right; left; reflexivity | right; right; reflexivity ].
Qed.

(* Claiming touches only pending/claimed, so the plan survives it. *)
Lemma plic_ok_claim (p : plic_state) (h : nat) :
  plic_ok p -> plic_ok (snd (plic_claim p h)).
Proof.
  intro Hplan. unfold plic_claim.
  destruct (plic_best p h); cbn [snd]; [ | exact Hplan ].
  intro k. cbn [p_enable]. exact (Hplan k).
Qed.

(* Completing touches only claimed, so it is a no-op as far as the plan is
   concerned -- which is the whole content of plic_complete's spec. *)
Lemma plic_ok_complete (p : plic_state) (i : N) :
  plic_ok p -> plic_ok (plic_complete p i).
Proof.
  intro Hplan. unfold plic_complete.
  destruct ((1 <=? Z.of_N i) && (Z.of_N i <? Z.of_nat plic_nsrc))%Z;
    [ | exact Hplan ].
  intro k. cbn [p_enable]. exact (Hplan k).
Qed.
