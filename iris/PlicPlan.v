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

     - the per-context PRIORITY THRESHOLD is left completely free (every
       32-bit value is a legal threshold, so there is nothing to maintain);
     - a per-context ENABLE word may only name interrupt sources this machine
       actually has -- the UART and the virtio disk.

   [plicinithart] writes exactly [(1 << uart_irq_id) | (1 << virtio_irq_id)],
   so its write lands inside the permitted set no matter what was there
   before.

   STATED OVER CONTEXTS AND WORDS, because that is what the device has: every
   context (M and S, [DevModel.plic_nctx] of them) and every word of its
   enable bitmap ([plic_nwords], the board's 96 sources) must name only real
   sources.  Both device sources are below 32, so words 1 and 2 must be
   ZERO -- which is what makes the plan say something about the sources the
   machine has but xv6 does not use, rather than nothing.  xv6 writes one
   word of one context per hart and leaves the rest at their reset zero. *)
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.definitions.
Require Import DevModel.
Import ListNotations.
Local Open Scope Z_scope.

(* the only enable bits the kernel ever intends to set, in the word they live
   in: both device sources are below 32, so word 0 carries them and every
   other word is permitted nothing at all *)
Definition plic_dev_irq_mask : Z :=
  Z.lor (Z.shiftl 1 (Z.of_N uart_irq_id)) (Z.shiftl 1 (Z.of_N virtio_irq_id)).

Definition plic_dev_irq_word (w : nat) : Z :=
  if Nat.eqb w 0 then plic_dev_irq_mask else 0.

Definition plic_senable_ok (w : nat) (word : bv 32) : Prop :=
  Z.land (bv_unsigned word) (plic_dev_irq_word w) = bv_unsigned word.

(* the kernel's PLIC plan: every context's enable bitmap names only real
   sources. *)
Definition plic_ok (p : plic_state) : Prop :=
  forall c w : nat, plic_senable_ok w (p_enable p c w).

(* The reset PLIC satisfies the plan: every S-context enable word is zero, and
   zero enables nothing (so a fortiori nothing outside the real sources).
   This is what lets a boot client allocate [plic_inv] over the machine a
   PowerOn hands it (claude-notes/design/crash.md). *)
Lemma plic_ok_plic0 : plic_ok plic0_state.
Proof.
  intros c w. unfold plic_senable_ok. cbn [p_enable plic0_state].
  destruct (Nat.eqb w 0); vm_compute; reflexivity.
Qed.

(* A hart that overwrites ONE WORD of ONE CONTEXT's bitmap with a value
   permitted in that word keeps the plan, whatever every other context and
   word holds -- this is the whole point of stating the plan pointwise. *)
Lemma plic_ok_wupd_enable (p : plic_state) (c wi : nat) (w : bv 32) :
  plic_ok p -> plic_senable_ok wi w ->
  plic_ok (PlicState (p_prio p) (p_pending p) (p_claimed p)
                     (wupd (p_enable p) c wi w) (p_thresh p)).
Proof.
  intros Hp Hw c' w'. cbn [p_enable]. unfold wupd.
  destruct (Nat.eqb c' c) eqn:Hc; cbn [andb].
  - destruct (Nat.eqb w' wi) eqn:Hw'; [ | apply Hp ].
    apply Nat.eqb_eq in Hw' as ->. exact Hw.
  - apply Hp.
Qed.

(* Writing a priority threshold touches no enable word. *)
Lemma plic_ok_hupd_thresh (p : plic_state) (h : nat) (w : bv 32) :
  plic_ok p ->
  plic_ok (PlicState (p_prio p) (p_pending p) (p_claimed p)
                     (p_enable p) (hupd (p_thresh p) h w)).
Proof. intros Hp c wi. exact (Hp c wi). Qed.

(* Writing a source priority touches no enable word. *)
Lemma plic_ok_nupd_prio (p : plic_state) (i : N) (w : bv 32) :
  plic_ok p ->
  plic_ok (PlicState (nupd (p_prio p) i w) (p_pending p) (p_claimed p)
                     (p_enable p) (p_thresh p)).
Proof. intros Hp c wi. exact (Hp c wi). Qed.

(* ...and a source-priority write is therefore ALWAYS admissible: an offset in
   the priority window (positive, below [4 * plic_nsrc], 4-aligned) makes
   [plic_write] take its first branch, which is defined for every state and
   only ever touches [p_prio] -- a field the plan says nothing about.  This is
   the exact shape an invariant-borrowing PLIC store leaf asks its caller for
   ("the write is defined and preserves [plic_ok] at EVERY admissible state"),
   and it is what discharges both of [plicinit]'s writes. *)
Lemma plic_write_prio_ok (p : plic_state) (off : Z) (i : N) (v : bv 32) :
  plic_prio_src off = Some i ->
  plic_ok p ->
  exists p', plic_write p off v = Some p' /\ plic_ok p'.
Proof.
  intros Hoff Hp. unfold plic_write. rewrite Hoff.
  (* source 0's register is hardwired zero, so that write is the identity;
     every other one lands in [p_prio], which the plan does not constrain *)
  destruct (i =? 0)%N.
  - exists p. split; [ reflexivity | exact Hp ].
  - eexists. split; [ reflexivity | ]. by apply plic_ok_nupd_prio.
Qed.

(* the gateway latching a pending source touches no enable word -- whichever
   of the machine's sources it was *)
Lemma plic_ok_latch (p p' : plic_state) (i : N) :
  plic_latch p i = Some p' -> plic_ok p -> plic_ok p'.
Proof.
  unfold plic_latch.
  destruct (negb (p_pending p i) && negb (p_claimed p i)); [ | discriminate ].
  intros Heq. injection Heq as <-. intros Hp c wi. exact (Hp c wi).
Qed.

(* the word [plicinithart] writes is permitted in word 0 (it IS the mask) *)
Lemma plic_senable_ok_mask : plic_senable_ok 0 (Z_to_bv 32 plic_dev_irq_mask).
Proof. unfold plic_senable_ok. vm_compute. reflexivity. Qed.

(* a reset PLIC (all enables clear) satisfies the plan, in any word *)
Lemma plic_senable_ok_zero (w : nat) : plic_senable_ok w (Z_to_bv 32 0).
Proof.
  unfold plic_senable_ok. destruct (Nat.eqb w 0); vm_compute; reflexivity.
Qed.

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
Lemma plic_fold_best (p : plic_state) (c : nat) :
  forall (l : list N) (acc : option N) (i : N),
    incl l plic_srcs ->
    (forall j, acc = Some j -> In j plic_srcs /\ plic_cand p c j = true) ->
    fold_left (fun best k =>
                 if plic_cand p c k then
                   match best with
                   | None => Some k
                   | Some j => if plic_better p k j then Some k else Some j
                   end
                 else best) l acc = Some i ->
    In i plic_srcs /\ plic_cand p c i = true.
Proof.
  induction l as [|k l IH]; intros acc i Hincl Hacc Hfold; cbn [fold_left] in Hfold.
  - exact (Hacc i Hfold).
  - eapply IH; [ intros x Hx; apply Hincl; right; exact Hx | | exact Hfold ].
    destruct (plic_cand p c k) eqn:Hk; [ | exact Hacc ].
    intros j Hj. destruct acc as [j0|].
    + destruct (plic_better p k j0); injection Hj as <-.
      * split; [ apply Hincl; left; reflexivity | exact Hk ].
      * exact (Hacc j0 eq_refl).
    + injection Hj as <-. split; [ apply Hincl; left; reflexivity | exact Hk ].
Qed.


Lemma plic_best_spec (p : plic_state) (c : nat) (i : N) :
  plic_best p c = Some i -> In i plic_srcs /\ plic_cand p c i = true.
Proof.
  unfold plic_best. intro H.
  refine (plic_fold_best p c plic_srcs None i (incl_refl _) _ H).
  intros j Hj. discriminate Hj.
Qed.

(* the plan, read off one enabled source: an enabled real source IS one of the
   machine's two.  [i] ranges over [plic_srcs] (1..95), and for each of those
   ids the WORD it lives in and the BIT within that word are concrete, so the
   bit test is decided by case analysis on the ninety-five ids -- including
   the sources in words 1 and 2, which the plan permits nothing in and which
   are therefore refuted by the same [vm_compute]. *)
Lemma plic_enabled_srcs (p : plic_state) (c : nat) (i : N) :
  plic_ok p -> In i plic_srcs -> plic_enabled p c i = true ->
  i = uart_irq_id \/ i = virtio_irq_id.
Proof.
  intros Hplan Hin Hen.
  assert (Hbit : Z.testbit (plic_dev_irq_word (plic_src_word i))
                           (plic_src_bit i) = true).
  { unfold plic_enabled in Hen. unfold plic_ok, plic_senable_ok in Hplan.
    rewrite <- (Hplan c (plic_src_word i)) in Hen. rewrite Z.land_spec in Hen.
    apply andb_prop in Hen as [_ Hen]. exact Hen. }
  vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]); try (exfalso; exact Hin);
    subst i; vm_compute in Hbit;
    first [ discriminate Hbit | left; reflexivity | right; reflexivity ].
Qed.

Lemma plic_claim_ret (p : plic_state) (c : nat) :
  plic_ok p -> plic_claim_ret_ok (fst (plic_claim p c)).
Proof.
  intro Hplan. unfold plic_claim.
  destruct (plic_best p c) as [i|] eqn:Hbest; cbn [fst]; [ | left; reflexivity ].
  destruct (plic_best_spec p c i Hbest) as [Hin Hcand].
  assert (Hen : plic_enabled p c i = true).
  { unfold plic_cand in Hcand.
    apply andb_prop in Hcand as [Hc _]. apply andb_prop in Hc as [_ Hc]. exact Hc. }
  destruct (plic_enabled_srcs p c i Hplan Hin Hen) as [-> | ->];
    [ right; left; reflexivity | right; right; reflexivity ].
Qed.

(* Claiming touches only pending/claimed, so the plan survives it. *)
Lemma plic_ok_claim (p : plic_state) (c : nat) :
  plic_ok p -> plic_ok (snd (plic_claim p c)).
Proof.
  intro Hplan. unfold plic_claim.
  destruct (plic_best p c); cbn [snd]; [ | exact Hplan ].
  intros c' w. cbn [p_enable]. exact (Hplan c' w).
Qed.

(* Completing touches only claimed, so it is a no-op as far as the plan is
   concerned -- which is the whole content of plic_complete's spec. *)
Lemma plic_ok_complete (p : plic_state) (i : N) :
  plic_ok p -> plic_ok (plic_complete p i).
Proof.
  intro Hplan. unfold plic_complete.
  destruct ((1 <=? Z.of_N i) && (Z.of_N i <? Z.of_nat plic_nsrc))%Z;
    [ | exact Hplan ].
  intros c w. cbn [p_enable]. exact (Hplan c w).
Qed.
