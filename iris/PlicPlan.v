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
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import DevModel.
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
