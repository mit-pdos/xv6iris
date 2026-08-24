(* ConcAmo.v -- the lost update, done CORRECTLY: `amoadd.w`.

   Source: tools/vtest/tests/conc_amo.S (`vtest: smp=2 repeat=40`).
   Capture: ConcAmoGen.v.

   Two harts, four `amoadd.w` each on RESULT+0x100.  QEMU answers 8 on all
   40 runs and the model answers 8 under every interleaving below -- the
   point being the contrast with ConcLost.v, which is the same race with the
   read-modify-write spelled out and which QEMU answers 4, 3 or 2 to.

   WHAT THIS CORRECTS.  VConc.v's header says "[exec] treats the reservation
   outcomes as stuck ... An AMO-based test will get [VStuck]; keep tests to
   plain loads and stores until that changes."  That is not what happens:
   [exec (riscv_step false)] runs `amoadd.w` and hands back a state with the
   counter incremented, and this whole two-hart program runs to the DONE
   flag on the model.  `lr.w` executes as well.  The instruction that is
   actually out of reach is `sc.w`: a single `sc.w` did not come back from
   [vm_compute] in 110 seconds, where the 16 instructions before it took
   3.1 seconds together.  So the limitation is real but it is narrower and
   of a different kind than the header says -- not a missing transition that
   fails fast, but an evaluation that does not come back, which is why there
   is no lemma about it here: a test file that cannot be compiled is not a
   test.  An earlier version of conc_amo.S had hart 1 use an `lr.w`/`sc.w`
   retry loop and had to be abandoned for exactly that reason.

   THE ATOMICITY CLAIM IS WEAK, deliberately.  [CCpu c n] steps whole
   instructions, so no schedule expressible here can split an `amoadd.w`;
   that its result is 8 under every interleaving therefore says the model
   COMPUTES the read-modify-write correctly, not that it is indivisible
   against a finer-grained stepper.  VConc.v's header makes the same point
   about [prim_step] in general.

   RESULT layout, mirroring tools/vtest/tests/conc_amo.S:
     +0x000  DONE          +0x100  CTR  -- the shared counter
     +0x004  status = 1    +0x104  DONE1
     +0x008  CTR read back by hart 0 = 8 *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VConc ConcAmoGen.
Local Open Scope Z_scope.

Definition amo_g0 : gstate := g0 conc_amo_text.

(* No rendezvous is needed and none is in the program: the answer does not
   depend on the interleaving.  Both harts take 11 instructions from reset
   into their body and 19 more through four rounds of `li; amoadd; addi;
   bnez`, so 30 runs one hart's whole loop; 16 stops it just after its FIRST
   `amoadd`, and 4 is one further round. *)

Definition amo_h0_first : list citem := [CCpu hart0 30].
Definition amo_h1_first : list citem := [CCpu hart1 30].

(* round by round, alternating: each hart's amoadd lands between the other's *)
Definition amo_interleaved : list citem :=
  [CCpu hart0 16; CCpu hart1 16; CCpu hart0 4; CCpu hart1 4;
   CCpu hart0 4;  CCpu hart1 4;  CCpu hart0 4; CCpu hart1 4].

Definition amo_schedules : list (list citem) :=
  [amo_h0_first; amo_h1_first; amo_interleaved].

Definition amo_expect : list (list Z) :=
  [conc_amo_qemu_result; conc_amo_qemu_result; conc_amo_qemu_result].

Lemma conc_amo_model_admits_all :
  cobs_all 20000 amo_schedules amo_g0 = amo_expect.
Proof. solve_vtest amo_expect. Qed.

(* nothing is lost, unlike conc_lost: 2 * NITER *)
Lemma conc_amo_nothing_lost : cap_word conc_amo_qemu_result 8 = 8.
Proof. reflexivity. Qed.

Lemma conc_amo_qemu_deterministic : length conc_amo_qemu_results = 1%nat.
Proof. reflexivity. Qed.
