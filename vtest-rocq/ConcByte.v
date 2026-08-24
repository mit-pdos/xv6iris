(* ConcByte.v -- two harts racing on ADJACENT BYTES of ONE word.

   Source: tools/vtest/tests/conc_byte.S (`vtest: smp=2 repeat=100`).
   Capture: ConcByteGen.v.

   Hart 0 runs three rounds of `lbu; addi 1; sb` on byte 0 of RESULT+0x100,
   hart 1 the same on byte 1.  The accesses are disjoint, so the answer
   should be 0x0303 whatever the interleaving -- but only if BOTH machines
   treat a sub-word store as touching only its own bytes.  A machine that
   implemented `sb` as a read-modify-write of the containing word would
   false-share and lose one side's increments.

   QEMU says 0x0303 on all 100 runs -- ONE outcome, so this test pins the
   hardware's behaviour rather than exhibiting a race.  What makes it worth
   having is the other side: the model agrees under THREE interleavings,
   including [byte_interleaved], in which each hart is holding a loaded byte
   while the other stores -- exactly the shape that loses an update in
   conc_lost, which differs from this test only in racing on the SAME byte.
   So the two tests together separate "the model's memory is byte-granular"
   from "the model's memory just happens not to be raced hard enough".

   RESULT layout, mirroring tools/vtest/tests/conc_byte.S:
     +0x000  DONE          +0x100  W  -- byte 0 hart 0's count,
     +0x004  status = 1                  byte 1 hart 1's count
     +0x008  W read back by hart 0
                           +0x104  BAR0A  +0x108  BAR1A   pass-1 rendezvous
                           +0x10c  BAR0B  +0x110  BAR1B   pass-2 rendezvous
                           +0x114  PRIV0  +0x115  PRIV1   warm-up bytes
                           +0x118  DONE1  -- hart 1's loop is over *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VConc ConcByteGen.
Local Open Scope Z_scope.

Definition byte_g0 : gstate := g0 conc_byte_text.

(* ---------------------------------------------------------------------- *)
(* 1. Getting both harts to the racy loop -- the same shape as ConcLost.v, *)
(*    two instructions later because the prologue carries one more [li].   *)
(*    21 instructions from reset to the pass-1 rendezvous store, 24 to     *)
(*    fall through it, 33 more through the warm-up pass and the pass-2     *)
(*    rendezvous store, 3 to fall through that.                            *)
(* ---------------------------------------------------------------------- *)

Definition align : list citem :=
  [CCpu hart0 21; CCpu hart1 24; CCpu hart0 33; CCpu hart1 33; CCpu hart0 3].

(* The racing pass is 29 instructions: 2 of setup and then three rounds of
   `lbu; nop x4; addi; sb; addi; bnez`.  [3] leaves a hart holding a loaded
   byte, [6] carries it through the store. *)

Definition byte_h0_first : list citem := align ++ [CCpu hart0 29].
Definition byte_h1_first : list citem := align ++ [CCpu hart1 29].

(* THE ONE THAT MATTERS: in every round both harts read their byte before
   either writes, so both are inside the other's read-modify-write window.
   On a machine with word-granular sub-word stores this loses one side's
   count; here it does not. *)
Definition byte_interleaved : list citem := align ++
  [CCpu hart0 3; CCpu hart1 3; CCpu hart0 6; CCpu hart1 6;
   CCpu hart0 3; CCpu hart1 3; CCpu hart0 6; CCpu hart1 6;
   CCpu hart0 3; CCpu hart1 3; CCpu hart0 6; CCpu hart1 6].

Definition byte_schedules : list (list citem) :=
  [byte_h0_first; byte_h1_first; byte_interleaved].

(* ---------------------------------------------------------------------- *)
(* 2. THE TEST.  QEMU has ONE outcome; the model has the same one under    *)
(*    every interleaving, whole 4 KB region.                               *)
(* ---------------------------------------------------------------------- *)

Definition byte_expect : list (list Z) :=
  [conc_byte_qemu_result; conc_byte_qemu_result; conc_byte_qemu_result].

Lemma conc_byte_model_admits_all :
  cobs_all 20000 byte_schedules byte_g0 = byte_expect.
Proof. solve_vtest byte_expect. Qed.

(* ...and the answer really is both counts, 3 in each byte, not one of them
   overwritten.  (Read off the capture, so this costs nothing.) *)
Lemma conc_byte_both_survive : cap_word conc_byte_qemu_result 8 = 0x0303.
Proof. reflexivity. Qed.

Lemma conc_byte_qemu_deterministic : length conc_byte_qemu_results = 1%nat.
Proof. reflexivity. Qed.
