(* ConcByteSched.v -- the INTERLEAVINGS for the multi-hart case, lifted from the
   retired hand-written test.

   One schedule per outcome the platform observed, in the order the capture
   lists them.  This is the part of a race that cannot be generated: which
   interleaving reproduces which outcome is the thing a human works out.
   Everything else about the run -- the image, the observations, the
   comparison -- is generated; see VRunConc.v. *)
From Stdlib Require Import List ZArith.
From stdpp Require Import base list.
Import ListNotations.
Require Import VTest VConc.
Local Open Scope Z_scope.


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

(* the uniform name VRunConc's generated case refers to *)
Definition schedules : list (list citem) := byte_schedules.
