(* ConcAmoSched.v -- the INTERLEAVINGS for the multi-hart case, lifted from the
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

(* the uniform name VRunConc's generated case refers to *)
Definition schedules : list (list citem) := amo_schedules.
