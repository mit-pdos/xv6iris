(* ConcLostSched.v -- the INTERLEAVINGS for the multi-hart case, lifted from the
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
(* 1. Getting both harts to the racy loop.                                 *)
(*                                                                         *)
(*    Instruction counts off `riscv64-linux-gnu-objdump -d`.  Both harts    *)
(*    take exactly 20 instructions from reset to the store that publishes   *)
(*    their pass-1 rendezvous flag (10 of vtest.S's dispatch, 6 of their    *)
(*    own prologue, 4 of <pass>), and the two bodies are instruction-for-   *)
(*    instruction identical from there on, which is why the same counts     *)
(*    work for both.                                                       *)
(*                                                                         *)
(*      20  hart 0 arrives at rendezvous A                                  *)
(*      23  hart 1 arrives, sees hart 0, and falls through the spin         *)
(*      33  hart 0 falls through (3) and runs the WARM-UP pass (30),        *)
(*          ending on the store that publishes rendezvous B                 *)
(*      33  hart 1 does the same and then falls through rendezvous B        *)
(*       3  hart 0 falls through rendezvous B                               *)
(*                                                                         *)
(*    Both harts are now at 0x80000094, the head of the racing pass, with   *)
(*    the counter still 0 -- the warm-up rounds went to their own PRIVate   *)
(*    words.                                                               *)
(* ---------------------------------------------------------------------- *)

Definition align : list citem :=
  [CCpu hart0 20; CCpu hart1 23; CCpu hart0 33; CCpu hart1 33; CCpu hart0 3].

(* The racing pass, per hart, is 22 instructions:                           *)
(*     2  set up the pointer and the round counter                          *)
(*     1  LOAD          round 1                                             *)
(*     5  four nops and the add                                             *)
(*     1  STORE         round 1                                             *)
(*     2  decrement and loop back                                           *)
(*     1  LOAD          round 2                                             *)
(*     5  four nops and the add                                             *)
(*     1  STORE         round 2                                             *)
(*     4  fall out of the loop and out of <pass>                            *)
(* so [3] leaves a hart holding a loaded value, [6] carries it to the store *)
(* inclusive, [3] carries it to the next round's load, and [11] runs a hart *)
(* from just after a store to the end of the pass.                          *)

(* BOTH ROUNDS COLLIDE.  Each hart reads before the other writes, twice, so
   the counter ends at 2 -- the floor: a hart's second round cannot read
   less than what its own first round wrote. *)
Definition race_2 : list citem :=
  align ++ [CCpu hart0 3;  (* h0 reads 0 *)
            CCpu hart1 3;  (* h1 reads 0 too *)
            CCpu hart0 6;  (* h0 writes 1 *)
            CCpu hart1 6;  (* h1 writes 1 -- h0's increment is LOST *)
            CCpu hart0 3;  (* h0 reads 1 *)
            CCpu hart1 3;  (* h1 reads 1 too *)
            CCpu hart0 6;  (* h0 writes 2 *)
            CCpu hart1 6]. (* h1 writes 2 -- and again *)

(* ONE ROUND COLLIDES.  The first rounds overlap, the second ones do not. *)
Definition race_3 : list citem :=
  align ++ [CCpu hart0 3; CCpu hart1 3; CCpu hart0 6; CCpu hart1 6;
            CCpu hart0 11]. (* h0 finishes alone: 1 -> 2, then h1: 2 -> 3 *)

(* NO COLLISION: hart 0 runs its whole racing pass before hart 1 starts. *)
Definition race_4 : list citem := align ++ [CCpu hart0 20].

(* in the order the capture lists them: counter 2, 3, 4 *)
Definition lost_schedules : list (list citem) := [race_2; race_3; race_4].

(* the uniform name VRunConc's generated case refers to *)
Definition schedules : list (list citem) := lost_schedules.
