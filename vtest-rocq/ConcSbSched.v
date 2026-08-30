(* ConcSbSched.v -- the INTERLEAVINGS for the multi-hart case, lifted from the
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
(* 1. Getting both harts to the litmus pair.                               *)
(*                                                                         *)
(*    Instruction counts off `riscv64-linux-gnu-objdump -d`.  Both harts    *)
(*    take 22 instructions from reset into <pass> and 6 more to the store   *)
(*    that publishes their pass-1 rendezvous flag, so:                      *)
(*                                                                         *)
(*      28  hart 0 arrives at rendezvous A                                  *)
(*      31  hart 1 arrives, sees hart 0, and falls through the spin         *)
(*      26  hart 0 falls through (3) and runs the WARM-UP pass (23),        *)
(*          ending on the store that publishes rendezvous B                 *)
(*      28  hart 1 does the same, falls through rendezvous B, and runs its  *)
(*          skew-trim delay loop, ending on `li t0, 1`                      *)
(*       9  hart 0 does the same (its delay loop is one round longer)       *)
(*                                                                         *)
(*    Both harts are now poised on their STORE, with two instructions each  *)
(*    left in the litmus test: [1] is the store, [2] is the store and the   *)
(*    load.  The counts differ (26/28/9 rather than one number) only        *)
(*    because the program deliberately gives the harts delay loops of       *)
(*    different lengths -- see the header of conc_sb.S.                     *)
(* ---------------------------------------------------------------------- *)

Definition align : list citem :=
  [CCpu hart0 28; CCpu hart1 31; CCpu hart0 26; CCpu hart1 28; CCpu hart0 9].

(* ---------------------------------------------------------------------- *)
(* 2. ALL SIX interleavings of the two two-instruction sequences, and what  *)
(*    each gives.  This is the exhaustive form of the SC argument: with     *)
(*    [s] the store and [l] the load,                                       *)
(*                                                                         *)
(*      s0 l0 s1 l1  (0,1)     s0 s1 l0 l1  (1,1)     s0 s1 l1 l0  (1,1)    *)
(*      s1 s0 l0 l1  (1,1)     s1 s0 l1 l0  (1,1)     s1 l1 s0 l0  (1,0)    *)
(*                                                                         *)
(*    -- and (0,0) is in none of them.                                     *)
(* ---------------------------------------------------------------------- *)

Definition sb_01 : list citem := align ++ [CCpu hart0 2; CCpu hart1 2].
Definition sb_11 : list citem :=
  align ++ [CCpu hart0 1; CCpu hart1 1; CCpu hart0 1; CCpu hart1 1].
Definition sb_ss_lr : list citem := align ++ [CCpu hart0 1; CCpu hart1 2; CCpu hart0 1].
Definition sb_ss_rl : list citem := align ++ [CCpu hart1 1; CCpu hart0 2; CCpu hart1 1].
Definition sb_11' : list citem :=
  align ++ [CCpu hart1 1; CCpu hart0 1; CCpu hart1 1; CCpu hart0 1].
Definition sb_10 : list citem := align ++ [CCpu hart1 2; CCpu hart0 2].

Definition sb_all_interleavings : list (list citem) :=
  [sb_01; sb_11; sb_ss_lr; sb_ss_rl; sb_11'; sb_10].

(* The WHY -- that a [gstate] has one [gmem], so the model is
   sequentially consistent and QEMU is not -- is now
   VModelFacts.model_hart_sees_the_one_memory and
   VModelFacts.model_store_is_immediately_global. *)

(* ---------------------------------------------------------------------- *)
(* 4. THE TEST.  QEMU's capture has four outcomes; the model reproduces the *)
(*    three SEQUENTIALLY CONSISTENT ones, whole 4 KB region each, in the    *)
(*    order the capture lists them.  The capture is sorted by the raw       *)
(*    bytes, i.e. by (a,b), so the non-SC (0,0) is entry 0 and [tail] is    *)
(*    exactly the part the model can do.                                    *)
(* ---------------------------------------------------------------------- *)

Definition sb_schedules : list (list citem) := [sb_01; sb_10; sb_11].

(* the uniform name VRunConc's generated case refers to *)
Definition schedules : list (list citem) := sb_schedules.
