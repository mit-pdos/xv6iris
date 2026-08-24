(* ConcLost.v -- A LOST UPDATE, and a model schedule for EVERY outcome
   QEMU produced.

   Source: tools/vtest/tests/conc_lost.S (`vtest: smp=2 repeat=100`).
   Capture: ConcLostGen.v.

   Two harts, one word, no atomics: each hart runs two rounds of
   `lw; nop x4; addi 1; sw` on RESULT+0x100.  Three answers are possible and
   QEMU produces all three -- over 300 runs, 4 (208x), 2 (59x) and 3 (33x) --
   so this is a genuine race and not a race-shaped program that only ever
   goes one way.  The capture is therefore a SET, [conc_lost_qemu_results],
   sorted by the raw result bytes, i.e. by the counter: 2, then 3, then 4.

   WHAT THE TEST CLAIMS is [conc_lost_model_admits_all]: schedule i
   reproduces observed outcome i, over the WHOLE 4 KB result region.  The
   [citem] lists ARE the witnesses, and they are also the documentation of
   which interleaving gives which answer -- read [race_2] and you can see the
   two harts reading the same value twice.

   RESULT layout, mirroring tools/vtest/tests/conc_lost.S:
     +0x000  DONE          +0x100  CTR    -- THE RACY WORD (= the total)
     +0x004  status = 1    +0x104  BAR0A  +0x108  BAR1A   pass-1 rendezvous
     +0x008  the total     +0x10c  BAR0B  +0x110  BAR1B   pass-2 rendezvous
                           +0x114  PRIV0  +0x118  PRIV1   warm-up words
                           +0x11c  DONE1  -- hart 1's loop is over *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VConc ConcLostGen.
Local Open Scope Z_scope.

Definition lost_g0 : gstate := g0 conc_lost_text.

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

(* ---------------------------------------------------------------------- *)
(* 2. THE TEST.  Schedule i reproduces QEMU's outcome i, whole region.     *)
(* ---------------------------------------------------------------------- *)

Lemma conc_lost_model_admits_all :
  cobs_all 20000 lost_schedules lost_g0 = conc_lost_qemu_results.
Proof. solve_vtest conc_lost_qemu_results. Qed.

(* ...and QEMU really did produce three different answers, not one. *)
Lemma conc_lost_really_races : length conc_lost_qemu_results = 3%nat.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The unscheduled run is the maximally-colliding one.                  *)
(*    [cobs] with an EMPTY schedule is [cfinish]'s round-robin from reset,  *)
(*    which steps the harts in lockstep -- so they read the same word in    *)
(*    the same round every time and the counter ends at the floor.  Worth   *)
(*    pinning: it is the reason a race test must NAME its interleaving      *)
(*    rather than let the harness pick one.                                 *)
(* ---------------------------------------------------------------------- *)

Lemma conc_lost_round_robin_loses_both :
  cobs 20000 [] lost_g0 = hd [] conc_lost_qemu_results.
Proof. solve_vtest (hd (@nil Z) conc_lost_qemu_results). Qed.
