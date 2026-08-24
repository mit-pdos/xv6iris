(* ConcSmoke.v -- the two-hart plumbing test, and the template for a race.

   Source: tools/vtest/tests/conc_smoke.S (`vtest: smp=2`).
   Capture: ConcSmokeGen.v.

   No race here: hart 1 stores a magic word, hart 0 spins until it sees it.
   What it checks is that the pieces a race test needs all work -- QEMU with
   -smp 2, vtest.S dispatching only non-zero harts to _vtest_body_ap, and
   VConc stepping two harts over ONE memory.  It is worth having on its own:
   with -smp 1 hart 0 spins forever, so this also pins down that the AP
   really does run.

   THE SCHEDULE IS EMPTY here because nothing about the interleaving matters
   -- [cfinish] round-robins the harts one instruction each until hart 0
   publishes.  A test that IS about an interleaving names it instead:

     Definition sch : list citem := [CCpu hart0 12; CCpu hart1 14; CCpu hart0 3].
     ... cobs 5000 sch (g0 foo_text) ...

   and then the schedule list is the readable record of which interleaving
   produced which outcome. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VConc ConcSmokeGen.
Local Open Scope Z_scope.

Definition smoke_g0 : gstate := g0 conc_smoke_text.

Lemma conc_smoke_finishes : cstatus 5000 smoke_g0 = VDone.
Proof. solve_vtest VDone. Qed.

(* the whole 4 KB result region, hart 1's store included *)
Lemma conc_smoke_result : cobs 5000 [] smoke_g0 = conc_smoke_qemu_result.
Proof. solve_vtest conc_smoke_qemu_result. Qed.
