(* PlicTie.v -- the TIE-BREAK, and it AGREES.

   Source: tools/vtest/tests/plic_tie.S.  Capture: PlicTieGen.v.

   PlicArb.v settles two simultaneously pending sources by PRIORITY, and the
   winner there is the HIGHER id (10 over 1), which is what makes it evidence
   about [plic_better]'s first clause rather than about the order the fold
   visits ids in.  This test is the same program with the two priorities made
   EQUAL, so the only thing left to decide the winner is [plic_better]'s
   second clause -- "ties broken toward the lower id" -- and the claim order
   REVERSES: source 1 first, then source 10.

   Two programs that differ in two priority values and produce OPPOSITE
   orders is what pins the comparison down.  Either one alone is matched by
   an implementation that gets half of it wrong: PlicArb alone by one that
   ignores ids, this one alone by one that ignores priorities.

   The whole 4 KB result region is compared, and the disk with it. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PlicTieGen.
Local Open Scope Z_scope.

Definition tie_run : option mstate := run_until 50000 (start_dma plic_tie_text).

(* Offsets mirror tools/vtest/tests/plic_tie.S -- PlicArb.v's layout exactly,
   with the four values the tie changes:
     +28 the FIRST claim  -- equal priorities, so the LOWER id     1
     +32 PLIC pending after it                                     0x400
     +36 mip & SEIP (source 10 is still pending)                   0x200
     +40 the SECOND claim                                          10
     +56 prio[1] read back                                         5
     +60 prio[10] read back                                        5                *)
Lemma plic_tie_result : result_of tie_run = plic_tie_qemu_result.
Proof. solve_vtest plic_tie_qemu_result. Qed.

Lemma plic_tie_disk : disk_like tie_run plic_tie_qemu_disk = plic_tie_qemu_disk.
Proof. solve_vtest plic_tie_qemu_disk. Qed.

(* What this rules out that PlicArb.v does not: that [plic_better]'s tie
   clause -- [(p_prio i =? p_prio j) && (i <? j)] -- has the comparison the
   wrong way round, or is absent.  Absent, [plic_best]'s fold would keep the
   FIRST candidate it met, which is still id 1, so this test would pass by
   accident; but PlicArb.v would then also return 1 and would fail.  The
   wrong way round, this test returns 10 first and fails.  It takes the two
   together to say the fold implements "highest priority, ties to the lowest
   id" and QEMU's PLIC does the same thing.

   (QEMU's is the same rule for the same reason: its claim scans sources in
   increasing id order and replaces the incumbent only on a STRICTLY greater
   priority, so ties fall to the lower id there too.) *)
