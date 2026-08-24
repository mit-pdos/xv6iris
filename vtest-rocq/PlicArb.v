(* PlicArb.v -- ARBITRATION between two sources, and it AGREES.

   Source: tools/vtest/tests/plic_arb.S.  Capture: PlicArbGen.v.

   disk_intr drives the PLIC, but only ever with ONE source up, at priority
   1, with threshold 0 -- so [plic_best] and [plic_better], the fold that
   picks a winner, were never asked a question with more than one answer,
   and the pending word was never read with more than one bit in it.  This
   test is the PLIC as subject.

   Two sources, and they are the only two this machine has: the virtio disk
   on source 1, raised by completing a write request, and the 16550 on
   source 10, raised with NO serial input at all by enabling the
   transmit-holding-register-empty interrupt in IER while the FIFO is empty
   ([DevModel.uart_tx_int] on the model, thr_ipending on QEMU).  The disk
   gets the LOWER priority and the LOWER id, so the claim order 10-then-1
   can only come from the priority comparison: an implementation that
   scanned ids in order, or ignored priority altogether, would answer 1
   first.  PlicTie.v is the same program with the priorities EQUAL and the
   order duly reversed, which is what pins [plic_better]'s two clauses down
   separately.

   NOTHING IS COMPLETED here.  A source completed while its level is still
   asserted is a different question, with a divergence of its own, and it
   lives in PlicLevel.v.

   The whole 4 KB result region is compared, and the disk with it: this test
   records no used.len and negotiates no features, so nothing it observes is
   subject to a known divergence and there is nothing to carve out. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PlicArbGen.
Local Open Scope Z_scope.

Definition arb_run : option mstate := run_until 50000 (start_dma plic_arb_text).

(* Every observation, byte for byte; offsets mirror tools/vtest/tests/plic_arb.S.
     +8  PLIC pending, before anything                       0
     +12 PLIC pending, after the UART line rises             0x400
     +16 the disk request's status byte                      0
     +20 PLIC pending, BOTH sources up                       0x402
     +24 mip & SEIP                                          0x200
     +28 the FIRST claim -- priority 7 beats priority 3      10
     +32 PLIC pending after it                               0x002
     +36 mip & SEIP (source 1 is still above threshold)      0x200
     +40 the SECOND claim                                    1
     +44 PLIC pending after it                               0
     +48 mip & SEIP                                          0
     +52 a THIRD claim, with nothing pending                 0
     +56 prio[1] read back                                   3
     +60 prio[10] read back                                  7
     +64 the S-context enable word read back                 0x402
     +68 the S-context threshold read back                   0                *)
Lemma plic_arb_result : result_of arb_run = plic_arb_qemu_result.
Proof. solve_vtest plic_arb_qemu_result. Qed.

Lemma plic_arb_disk : disk_like arb_run plic_arb_qemu_disk = plic_arb_qemu_disk.
Proof. solve_vtest plic_arb_qemu_disk. Qed.

(* A POSITIVE result is worth as much as a divergence.  What this rules out,
   concretely -- each of these is a way [DevModel]'s PLIC could have been
   wrong and is not:

   - the pending WORD.  [plic_pending_word] folds bit i in from
     [p_pending] over word 0's thirty-two ids; until now only one bit
     was ever set in it, so an off-by-one in the shift or the fold could not
     show.  Here 0x402 pins bits 1 and 10 simultaneously, and the two
     intermediate reads (0x400 with only the UART up, 0x002 with only the
     disk left) pin each bit separately against the other.

   - ARBITRATION BY PRIORITY.  [plic_best]'s fold and [plic_better]'s first
     clause: the claim returns 10 while 1 is also pending, enabled and
     non-zero-priority.  Ids are scanned in order, so returning the
     LATER id is exactly the evidence that priority, not position, decided.

   - the claim's SIDE EFFECTS, twice over.  Each claim clears that source's
     pending bit and no other (+32 keeps bit 1, +44 clears it), and marks it
     claimed -- which is why neither source re-latches even though BOTH
     device lines are still high at every one of these reads.  If
     [plic_latch]'s [negb (p_claimed p i)] guard were dropped the model
     would re-forward both and +44 would read 0x402.

   - the NOTIFICATION tracking the remaining work.  mip.SEIP stays high
     across the first claim (source 1 still qualifies) and drops only when
     the last pending source goes -- so [plic_eip] is recomputed from the
     pending set rather than latched, and the wire follows it down as well
     as up.

   - a claim with NOTHING pending returns 0 and disturbs nothing ([plic_best]
     = None), which is the case a driver's interrupt handler hits on a
     spurious entry.

   - the configuration registers READ BACK: the priority window at 4*i, the
     S-context enable word at 0x2080 and the threshold at 0x201000 all
     return what was written.  That is [plic_read]'s decode agreeing with
     [plic_write]'s on three different register families at once. *)
