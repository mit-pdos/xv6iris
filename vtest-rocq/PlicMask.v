(* PlicMask.v -- the ENABLE bit and the two degenerate accesses, and they
   all AGREE.

   Source: tools/vtest/tests/plic_mask.S.  Capture: PlicMaskGen.v.

   One source, the cheap one: the 16550 on source 10, raised with NO serial
   input at all by enabling the transmit-holding-register-empty interrupt in
   IER while the FIFO is empty.  No virtqueue, so this test declares only the
   stack and the result region ([start], not [start_dma]) -- declared bytes,
   not instructions, are what a test costs on the model side.

   Three things disk_intr never does:

     - a CLAIM WHEN NOTHING IS PENDING.  Returns 0 and changes nothing.  This
       is the case a driver's handler hits on a spurious entry, and the one
       xv6's plic_claim would return into trap.c's "unexpected interrupt".

     - a COMPLETE of a source that was never CLAIMED -- both when it is not
       pending either, and, more sharply, when it IS pending.  Completion
       must touch [p_claimed] and NOT [p_pending]: they are different bits
       for a reason, and an implementation that cleared pending here would
       silently drop a real request.

     - the ENABLE BIT IS NOT THE GATEWAY.  A source whose enable bit is clear
       still becomes pending -- [plic_latch] takes only the source, never a
       context, and QEMU's PLIC is the same -- but drives no notification and
       is not claimable.  Setting the bit AFTERWARDS makes the already-latched
       request claimable with no new edge from the device at all, which is
       the fact that separates "enable gates the gateway" from "enable gates
       the context's view of it". *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest PlicMaskGen.
Local Open Scope Z_scope.

Definition mask_run : option mstate := run_until 50000 (start plic_mask_text).

(* Every observation, byte for byte; offsets mirror tools/vtest/tests/plic_mask.S.
     +8  claim with nothing pending at all                    0
     +12 pending after completing source 5, never claimed     0
     +16 pending, source 10 up but NOT enabled                0x400
     +20 mip & SEIP -- no notification                        0
     +24 claim while the source is not enabled                0
     +28 pending -- the claim took nothing                    0x400
     +32 pending after complete(10), pending but not claimed  0x400
     +36 mip & SEIP once the enable bit is set                0x200
     +40 claim, now enabled                                   10
     +44 pending after it                                     0
     +48 mip & SEIP                                           0
     +52 the S-context enable word read back                  0x400          *)
Lemma plic_mask_result : result_of mask_run = plic_mask_qemu_result.
Proof. solve_vtest plic_mask_qemu_result. Qed.

(* What this rules out:

   - [plic_cand]'s [plic_enabled] conjunct, in both of its jobs.  Without it
     +24 would claim source 10 while it is masked, and +20 would report a
     notification for a source the context has not asked for.

   - [plic_latch] consulting the context.  It does not, and neither does the
     hardware: +16 latches a DISABLED source.  A model that had folded the
     enable check into the gateway would read 0 there -- and would then
     never produce the +36/+40 behaviour, where the bit is set long after
     the device's edge has come and gone and the request is still there to
     be claimed.

   - [plic_complete] touching [p_pending].  +32 is the pointed one: source
     10 is pending and NOT claimed, and completing it leaves the pending bit
     exactly where it was.  Completion clears an in-service marker; it is
     not an acknowledgement of the request.

   - a spurious claim ([plic_best] = None) having a side effect: +8 returns
     0 and +12 shows the PLIC unmoved.

   Nothing here diverges, so the whole 4 KB region is compared at once. *)
