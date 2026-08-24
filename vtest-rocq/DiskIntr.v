(* DiskIntr.v -- the INTERRUPT PATH, end to end, and it AGREES.

   Source: tools/vtest/tests/disk_intr.S.  Capture: DiskIntrGen.v.
   152 instructions on the model side.

   Four model components that only ever appear together, and that nothing in
   the suite had exercised before: [virtio_irq] (interrupt status nonzero =>
   the line is high), [dev_irq_level] (which device drives which PLIC
   source), [plic_latch] (the per-source gateway, which forwards a LEVEL
   source only while it is neither already pending nor claimed) and
   [plic_step] (the wire onto hart 0's sig_seip).  Two of VSched's schedule
   arms, SLatch and SWire, exist for this and had never been driven; running
   this test is what put them in [VSched.settle].

   THE PROPAGATION DELAY IS REAL AND IS TESTED.  The model deliberately makes
   the gateway latch and the wire SEPARATE steps from the MMIO write that
   caused them, rather than updating the pin synchronously.  So the test
   spins on the PLIC pending bit instead of reading it once -- which is what
   a driver must do against real hardware, and which is why this test would
   still pass if the delay were longer, and would NOT pass if the model had
   quietly made the pin synchronous.

   The whole 4 KB result region is compared here, not field by field: unlike
   DiskRw and DiskOrder this test records no used.len, so nothing it observes is
   subject to a known divergence and there is nothing to carve out. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIntrGen.
Local Open Scope Z_scope.

Definition intr_run : option mstate := run_until 30000 (start_dma disk_intr_text).

(* Every observation, byte for byte:
     +8  PLIC pending before the request          0
     +12 virtio InterruptStatus after completion  1
     +16 PLIC pending after completion            2   (source 1 latched)
     +20 mip & SEIP after completion              0x200 (the wire drove it)
     +24 what the S-context claim returned        1
     +28 PLIC pending after the claim             0
     +32 mip & SEIP after the claim               0
     +36 virtio InterruptStatus after the ack     0
     +40 PLIC pending after complete              0
     +44 mip & SEIP at the end                    0
     +48 the request's status byte                0                            *)
Lemma disk_intr_result : result_of intr_run = disk_intr_qemu_result.
Proof. solve_vtest disk_intr_qemu_result. Qed.

Lemma disk_intr_disk : disk_like intr_run disk_intr_qemu_disk = disk_intr_qemu_disk.
Proof. solve_vtest disk_intr_qemu_disk. Qed.

(* A POSITIVE result is worth as much as a divergence, and worth stating.
   What this rules out, concretely:
   - the disk raising its line but the gateway never forwarding it, or
     forwarding it to the wrong source id;
   - the claim returning something other than the source, or not clearing
     pending;
   - the line RE-latching after the claim -- it must not, because the level
     is still high at that point (the device has not been acknowledged yet)
     and [plic_latch] refuses a source that is already claimed.  If that
     guard were dropped the model would produce a second interrupt QEMU does
     not, and +28/+40 would separate;
   - the acknowledgement at the device (InterruptACK) not dropping the line,
     or the PLIC complete not clearing the claim. *)
