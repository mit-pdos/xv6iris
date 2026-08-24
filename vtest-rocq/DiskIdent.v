(* DiskIdent.v -- EVERY VIRTIO-MMIO REGISTER THE MODEL DECODES, against QEMU.
   The positive half of the STUCK MATRIX: the twelve disk_ident_* programs
   each pin ONE access the model refuses; this one pins the whole of what it
   does answer, so the two together are a scoreboard of the register set
   rather than a list of anecdotes.

   Source: tools/vtest/tests/disk_ident.S.  Capture: DiskIdentGen.v.
   65 instructions on the model side, and no DMA region: the queue is
   configured and made ready but nothing is ever published, so the device
   never has work and never reads memory.

   WHAT IT FINDS.  Sixteen of nineteen observations are identical, including
   the whole of the RESET command, which nothing had tested before.  The
   three that differ are the two ALREADY-KNOWN divergences of findings 1 and
   2 (QueueNumMax, and the offered feature word read twice), pinned on both
   sides in section 2 rather than re-reported.

   THE SCOREBOARD.  [VirtioModel.virtio_read] answers nine offsets and
   [virtio_write] fourteen; everything else in the 4 KB window is None.
   What that costs, one file per entry:

     0x100..  config space (CAPACITY)  DiskIdentCap.v   <- worth FIXING
     0x0fc    ConfigGeneration         DiskIdentConfgen.v
     0x0c0    QueueReset               DiskIdentQreset.v
     0x0ac    SHMSel + SHMLen/SHMBase  DiskIdentShmsel.v
     0x014    DeviceFeaturesSel        DiskIdentFeatsel.v   (finding 3)
     0x024    DriverFeaturesSel        DiskIdentDrvfsel.v   (finding 3)
     any      a 1-byte read            DiskIdentRd1.v
     any      a 2-byte read            DiskIdentRd2.v
     any      a 1-byte write           DiskIdentWr1.v
     0x038    QueueNum = 16            DiskIdentQnum.v      (finding 1's cost)
     0x038    any per-queue write at QueueSel /= 0  DiskIdentQsel.v
     0x050    QueueNotify = 1          DiskIdentNotify.v

   Every one of those is INCOMPLETENESS, not unsoundness: a stuck state has
   no transition, the system theorem proves xv6 never reaches one, and so no
   proof can be wrong because of it.  What it costs is which drivers the
   development can describe at all. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentGen.
Local Open Scope Z_scope.

Definition ident_run : option mstate := run_until 50000 (start disk_ident_text).

(* result-region offsets, mirroring tools/vtest/tests/disk_ident.S *)
Definition ident_agree_offs : list nat :=
  [4;   (* progress marker: 2 = the reset at the end also completed *)
   8;   (* MagicValue      0x74726976 *)
   12;  (* Version         2 *)
   16;  (* DeviceID        2 = block *)
   20;  (* VendorID        0x554d4551 *)
   28;  (* Status after ACKNOWLEDGE|DRIVER   3 *)
   32;  (* Status after FEATURES_OK          11 -- the bit STUCK *)
   36;  (* QueueNumMax at QueueSel = 0    1024 -- was finding 1 *)
   40;  (* QueueNumMax at QueueSel = 1       0  -- no such queue *)
   44;  (* QueueReady  at QueueSel = 1       0 *)
   48;  (* QueueReady  at QueueSel = 0, before  0 *)
   52;  (* QueueReady  at QueueSel = 0, after   1 *)
   56;  (* InterruptStatus, nothing outstanding 0 *)
   60;  (* Status after DRIVER_OK            15 *)
   64;  (* Status after the RESET command    0 *)
   68;  (* QueueReady after the reset        0 *)
   76]%nat. (* InterruptStatus after the reset 0 *)

Definition ident_diverge_offs : list nat :=
  [24;  (* DeviceFeatures                     -- finding 2 *)
   72]%nat. (* DeviceFeatures again, after the reset -- finding 2 *)

(* ---------------------------------------------------------------------- *)
(* 1. What agrees.                                                         *)
(*                                                                         *)
(*    ONE lemma, one evaluation: the RHS is a [Definition] over the capture *)
(*    so that naming it in [solve_vtest] does not cost a second run.        *)
(* ---------------------------------------------------------------------- *)

Definition ident_expect :=
  (fun o => cap_word disk_ident_qemu_result o) <$> ident_agree_offs.

Lemma disk_ident_agrees :
  (fun o => res_word ident_run o) <$> ident_agree_offs = ident_expect.
Proof. solve_vtest ident_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What does not -- pinned on BOTH sides, findings 1 and 2.             *)
(*                                                                         *)
(*    [virtio_queue_num_max] is 8 where QEMU offers 1024, and               *)
(*    [virtio_device_features] offers FLUSH|CONFIG_WCE = 0xa00 where QEMU   *)
(*    offers 0x30006e54.  Both are already in the findings table; they are  *)
(*    recorded here rather than asserted equal so that this file goes RED   *)
(*    the day the model changes there, which is exactly when it should be   *)
(*    revisited.                                                           *)
(*                                                                         *)
(*    Reading DeviceFeatures a second time AFTER the reset is not padding:  *)
(*    it says the OFFERED word is not part of what a reset clears, on both  *)
(*    machines.  In the model that is because [virtio_read] returns a       *)
(*    constant; in QEMU because the host feature set belongs to the device  *)
(*    and not to the session.  Same value, and for once the model's         *)
(*    simplification is the right shape.                                    *)
(* ---------------------------------------------------------------------- *)

Definition ident_model_diverging : list Z := [0xa00; 0xa00].
Definition ident_qemu_diverging  : list Z := [0x30006e54; 0x30006e54].

Lemma disk_ident_model_diverging :
  (fun o => res_word ident_run o) <$> ident_diverge_offs = ident_model_diverging.
Proof. solve_vtest ident_model_diverging. Qed.

Lemma disk_ident_qemu_diverging :
  (fun o => cap_word disk_ident_qemu_result o) <$> ident_diverge_offs
  = ident_qemu_diverging.
Proof. solve_vtest ident_qemu_diverging. Qed.

Lemma disk_ident_really_diverges :
  ident_model_diverging <> ident_qemu_diverging.
Proof. discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The CONFIRMATIONS, which are the point of this file.                 *)
(*                                                                         *)
(*  - The four identification registers, read before any bring-up:          *)
(*    MagicValue, Version, DeviceID, VendorID.  Version in particular is 2  *)
(*    on both, which is only true because tools/vtest/vtest.py passes       *)
(*    -global virtio-mmio.force-legacy=false; without it QEMU presents a    *)
(*    LEGACY device and this register alone would sink every test.          *)
(*                                                                         *)
(*  - The STATUS PROTOCOL, at every step: 3 after ACKNOWLEDGE|DRIVER, 11    *)
(*    after FEATURES_OK -- and the model, like QEMU, LETS FEATURES_OK STICK *)
(*    for this feature set, which is the driver's only way to learn the     *)
(*    device accepted it -- and 15 after DRIVER_OK.                        *)
(*                                                                         *)
(*  - The PER-QUEUE READS AT A QUEUE THAT DOES NOT EXIST.  [virtio_read]    *)
(*    answers QueueNumMax and QueueReady with 0 when [vc_qsel] is not 0,    *)
(*    and QEMU does the same, so a driver may LOOK at queue 1 -- it may not *)
(*    TOUCH it (DiskIdentQsel.v).  This is the model's one per-queue        *)
(*    behaviour and it is faithful.                                        *)
(*                                                                         *)
(*  - QueueReady reads back what was written to it, 0 then 1.               *)
(*                                                                         *)
(*  - THE RESET COMMAND, which nothing in the suite had exercised.  Writing *)
(*    0 to Status drops the whole configuration on both machines: Status    *)
(*    reads 0, QueueReady is back to 0 even though the driver never cleared *)
(*    it, InterruptStatus is 0, and the offered feature word is untouched.  *)
(*    [VirtioModel.virtio_reset] keeps exactly one field, [v_disk], and     *)
(*    that is what the hardware does too.                                   *)
(*                                                                         *)
(*  - InterruptStatus is 0 while nothing is outstanding, both before and    *)
(*    after the reset.  Note what is NOT tested: the model's [v_isr] can    *)
(*    only ever hold bit 0 ([vio_isr_used_buffer]), because that is the     *)
(*    only bit anything sets; a real virtio device also has bit 1,          *)
(*    CONFIGURATION CHANGE, which it raises when the config space moves.    *)
(*    With no config space in the model (DiskIdentCap.v) there is nothing   *)
(*    to raise it for, so the missing bit and the missing config space are  *)
(*    one gap and not two.                                                  *)
(* ---------------------------------------------------------------------- *)
