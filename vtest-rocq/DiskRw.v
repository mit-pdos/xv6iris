(* DiskRw.v -- one virtqueue, one WRITE, one READ.  The first test that makes
   the device do work: DMA in both directions, the used ring, the interrupt
   status, and the disk image itself.

   Source: tools/vtest/tests/disk_rw.S.  Capture: DiskRwGen.v.
   628 instructions on the model side, ~20 s per evaluation, so this file is
   deliberately TWO evaluations and no more (see below).

   WHAT IT FINDS.  The model matches QEMU on everything the request protocol
   turns on -- both status bytes, both used-ring ids, the used index, the
   interrupt status, the 512 bytes DMA'd back, and the sector on the disk --
   and diverges on three fields, listed and classified in section 3.  The
   third of them is new and is the reason this test exists. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskRwGen.
Local Open Scope Z_scope.

Definition rw_run : option mstate := run_until 20000 (start_dma disk_rw_text).

(* result-region offsets, mirroring tools/vtest/tests/disk_rw.S *)
Definition agree_offs : list nat :=
  [4;   (* progress marker: 3 = both requests completed *)
   12;  (* Status read back after FEATURES_OK *)
   20; 24; 28; 36;   (* write: status byte, used.idx, used.ring[0].id, ISR *)
   40; 44; 48; 56]%nat.  (* read:  the same four *)

Definition diverge_offs : list nat :=
  [8;   (* QueueNumMax *)
   16;  (* the negotiated feature word *)
   32;  (* write: used.ring[0].len *)
   52]%nat. (* read:  used.ring[1].len *)

(* ---------------------------------------------------------------------- *)
(* 1. What agrees -- and it is everything the protocol turns on.           *)
(*                                                                         *)
(*    ONE lemma, because each is one 628-instruction evaluation.  The RHS   *)
(*    is a [Definition] over the capture so that naming it in              *)
(*    [solve_vtest] does not cost a second run of the model.               *)
(* ---------------------------------------------------------------------- *)

Definition rw_expect :=
  ((fun o => cap_word disk_rw_qemu_result o) <$> agree_offs,
   cap_bytes disk_rw_qemu_result 512 512,
   disk_rw_qemu_disk).

Lemma disk_rw_agrees :
  ((fun o => res_word rw_run o) <$> agree_offs,
   res_bytes rw_run 512 512,
   disk_like rw_run disk_rw_qemu_disk) = rw_expect.
Proof. solve_vtest rw_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What does not.                                                       *)
(*                                                                         *)
(*    Pinned on BOTH sides rather than asserted equal.  A [<>] between two  *)
(*    literals is green today and the model-side equation goes RED the day  *)
(*    someone changes the model here -- which is exactly when this file     *)
(*    should be revisited, and is the property a comment alone would not    *)
(*    give.                                                                 *)
(* ---------------------------------------------------------------------- *)

Definition rw_model_diverging : list Z := [8; 0; 512; 512].
Definition rw_qemu_diverging  : list Z := [1024; 25684; 1; 513].

Lemma disk_rw_model_diverging :
  (fun o => res_word rw_run o) <$> diverge_offs = rw_model_diverging.
Proof. solve_vtest rw_model_diverging. Qed.

Lemma disk_rw_qemu_diverging :
  (fun o => cap_word disk_rw_qemu_result o) <$> diverge_offs = rw_qemu_diverging.
Proof. solve_vtest rw_qemu_diverging. Qed.

Lemma disk_rw_really_diverges : rw_model_diverging <> rw_qemu_diverging.
Proof. discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The three divergences, classified.                                   *)
(*                                                                         *)
(* (a) QueueNumMax: 8 versus 1024.  INCOMPLETENESS.  [vq_size_ok] accepts   *)
(*     only {1,2,4,8} and [virtio_write] REFUSES any other QueueNum, so a   *)
(*     driver that sizes its queue at 16 -- legal, and what a real one may  *)
(*     do -- has no model execution at all.  It cannot make a proof wrong;  *)
(*     it makes some drivers unverifiable.  Already visible in t1.          *)
(*                                                                         *)
(* (b) The negotiated feature word: 0 versus 0x6454.  INCOMPLETENESS, same  *)
(*     shape.  [virtio_device_features] offers only FLUSH|CONFIG_WCE, so    *)
(*     everything else the driver clears was never offered and the          *)
(*     negotiation lands on 0.  Both sides agree on the one bit that has a  *)
(*     BEHAVIOUR here -- bit 9, FLUSH, which both clear, so both devices    *)
(*     are writethrough and the rest of this test agrees because of it.     *)
(*     Note also that DeviceFeaturesSel (0x14) and DriverFeaturesSel (0x24) *)
(*     are not modelled at all, so VIRTIO_F_VERSION_1 (bit 32) can neither  *)
(*     be read nor acknowledged: a spec-conforming modern driver is outside *)
(*     the model entirely.                                                  *)
(*                                                                         *)
(* (c) used.ring[i].len: 512/512 versus 1/513.  THIS ONE IS A DEFECT, and   *)
(*     not of the same kind.  The spec defines the used element's [len] as  *)
(*     the number of bytes written into the DEVICE-WRITABLE part of the     *)
(*     chain: 1 for a write request (the status byte alone) and 512+1 for a *)
(*     read (the data buffer plus the status byte).  QEMU produces exactly  *)
(*     that.  [VirtioModel.virtio_used_writes] instead writes [vr_len r] --  *)
(*     the DATA descriptor's length -- in both directions, which is a value *)
(*     real hardware never produces.  So the model is not merely stricter    *)
(*     here, it is WRONG: a driver that reads used.len to learn how much     *)
(*     data arrived would be verified against a device that does not exist.  *)
(*     xv6's driver ignores the field, which is why nothing in the tree has  *)
(*     noticed.                                                             *)
(*                                                                         *)
(*     The fix is local -- [virtio_used_writes] needs the request TYPE to    *)
(*     choose between 1 and [vr_len r + 1] -- but it moves a definition in   *)
(*     VirtioModel.v, whose reverse-dependency closure is 1286 files, so it  *)
(*     is a deliberate decision rather than a drive-by edit.  When it is     *)
(*     made, [disk_rw_model_diverging] goes red and this section shrinks.      *)
(* ---------------------------------------------------------------------- *)
