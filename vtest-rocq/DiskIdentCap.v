(* DiskIdentCap.v -- THE CONFIGURATION SPACE: the capacity, and the fields
   after it.  The capacity agrees; one field of a feature this device does
   not offer does not, and that is finding 2.

   Source: tools/vtest/tests/disk_ident_cap.S.  Capture: DiskIdentCapGen.v.

   virtio-blk's configuration space starts at 0x100 with the 64-bit CAPACITY
   in sectors, and it is not feature-gated: every virtio-blk device has one,
   and a driver that asks how big the disk is reads it there.  The model used
   to decode nothing above 0x0a4 (finding 13), so that question was a STUCK
   machine.

   THE MODEL HAS NO SIZE OF ITS OWN.  [VirtioModel.v_disk] is a total
   function, so the medium's edge is a separate fact about the machine: the
   capacity is a FIELD, [v_cap], set by whoever attaches the image and kept
   across a reset (the configuration goes, the disk does not).  Its power-on
   value is the size of the image this harness attaches -- 128 sectors, 64 KB
   -- which is what makes the first two fields below a real comparison rather
   than a constant agreeing with itself. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list bitvector.definitions.
Require Import VTest DiskIdentCapGen.
Local Open Scope Z_scope.

Definition cap_run : option mstate := run_until 50000 (start disk_ident_cap_text).

(* result-region offsets, mirroring tools/vtest/tests/disk_ident_cap.S *)
Definition cap_agree_offs : list nat :=
  [4;    (* progress marker: the program ran *)
   8;    (* capacity, low word    128 = the backing image *)
   12;   (* capacity, high word     0 *)
   16]%nat. (* size_max              0 -- VIRTIO_BLK_F_SIZE_MAX is offered by
                                          neither device, so neither fills it *)

Definition cap_diverge_offs : list nat :=
  [20]%nat. (* seg_max *)

Definition cap_expect :=
  (fun o => cap_word disk_ident_cap_qemu_result o) <$> cap_agree_offs.

Lemma disk_ident_cap_agrees :
  (fun o => res_word cap_run o) <$> cap_agree_offs = cap_expect.
Proof. solve_vtest cap_expect. Qed.

(* SEG_MAX: the QEMU device OFFERS VIRTIO_BLK_F_SEG_MAX and therefore fills
   its config field; this device does not offer it, so the field belongs to
   no negotiated feature and reads zero.  A driver may only look at a config
   field whose feature it negotiated, so neither answer can mislead one --
   but the two differ, and the difference is finding 2 (which features this
   device has), seen through the configuration space. *)
Definition cap_model_diverging : list Z := [0].
Definition cap_qemu_diverging  : list Z := [254].

Lemma disk_ident_cap_model_diverging :
  (fun o => res_word cap_run o) <$> cap_diverge_offs = cap_model_diverging.
Proof. solve_vtest cap_model_diverging. Qed.

Lemma disk_ident_cap_qemu_diverging :
  (fun o => cap_word disk_ident_cap_qemu_result o) <$> cap_diverge_offs
  = cap_qemu_diverging.
Proof. solve_vtest cap_qemu_diverging. Qed.

Lemma disk_ident_cap_really_diverges :
  cap_model_diverging <> cap_qemu_diverging.
Proof. discriminate. Qed.

(* ...and the capacity is the MEDIUM's, not a constant: attach a different
   image and the register follows it. *)
Lemma disk_ident_cap_follows_medium :
  match virtio_read (set_vcap virtio0_state (Z_to_bv 64 2000)) 0x100 with
  | Some w => bv_unsigned w
  | None => -1
  end = 2000.
Proof. solve_vtest (2000 : Z). Qed.
