(* DiskIdentFeatsel.v -- THE DEVICE-FEATURES WORD SELECTOR.  The mechanism
   agrees; the two words it selects do not, and that is finding 2 rather than
   anything about the selector.

   Source: tools/vtest/tests/disk_ident_featsel.S.  Capture: DiskIdentFeatselGen.v.

   DeviceFeaturesSel (0x014) was not decoded at all (finding 3), so a driver
   that wanted any feature bit above 31 -- VIRTIO_F_VERSION_1 among them, the
   bit a 1.x driver MUST ack -- was a STUCK machine at its first select.  The
   register is now real: it selects which 32-bit word DeviceFeatures reports,
   word 1 carries VERSION_1, and a selection with nothing behind it reads
   zero.  The program runs to completion on both machines.

   WHAT STILL DIFFERS is what the device OFFERS, which is a statement about
   the device's capabilities and not about this register: this model offers
   FLUSH and CONFIG_WCE, the QEMU device offers those plus SEG_MAX, GEOMETRY,
   BLK_SIZE, TOPOLOGY, DISCARD, WRITE_ZEROES, INDIRECT_DESC and EVENT_IDX,
   and in the high word RING_RESET beside VERSION_1.  Offering a feature
   obliges implementing it -- its config fields, and for DISCARD and
   WRITE_ZEROES whole request types -- so widening the word is a device
   change, not a decode fix, and it is recorded as finding 2. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentFeatselGen.
Local Open Scope Z_scope.

Definition di_featsel_run : option mstate :=
  run_until 50000 (start disk_ident_featsel_text).

(* result-region offsets, mirroring tools/vtest/tests/disk_ident_featsel.S *)
Definition di_featsel_agree_offs : list nat :=
  [4]%nat.   (* the progress marker: the program RAN, which is the finding-3 half *)

Definition di_featsel_diverge_offs : list nat :=
  [8;    (* DeviceFeatures with word 0 selected *)
   12]%nat. (* ...and with word 1 selected *)

Definition di_featsel_expect :=
  (fun o => cap_word disk_ident_featsel_qemu_result o) <$> di_featsel_agree_offs.

Lemma disk_ident_featsel_agrees :
  (fun o => res_word di_featsel_run o) <$> di_featsel_agree_offs
  = di_featsel_expect.
Proof. solve_vtest di_featsel_expect. Qed.

(* the two feature words, pinned on both sides *)
Definition di_featsel_model_diverging : list Z := [0xa00; 1].
Definition di_featsel_qemu_diverging  : list Z := [805334612; 257].

Lemma disk_ident_featsel_model_diverging :
  (fun o => res_word di_featsel_run o) <$> di_featsel_diverge_offs
  = di_featsel_model_diverging.
Proof. solve_vtest di_featsel_model_diverging. Qed.

Lemma disk_ident_featsel_qemu_diverging :
  (fun o => cap_word disk_ident_featsel_qemu_result o) <$> di_featsel_diverge_offs
  = di_featsel_qemu_diverging.
Proof. solve_vtest di_featsel_qemu_diverging. Qed.

Lemma disk_ident_featsel_really_diverges :
  di_featsel_model_diverging <> di_featsel_qemu_diverging.
Proof. discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* CLASSIFICATION: INCOMPLETENESS, and the safe direction of it.  The      *)
(* model offers a SUBSET of what the machine offers, so every negotiation  *)
(* it can describe is one the machine would also accept; what it cannot    *)
(* describe is a driver that wants one of the bits this device does not     *)
(* have.  The reverse -- advertising a feature and then not implementing   *)
(* it -- is the direction that would make a proof wrong, and it is why     *)
(* the word was not simply widened to match the capture.                   *)
(* ---------------------------------------------------------------------- *)
