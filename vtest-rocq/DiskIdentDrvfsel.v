(* DiskIdentDrvfsel.v -- THE DRIVER-FEATURES WORD SELECTOR, and a full 1.x
   negotiation.  The mechanism agrees and the negotiation completes; the two
   feature words differ, which is finding 2 (see DiskIdentFeatsel.v).

   Source: tools/vtest/tests/disk_ident_drvfsel.S.  Capture: DiskIdentDrvfselGen.v.

   DriverFeaturesSel (0x024) was not decoded (finding 3), so a driver could
   not ack a feature bit above 31 at all -- and VIRTIO_F_VERSION_1 lives up
   there, which makes it the bit a modern driver MUST ack for the transport
   to be legal.  Both selectors are now real registers: the ack lands in the
   word DriverFeaturesSel names, and the device records both words.

   What this test therefore pins, and could not before, is the SHAPE of a
   1.x negotiation: select word 0, read, ack; select word 1, read, ack
   VERSION_1; set FEATURES_OK; re-read status and find it stuck.  The final
   status is 11 on both machines. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentDrvfselGen.
Local Open Scope Z_scope.

Definition di_drvfsel_run : option mstate :=
  run_until 50000 (start disk_ident_drvfsel_text).

(* result-region offsets, mirroring tools/vtest/tests/disk_ident_drvfsel.S *)
Definition di_drvfsel_agree_offs : list nat :=
  [4;    (* progress marker *)
   16]%nat. (* the status after the whole negotiation: 11 = ACK|DRIVER|FEATURES_OK *)

Definition di_drvfsel_diverge_offs : list nat :=
  [8; 12]%nat.   (* the two feature words -- finding 2 *)

Definition di_drvfsel_expect :=
  (fun o => cap_word disk_ident_drvfsel_qemu_result o) <$> di_drvfsel_agree_offs.

Lemma disk_ident_drvfsel_agrees :
  (fun o => res_word di_drvfsel_run o) <$> di_drvfsel_agree_offs
  = di_drvfsel_expect.
Proof. solve_vtest di_drvfsel_expect. Qed.

(* THE STATUS IS THE POINT: FEATURES_OK stays set, so the device ACCEPTED the
   negotiation -- including the VERSION_1 ack, which had nowhere to land
   before.  A device that dropped the second word would still report 11 here,
   which is why the model states separately (VioCheck / the model's own
   [vc_dfeat1]) that the acked word is recorded. *)

Definition di_drvfsel_model_diverging : list Z := [0xa00; 1].
Definition di_drvfsel_qemu_diverging  : list Z := [805334612; 257].

Lemma disk_ident_drvfsel_model_diverging :
  (fun o => res_word di_drvfsel_run o) <$> di_drvfsel_diverge_offs
  = di_drvfsel_model_diverging.
Proof. solve_vtest di_drvfsel_model_diverging. Qed.

Lemma disk_ident_drvfsel_qemu_diverging :
  (fun o => cap_word disk_ident_drvfsel_qemu_result o) <$> di_drvfsel_diverge_offs
  = di_drvfsel_qemu_diverging.
Proof. solve_vtest di_drvfsel_qemu_diverging. Qed.

Lemma disk_ident_drvfsel_really_diverges :
  di_drvfsel_model_diverging <> di_drvfsel_qemu_diverging.
Proof. discriminate. Qed.
