(* DiskIdentDrvfsel.v -- DriverFeaturesSel (0x024).  FINDING 3, second half.

   Source: tools/vtest/tests/disk_ident_drvfsel.S.  Capture:
   DiskIdentDrvfselGen.v.

   DeviceFeaturesSel (DiskIdentFeatsel.v) is how a driver READS the high half
   of the feature word; DriverFeaturesSel is how it ACKNOWLEDGES it.  Neither
   is decoded, so the store is stuck and VIRTIO_F_VERSION_1 can be neither
   read nor acked: a spec-conforming modern driver is outside the model
   ENTIRELY, not merely restricted by it.

   After the stuck store the program does, on QEMU only, exactly the
   negotiation such a driver performs -- ack the low half, select the high
   half, ack VERSION_1, then FEATURES_OK -- and reads Status back.  QEMU
   answers 11: FEATURES_OK stuck, the device accepted the set.  That whole
   sequence has no model execution. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentDrvfselGen.
Local Open Scope Z_scope.

Definition di_drvfsel_start : mstate := start disk_ident_drvfsel_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model: STUCK, at exactly the access named in the header.         *)
(*                                                                         *)
(*    The pc below is cross-checked against the disassembly                *)
(*    riscv64-linux-gnu-objdump -d tools/vtest/build/disk_ident_drvfsel.elf, *)
(*    and names that access.  Every MMIO offset the program touches before  *)
(*    it is one the model DOES decode, so the model reaches the intended    *)
(*    access rather than tripping on something earlier -- and every address *)
(*    the program materialises comes from [li]/[lui], never [la], whose GOT *)
(*    load would be outside the [-j .text] image and would look like a      *)
(*    device finding while being nothing of the sort.                      *)
(* ---------------------------------------------------------------------- *)

Lemma disk_ident_drvfsel_model_stuck : run_status 50000 di_drvfsel_start = VStuck.
Proof. solve_vtest VStuck. Qed.

Lemma disk_ident_drvfsel_stuck_at : stuck_pc 50000 di_drvfsel_start = 0x8000009c.
Proof. solve_vtest (0x8000009c : Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and the hardware COMPLETED the same program.  Read off the        *)
(*    capture, so it costs no model evaluation.                            *)
(* ---------------------------------------------------------------------- *)

Definition di_drvfsel_qemu : list Z :=
  (fun o => cap_word disk_ident_drvfsel_qemu_result o) <$> [8; 12; 16]%nat.

Definition di_drvfsel_qemu_expect : list Z := [805334612; 257; 11].

Lemma disk_ident_drvfsel_qemu_completes : di_drvfsel_qemu = di_drvfsel_qemu_expect.
Proof. solve_vtest di_drvfsel_qemu_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. CLASSIFICATION: INCOMPLETENESS.                                      *)
(*                                                                         *)
(*    A stuck machine is NOT unsoundness.  The system theorem proves xv6    *)
(*    never gets stuck, so a state with no transition is never reached and  *)
(*    no proof can be wrong because of one.  What it costs is COVERAGE: a   *)
(*    driver that performs this access has no model execution at all, so it *)
(*    cannot be verified in this development.  Each such access is one more *)
(*    driver the semantics cannot describe.                                *)
(* ---------------------------------------------------------------------- *)
