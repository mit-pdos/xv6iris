(* DiskIdentFeatsel.v -- DeviceFeaturesSel (0x014).  FINDING 3, first half,
   which had no landed test until this one.

   Source: tools/vtest/tests/disk_ident_featsel.S.  Capture:
   DiskIdentFeatselGen.v.

   The device's feature word is 64 bits and the DeviceFeatures register
   (0x010) is 32; DeviceFeaturesSel picks which half it reports.  [virtio_
   write] has no case for 0x014, so the store is None and the machine is
   stuck -- the model's DeviceFeatures is a constant, and the high half of
   the feature word simply cannot be READ.

   That is not a cosmetic gap.  Bit 32 is VIRTIO_F_VERSION_1, which virtio
   1.x REQUIRES every driver to negotiate; QEMU's high half here is 0x101,
   i.e. VERSION_1 (bit 32) and VIRTIO_F_RING_RESET (bit 40).  See
   DiskIdentDrvfsel.v for the acknowledgement side. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentFeatselGen.
Local Open Scope Z_scope.

Definition di_featsel_start : mstate := start disk_ident_featsel_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model: STUCK, at exactly the access named in the header.         *)
(*                                                                         *)
(*    The pc below is cross-checked against the disassembly                *)
(*    riscv64-linux-gnu-objdump -d tools/vtest/build/disk_ident_featsel.elf, *)
(*    and names that access.  Every MMIO offset the program touches before  *)
(*    it is one the model DOES decode, so the model reaches the intended    *)
(*    access rather than tripping on something earlier -- and every address *)
(*    the program materialises comes from [li]/[lui], never [la], whose GOT *)
(*    load would be outside the [-j .text] image and would look like a      *)
(*    device finding while being nothing of the sort.                      *)
(* ---------------------------------------------------------------------- *)

Lemma disk_ident_featsel_model_stuck : run_status 50000 di_featsel_start = VStuck.
Proof. solve_vtest VStuck. Qed.

Lemma disk_ident_featsel_stuck_at : stuck_pc 50000 di_featsel_start = 0x8000009c.
Proof. solve_vtest (0x8000009c : Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and the hardware COMPLETED the same program.  Read off the        *)
(*    capture, so it costs no model evaluation.                            *)
(* ---------------------------------------------------------------------- *)

Definition di_featsel_qemu : list Z :=
  (fun o => cap_word disk_ident_featsel_qemu_result o) <$> [8; 12]%nat.

Definition di_featsel_qemu_expect : list Z := [805334612; 257].

Lemma disk_ident_featsel_qemu_completes : di_featsel_qemu = di_featsel_qemu_expect.
Proof. solve_vtest di_featsel_qemu_expect. Qed.

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
