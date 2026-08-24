(* DiskIdentQreset.v -- QueueReset (0x0c0).

   Source: tools/vtest/tests/disk_ident_qreset.S.  Capture:
   DiskIdentQresetGen.v.

   Per-queue reset, virtio 1.2's VIRTIO_F_RING_RESET.  Note the offset:
   0x0c0.  (0x08c is not a virtio-mmio register at all; the register between
   QueueReady and QueueNotify does not exist.)  Not decoded by the model, so
   the load is stuck.

   This one is not hypothetical for THIS device: DiskIdentFeatsel.v records
   QEMU's high feature word as 0x101, whose bit 8 is bit 40 of the whole
   word -- VIRTIO_F_RING_RESET.  The hardware under test OFFERS the feature
   whose register the model does not decode.

   The WRITE that would actually reset the queue is stuck too; it is not
   attempted here, because once the model is stuck the run is over and one
   program can pin only one refused access. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentQresetGen.
Local Open Scope Z_scope.

Definition di_qreset_start : mstate := start disk_ident_qreset_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model: STUCK, at exactly the access named in the header.         *)
(*                                                                         *)
(*    The pc below is cross-checked against the disassembly                *)
(*    riscv64-linux-gnu-objdump -d tools/vtest/build/disk_ident_qreset.elf, *)
(*    and names that access.  Every MMIO offset the program touches before  *)
(*    it is one the model DOES decode, so the model reaches the intended    *)
(*    access rather than tripping on something earlier -- and every address *)
(*    the program materialises comes from [li]/[lui], never [la], whose GOT *)
(*    load would be outside the [-j .text] image and would look like a      *)
(*    device finding while being nothing of the sort.                      *)
(* ---------------------------------------------------------------------- *)

Lemma disk_ident_qreset_model_stuck : run_status 50000 di_qreset_start = VStuck.
Proof. solve_vtest VStuck. Qed.

Lemma disk_ident_qreset_stuck_at : stuck_pc 50000 di_qreset_start = 0x80000094.
Proof. solve_vtest (0x80000094 : Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and the hardware COMPLETED the same program.  Read off the        *)
(*    capture, so it costs no model evaluation.                            *)
(* ---------------------------------------------------------------------- *)

Definition di_qreset_qemu : list Z :=
  (fun o => cap_word disk_ident_qreset_qemu_result o) <$> [8]%nat.

Definition di_qreset_qemu_expect : list Z := [0].

Lemma disk_ident_qreset_qemu_completes : di_qreset_qemu = di_qreset_qemu_expect.
Proof. solve_vtest di_qreset_qemu_expect. Qed.

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
