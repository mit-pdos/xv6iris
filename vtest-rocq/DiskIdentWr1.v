(* DiskIdentWr1.v -- A ONE-BYTE WRITE to the virtio window.

   Source: tools/vtest/tests/disk_ident_wr1.S.  Capture: DiskIdentWr1Gen.v.

   The write half of the width restriction: [DevModel.dev_write]'s virtio arm
   also matches width 4 and nothing else, so [sb] to Status is stuck.

   The QEMU side is the interesting half.  The hardware completes the
   transaction and DROPS it -- guest-error log, no state change -- so Status
   reads 11 both before and after the byte store of 15.  A real driver that
   made this mistake would see its DRIVER_OK silently not take effect and
   would hang; the model instead has nothing to say about it at all.  The two
   are different failures, and only the hardware's is one a proof could
   describe. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentWr1Gen.
Local Open Scope Z_scope.

Definition di_wr1_start : mstate := start disk_ident_wr1_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model: STUCK, at exactly the access named in the header.         *)
(*                                                                         *)
(*    The pc below is cross-checked against the disassembly                *)
(*    riscv64-linux-gnu-objdump -d tools/vtest/build/disk_ident_wr1.elf, *)
(*    and names that access.  Every MMIO offset the program touches before  *)
(*    it is one the model DOES decode, so the model reaches the intended    *)
(*    access rather than tripping on something earlier -- and every address *)
(*    the program materialises comes from [li]/[lui], never [la], whose GOT *)
(*    load would be outside the [-j .text] image and would look like a      *)
(*    device finding while being nothing of the sort.                      *)
(* ---------------------------------------------------------------------- *)

Lemma disk_ident_wr1_model_stuck : run_status 50000 di_wr1_start = VStuck.
Proof. solve_vtest VStuck. Qed.

Lemma disk_ident_wr1_stuck_at : stuck_pc 50000 di_wr1_start = 0x8000009c.
Proof. solve_vtest (0x8000009c : Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and the hardware COMPLETED the same program.  Read off the        *)
(*    capture, so it costs no model evaluation.                            *)
(* ---------------------------------------------------------------------- *)

Definition di_wr1_qemu : list Z :=
  (fun o => cap_word disk_ident_wr1_qemu_result o) <$> [8; 12]%nat.

Definition di_wr1_qemu_expect : list Z := [11; 11].

Lemma disk_ident_wr1_qemu_completes : di_wr1_qemu = di_wr1_qemu_expect.
Proof. solve_vtest di_wr1_qemu_expect. Qed.

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
