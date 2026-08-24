(* DiskIdentRd1.v -- A ONE-BYTE READ of the virtio window.

   Source: tools/vtest/tests/disk_ident_rd1.S.  Capture: DiskIdentRd1Gen.v.

   [DevModel.dev_read] decodes the virtio window at WIDTH 4 ONLY:

     else if in_virtio a then
       match n with 4%N => ... | _ => None end

   so an [lbu] anywhere in the window is stuck whatever the offset -- here it
   is byte 0 of MagicValue.  The width restriction is a property of the BUS
   decode, not of any register, so it applies to all 4096 bytes of the
   window including the config space.

   QEMU does not fault either: virtio_mmio_read logs a guest error for any
   width but 4 below the config space and returns 0.  So the hardware
   COMPLETES the access -- with a defined value -- where the model has no
   transition, which is what makes this an incompleteness rather than two
   machines agreeing to refuse. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentRd1Gen.
Local Open Scope Z_scope.

Definition di_rd1_start : mstate := start disk_ident_rd1_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model: STUCK, at exactly the access named in the header.         *)
(*                                                                         *)
(*    The pc below is cross-checked against the disassembly                *)
(*    riscv64-linux-gnu-objdump -d tools/vtest/build/disk_ident_rd1.elf, *)
(*    and names that access.  Every MMIO offset the program touches before  *)
(*    it is one the model DOES decode, so the model reaches the intended    *)
(*    access rather than tripping on something earlier -- and every address *)
(*    the program materialises comes from [li]/[lui], never [la], whose GOT *)
(*    load would be outside the [-j .text] image and would look like a      *)
(*    device finding while being nothing of the sort.                      *)
(* ---------------------------------------------------------------------- *)

Lemma disk_ident_rd1_model_stuck : run_status 50000 di_rd1_start = VStuck.
Proof. solve_vtest VStuck. Qed.

Lemma disk_ident_rd1_stuck_at : stuck_pc 50000 di_rd1_start = 0x80000090.
Proof. solve_vtest (0x80000090 : Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and the hardware COMPLETED the same program.  Read off the        *)
(*    capture, so it costs no model evaluation.                            *)
(* ---------------------------------------------------------------------- *)

Definition di_rd1_qemu : list Z :=
  (fun o => cap_word disk_ident_rd1_qemu_result o) <$> [8]%nat.

Definition di_rd1_qemu_expect : list Z := [0].

Lemma disk_ident_rd1_qemu_completes : di_rd1_qemu = di_rd1_qemu_expect.
Proof. solve_vtest di_rd1_qemu_expect. Qed.

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
