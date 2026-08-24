(* DiskIdentQnum.v -- A QUEUE SIZE THE MODEL REFUSES.  Finding 1, from the
   other end: not "QueueNumMax reads 8 instead of 1024" but "the store the
   driver makes on the strength of that answer is STUCK".

   Source: tools/vtest/tests/disk_ident_qnum.S.  Capture: DiskIdentQnumGen.v.

   [VirtioModel.vq_size_ok] accepts {1,2,4,8} and [virtio_write] returns None
   for any other QueueNum, on purpose: the ring geometry divides by that
   number and the model refuses a configuration no real device would accept.
   But 16 IS a configuration a real device accepts -- QEMU has just reported
   QueueNumMax = 1024 in the very same program, which is recorded above --
   so the refusal lands on a legal driver.

   This is the concrete cost of finding 1: not a wrong value read, but every
   driver that believes QueueNumMax and sizes its queue accordingly having no
   model execution. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentQnumGen.
Local Open Scope Z_scope.

Definition di_qnum_start : mstate := start disk_ident_qnum_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model: STUCK, at exactly the access named in the header.         *)
(*                                                                         *)
(*    The pc below is cross-checked against the disassembly                *)
(*    riscv64-linux-gnu-objdump -d tools/vtest/build/disk_ident_qnum.elf, *)
(*    and names that access.  Every MMIO offset the program touches before  *)
(*    it is one the model DOES decode, so the model reaches the intended    *)
(*    access rather than tripping on something earlier -- and every address *)
(*    the program materialises comes from [li]/[lui], never [la], whose GOT *)
(*    load would be outside the [-j .text] image and would look like a      *)
(*    device finding while being nothing of the sort.                      *)
(* ---------------------------------------------------------------------- *)

Lemma disk_ident_qnum_model_stuck : run_status 50000 di_qnum_start = VStuck.
Proof. solve_vtest VStuck. Qed.

Lemma disk_ident_qnum_stuck_at : stuck_pc 50000 di_qnum_start = 0x800000a0.
Proof. solve_vtest (0x800000a0 : Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and the hardware COMPLETED the same program.  Read off the        *)
(*    capture, so it costs no model evaluation.                            *)
(* ---------------------------------------------------------------------- *)

Definition di_qnum_qemu : list Z :=
  (fun o => cap_word disk_ident_qnum_qemu_result o) <$> [8]%nat.

Definition di_qnum_qemu_expect : list Z := [1024].

Lemma disk_ident_qnum_qemu_completes : di_qnum_qemu = di_qnum_qemu_expect.
Proof. solve_vtest di_qnum_qemu_expect. Qed.

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
