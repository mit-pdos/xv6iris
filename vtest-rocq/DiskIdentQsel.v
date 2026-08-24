(* DiskIdentQsel.v -- A PER-QUEUE WRITE WITH A NON-ZERO QueueSel.

   Source: tools/vtest/tests/disk_ident_qsel.S.  Capture: DiskIdentQselGen.v.

   The model lets QueueSel be set to anything -- [virtio_write]'s queue-sel
   case is unconditional -- and then refuses EVERY per-queue write while it
   is not 0: QueueNum, QueueReady and all six queue-address halves each begin

     if negb (bv_unsigned (vc_qsel c) =? 0) then None else ...

   so the machine is stuck rather than the write being ignored.  Reads are
   different: [virtio_read] answers QueueNumMax and QueueReady at a non-zero
   selection with 0, which is what QEMU does too and what the recorded value
   above shows -- so a driver may LOOK at queue 1 and may not TOUCH it.

   QEMU ignores the write: queue 1 does not exist, and virtio_queue_set_num
   declines to move a queue between existent and non-existent.  So a driver
   that probes the queues by walking QueueSel upward and writing as it goes
   completes on hardware and has no model execution. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentQselGen.
Local Open Scope Z_scope.

Definition di_qsel_start : mstate := start disk_ident_qsel_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model: STUCK, at exactly the access named in the header.         *)
(*                                                                         *)
(*    The pc below is cross-checked against the disassembly                *)
(*    riscv64-linux-gnu-objdump -d tools/vtest/build/disk_ident_qsel.elf, *)
(*    and names that access.  Every MMIO offset the program touches before  *)
(*    it is one the model DOES decode, so the model reaches the intended    *)
(*    access rather than tripping on something earlier -- and every address *)
(*    the program materialises comes from [li]/[lui], never [la], whose GOT *)
(*    load would be outside the [-j .text] image and would look like a      *)
(*    device finding while being nothing of the sort.                      *)
(* ---------------------------------------------------------------------- *)

Lemma disk_ident_qsel_model_stuck : run_status 50000 di_qsel_start = VStuck.
Proof. solve_vtest VStuck. Qed.

Lemma disk_ident_qsel_stuck_at : stuck_pc 50000 di_qsel_start = 0x800000a4.
Proof. solve_vtest (0x800000a4 : Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and the hardware COMPLETED the same program.  Read off the        *)
(*    capture, so it costs no model evaluation.                            *)
(* ---------------------------------------------------------------------- *)

Definition di_qsel_qemu : list Z :=
  (fun o => cap_word disk_ident_qsel_qemu_result o) <$> [8]%nat.

Definition di_qsel_qemu_expect : list Z := [0].

Lemma disk_ident_qsel_qemu_completes : di_qsel_qemu = di_qsel_qemu_expect.
Proof. solve_vtest di_qsel_qemu_expect. Qed.

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
