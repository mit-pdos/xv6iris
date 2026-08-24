(* DiskIdentNotify.v -- QueueNotify NAMING A QUEUE THAT DOES NOT EXIST.

   Source: tools/vtest/tests/disk_ident_notify.S.  Capture:
   DiskIdentNotifyGen.v.

   [virtio_write]'s queue-notify case is

     if negb (bv_unsigned w =? 0) then None else Some v

   -- a notification is a hint this device does not need, but naming any
   queue but 0 is refused rather than ignored.  QEMU checks the index against
   VIRTIO_QUEUE_MAX, finds queue 1 has no descriptor ring, and drops it.

   Of the twelve refused accesses in the stuck matrix this is the one least
   likely to matter in practice -- a driver has little reason to notify a
   queue it never configured -- and it is recorded for completeness of the
   scoreboard rather than as a gap worth closing. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentNotifyGen.
Local Open Scope Z_scope.

Definition di_notify_start : mstate := start disk_ident_notify_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model: STUCK, at exactly the access named in the header.         *)
(*                                                                         *)
(*    The pc below is cross-checked against the disassembly                *)
(*    riscv64-linux-gnu-objdump -d tools/vtest/build/disk_ident_notify.elf, *)
(*    and names that access.  Every MMIO offset the program touches before  *)
(*    it is one the model DOES decode, so the model reaches the intended    *)
(*    access rather than tripping on something earlier -- and every address *)
(*    the program materialises comes from [li]/[lui], never [la], whose GOT *)
(*    load would be outside the [-j .text] image and would look like a      *)
(*    device finding while being nothing of the sort.                      *)
(* ---------------------------------------------------------------------- *)

Lemma disk_ident_notify_model_stuck : run_status 50000 di_notify_start = VStuck.
Proof. solve_vtest VStuck. Qed.

Lemma disk_ident_notify_stuck_at : stuck_pc 50000 di_notify_start = 0x8000009c.
Proof. solve_vtest (0x8000009c : Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and the hardware COMPLETED the same program.  Read off the        *)
(*    capture, so it costs no model evaluation.                            *)
(* ---------------------------------------------------------------------- *)

Definition di_notify_qemu : list Z :=
  (fun o => cap_word disk_ident_notify_qemu_result o) <$> [8]%nat.

Definition di_notify_qemu_expect : list Z := [11].

Lemma disk_ident_notify_qemu_completes : di_notify_qemu = di_notify_qemu_expect.
Proof. solve_vtest di_notify_qemu_expect. Qed.

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
