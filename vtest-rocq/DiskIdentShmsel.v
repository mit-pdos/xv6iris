(* DiskIdentShmsel.v -- SHMSel (0x0ac) and the shared-memory registers.

   Source: tools/vtest/tests/disk_ident_shmsel.S.  Capture:
   DiskIdentShmselGen.v.

   A driver discovers a device's shared-memory regions by writing a region id
   to SHMSel and reading SHMLen/SHMBase (0x0b0..0x0bc) back; an all-ones
   length means "no such region".  None of the five registers is decoded, so
   the SELECT is already stuck and the four reads after it are never reached.

   QEMU answers the probe honestly: length 0xffffffff_ffffffff, i.e. this
   virtio-blk device has no shared-memory region 0.  So the model cannot even
   express a driver ASKING a question whose answer is "no". *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentShmselGen.
Local Open Scope Z_scope.

Definition di_shmsel_start : mstate := start disk_ident_shmsel_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model: STUCK, at exactly the access named in the header.         *)
(*                                                                         *)
(*    The pc below is cross-checked against the disassembly                *)
(*    riscv64-linux-gnu-objdump -d tools/vtest/build/disk_ident_shmsel.elf, *)
(*    and names that access.  Every MMIO offset the program touches before  *)
(*    it is one the model DOES decode, so the model reaches the intended    *)
(*    access rather than tripping on something earlier -- and every address *)
(*    the program materialises comes from [li]/[lui], never [la], whose GOT *)
(*    load would be outside the [-j .text] image and would look like a      *)
(*    device finding while being nothing of the sort.                      *)
(* ---------------------------------------------------------------------- *)

Lemma disk_ident_shmsel_model_stuck : run_status 50000 di_shmsel_start = VStuck.
Proof. solve_vtest VStuck. Qed.

Lemma disk_ident_shmsel_stuck_at : stuck_pc 50000 di_shmsel_start = 0x80000090.
Proof. solve_vtest (0x80000090 : Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and the hardware COMPLETED the same program.  Read off the        *)
(*    capture, so it costs no model evaluation.                            *)
(* ---------------------------------------------------------------------- *)

Definition di_shmsel_qemu : list Z :=
  (fun o => cap_word disk_ident_shmsel_qemu_result o) <$> [8; 12]%nat.

Definition di_shmsel_qemu_expect : list Z := [4294967295; 4294967295].

Lemma disk_ident_shmsel_qemu_completes : di_shmsel_qemu = di_shmsel_qemu_expect.
Proof. solve_vtest di_shmsel_qemu_expect. Qed.

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
