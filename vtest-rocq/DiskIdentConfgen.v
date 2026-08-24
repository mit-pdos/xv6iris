(* DiskIdentConfgen.v -- ConfigGeneration (0x0fc).

   Source: tools/vtest/tests/disk_ident_confgen.S.  Capture:
   DiskIdentConfgenGen.v.

   The register a driver reads before and after a config-space read so it can
   detect that the device changed the configuration underneath it (virtio
   spec 4.2.2.2 / 2.4.1).  Not decoded: the load is stuck.  Together with
   DiskIdentCap.v this means the whole config-space protocol -- the values
   AND the generation counter that makes reading them atomic -- is outside
   the model. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentConfgenGen.
Local Open Scope Z_scope.

Definition di_confgen_start : mstate := start disk_ident_confgen_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model: STUCK, at exactly the access named in the header.         *)
(*                                                                         *)
(*    The pc below is cross-checked against the disassembly                *)
(*    riscv64-linux-gnu-objdump -d tools/vtest/build/disk_ident_confgen.elf, *)
(*    and names that access.  Every MMIO offset the program touches before  *)
(*    it is one the model DOES decode, so the model reaches the intended    *)
(*    access rather than tripping on something earlier -- and every address *)
(*    the program materialises comes from [li]/[lui], never [la], whose GOT *)
(*    load would be outside the [-j .text] image and would look like a      *)
(*    device finding while being nothing of the sort.                      *)
(* ---------------------------------------------------------------------- *)

Lemma disk_ident_confgen_model_stuck : run_status 50000 di_confgen_start = VStuck.
Proof. solve_vtest VStuck. Qed.

Lemma disk_ident_confgen_stuck_at : stuck_pc 50000 di_confgen_start = 0x80000090.
Proof. solve_vtest (0x80000090 : Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and the hardware COMPLETED the same program.  Read off the        *)
(*    capture, so it costs no model evaluation.                            *)
(* ---------------------------------------------------------------------- *)

Definition di_confgen_qemu : list Z :=
  (fun o => cap_word disk_ident_confgen_qemu_result o) <$> [8]%nat.

Definition di_confgen_qemu_expect : list Z := [0].

Lemma disk_ident_confgen_qemu_completes : di_confgen_qemu = di_confgen_qemu_expect.
Proof. solve_vtest di_confgen_qemu_expect. Qed.

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
