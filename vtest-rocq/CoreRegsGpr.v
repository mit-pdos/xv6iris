(* ======================================================================= *)
(* CoreRegsGpr.v -- THE 31 GENERAL-PURPOSE REGISTERS AT BOOT.               *)
(*                                                                          *)
(* Source: tools/vtest/tests/core_regs_gpr.S.  Capture: CoreRegsGprGen.v.    *)
(*                                                                          *)
(* THIS FILE FOLLOWS VBoot.v's FOUR-STEP PROCEDURE and it has to: the model  *)
(* does not pin the power-on register file ([RiscvLang.boot_facts]           *)
(* quantifies [rs0] EXISTENTIALLY), so a raw diff of the DEFAULT boot        *)
(* against QEMU would report a scratch register as a divergence when all it  *)
(* means is that the two machines' garbage differs.  Step 1 is [gpr_run]     *)
(* below (from [init_regstate], which is what [VTest.start] uses); step 2 is *)
(* [gpr_witness]; step 3 is [core_regs_gpr_a2_witnessed]; step 4 -- the only *)
(* real finding -- is section 3.                                            *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S: x<i> is the 8-byte              *)
(* little-endian word at 8*i, i = 1..31.  x0 is not stored.                 *)
(*                                                                          *)
(* WHAT `AT BOOT` MEANS HERE.  vtest.S's prologue runs before _vtest_body,   *)
(* so six of the 31 are values the PROLOGUE wrote and not power-on values:   *)
(*   x1 ra = 0x8000002c (the return address of `jal ra, _vtest_body`)        *)
(*   x2 sp = 0x80091000, x6 t1 = 0x80091000, x7 t2 = 0 (the stack carve)     *)
(*   x5 t0 = 0 (mhartid, read by the prologue's csrr)                        *)
(*   x27 s11 = 0x80100000 (RESULT_BASE, the ABI-reserved result cursor)      *)
(* Those six agreeing is a check on the image and the ABI rather than on the *)
(* boot contract; the other 25 are the boot contract itself.                 *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VBoot CoreRegsGprGen.
Local Open Scope Z_scope.

(* a 64-bit result-region field, out of either side, as one number *)
Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

(* ---------------------------------------------------------------------- *)
(* 1. STEP 1 -- the DEFAULT boot, diffed against QEMU.                      *)
(*                                                                         *)
(*    29 of the 31 agree outright.  a1 (x11) and a2 (x12) do not, and       *)
(*    those two are the whole content of this test.                        *)
(* ---------------------------------------------------------------------- *)

Definition gpr_run : option mstate := run_until 600 (start core_regs_gpr_text).

(* every x<i> except a1 (x11, at +88) and a2 (x12, at +96) *)
Definition gpr_agree_offs : list nat :=
  [8; 16; 24; 32; 40; 48; 56; 64; 72; 80;
   104; 112; 120; 128; 136; 144; 152; 160; 168; 176;
   184; 192; 200; 208; 216; 224; 232; 240; 248]%nat.

(* ONE evaluation: the 29 that agree, plus the model's own values for the
   two that do not, so section 2 and section 3 cost no further runs. *)
Definition gpr_expect :=
  ((fun o => cap_dw core_regs_gpr_qemu_result o) <$> gpr_agree_offs,
   0x1000, 0).

Lemma core_regs_gpr_default :
  ((fun o => res_dw gpr_run o) <$> gpr_agree_offs,
   res_dw gpr_run 88%nat, res_dw gpr_run 96%nat) = gpr_expect.
Proof. solve_vtest gpr_expect. Qed.

(* ...and what QEMU put in those two. *)
Lemma core_regs_gpr_qemu_a1a2 :
  (cap_dw core_regs_gpr_qemu_result 88%nat,
   cap_dw core_regs_gpr_qemu_result 96%nat) = (0x87e00000, 0x1028).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. STEP 2/3 -- a2 IS NONDETERMINISTIC, AND THE MODEL ADMITS QEMU'S      *)
(*    VALUE.  NO FINDING.                                                  *)
(*                                                                         *)
(*    Nothing in the boot chain writes a2: [ArchReset.board_regs] does not  *)
(*    name it, and [init_boot_requirements] writes a0 and a1 and stops.  So *)
(*    a2 = 0 under the default boot is [init_regstate]'s zero showing       *)
(*    through, not a claim.  Preset it in the POWER-ON file to what QEMU's  *)
(*    reset ROM leaves there (0x1028, the pointer to the fw_dynamic info    *)
(*    struct the virt board stages at 0x1000) and the model reproduces      *)
(*    QEMU's run exactly.  That is the model ADMITTING the hardware's       *)
(*    value, which is all the one-directional question asks.                *)
(*                                                                         *)
(*    The same argument covers every other scratch register in the file:    *)
(*    both machines happen to show 0, so no witness is needed to see it,    *)
(*    but none of those zeros is pinned by the model either.               *)
(* ---------------------------------------------------------------------- *)

Definition gpr_a2 : Z := 0x1028.

Definition gpr_rs0 : regstate :=
  poison [pset (register_set (R_bitvector_64 x12)
                             (SailStdpp.Values.mword_of_int (len:=64) gpr_a2))]
         init_regstate.

Definition gpr_witness : option mstate :=
  run_from 600 0 gpr_rs0 core_regs_gpr_text std_regions.

Lemma core_regs_gpr_a2_witnessed : res_dw gpr_witness 96%nat = gpr_a2.
Proof. solve_vtest gpr_a2. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. STEP 4 -- a1 IS PINNED BY THE BOOT CHAIN, AND TO A VALUE THE          *)
(*    HARDWARE DOES NOT PRODUCE.  THIS IS THE FINDING.                     *)
(*                                                                         *)
(*    Presetting a1 in [rs0] does NOT help, because the chain overwrites    *)
(*    it: rv64d's [init_boot_requirements] is                               *)
(*                                                                         *)
(*      a0 := mhartid ;  a1 := 0x1000                                       *)
(*                                                                         *)
(*    -- a HARDCODED device-tree address baked into the Sail model.  On the *)
(*    virt board QEMU stages the flattened device tree near the top of RAM  *)
(*    and passes its real address, 0x87e00000 for this -m 128M run, and     *)
(*    that address MOVES with the memory size and the image, so no constant *)
(*    could have been right.  0x1000 is where virt's reset ROM lives, not   *)
(*    where the DTB is.                                                     *)
(*                                                                         *)
(*    CLASSIFICATION: a defect in the BOOT CONTRACT, and a narrow one.  A   *)
(*    kernel that reads a1 to find its device tree -- which is what the     *)
(*    firmware hand-off is for -- would be verified against an address the  *)
(*    machine never passes.  It is harmless for xv6 in this tree only        *)
(*    because xv6 hard-codes its device addresses and never dereferences    *)
(*    a1; nothing in the proofs consumes a1's value.  a0 is fine (both      *)
(*    machines pass the hart id, 0 here).                                   *)
(*                                                                         *)
(*    The fix would be to make the DTB address a PARAMETER of the boot      *)
(*    program the way [hid] already is, rather than a constant of the        *)
(*    generated model -- which is a change to rv64d.v (generated) or a      *)
(*    board write in ArchReset.v, so it is a decision, not a drive-by edit. *)
(*                                                                         *)
(*    Pinned on BOTH sides, per the suite's convention: the model-side      *)
(*    equation goes red the day someone changes this, which is exactly when *)
(*    this file should be revisited.                                        *)
(* ---------------------------------------------------------------------- *)

Definition gpr_a1_model : Z := 0x1000.
Definition gpr_a1_qemu  : Z := 0x87e00000.

(* the model's value, EVEN AFTER PRESETTING a1 TO QEMU'S: the chain wins *)
Definition gpr_rs0_a1 : regstate :=
  poison [pset (register_set (R_bitvector_64 x11)
                             (SailStdpp.Values.mword_of_int (len:=64) gpr_a1_qemu))]
         init_regstate.

Definition gpr_witness_a1 : option mstate :=
  run_from 600 0 gpr_rs0_a1 core_regs_gpr_text std_regions.

Lemma core_regs_gpr_a1_model : res_dw gpr_witness_a1 88%nat = gpr_a1_model.
Proof. solve_vtest gpr_a1_model. Qed.

Lemma core_regs_gpr_a1_qemu :
  cap_dw core_regs_gpr_qemu_result 88%nat = gpr_a1_qemu.
Proof. reflexivity. Qed.

Lemma core_regs_gpr_a1_really_diverges : gpr_a1_model <> gpr_a1_qemu.
Proof. discriminate. Qed.

(* ...and the run touched no disk, as QEMU's did not. *)
Lemma core_regs_gpr_disk : core_regs_gpr_qemu_disk = [].
Proof. reflexivity. Qed.
