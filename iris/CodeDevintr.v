(* CodeDevintr.v -- decode templates + [instr] facts for devintr()'s
   instructions at KernelSyms.devintr = 0x8000250c.

   devintr's 32-byte frame (ra/s0, and s1 SHRINK-WRAPPED into the PLIC arm --
   [c.sdsp s1,8(sp)] is the FIRST instruction of that arm, at +0x2a, and the
   two exits from it each reload s1 before jumping to the common epilogue) is
   byte-identical to uartintr's, so the prologue/epilogue words come from
   KernelRvcDecode.v's shared [cdec_*] set.  Five more of devintr's words had
   exactly one private copy elsewhere in the tree and were promoted to the
   shared catalogs when devintr became their second user ([cdec_4505],
   [cdec_872a], [cdec_a801], [cdec_bf5d], [cdec_bff1]; [bdec_04f70863],
   [bdec_f3dff0ef]).  What is left here is devintr's own.

   +0x54 .. +0x61 -- [mv a1,a4; auipc a0,0x5; addi a0,a0,-786; jal printk],
   the "unexpected interrupt irq=%d" arm -- IS NOT DECODED, because it is
   DEAD: [PlicPlan.plic_claim_ret_ok] bounds a claim's result to
   {0, uart_irq_id, virtio_irq_id}, the two [beq]s above have already taken
   the two nonzero cases, and the [c.bnez a4] at +0x42 therefore provably
   falls through.  See ProofDevintr.v. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpDecodeBridge.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
Require Import WpGprCsrrB.
Require Import KernelRvcDecode KernelBaseDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts unique to devintr.                             *)
(* ===================================================================== *)

(* 0x17fe  c.slli a5,a5,0x3f  (twice: the scause literals' sign bit) *)
Lemma didc_17fe s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x17fe : mword 16)) s
  = Some (C_SLLI (mword_of_int 63, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x07a5  c.addi a5,a5,9   (scause == 0x8000000000000009: external) *)
Lemma didc_07a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x07a5 : mword 16)) s
  = Some (C_ADDI (mword_of_int 9, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0795  c.addi a5,a5,5   (scause == 0x8000000000000005: timer) *)
Lemma didc_0795 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0795 : mword 16)) s
  = Some (C_ADDI (mword_of_int 5, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x47a9  c.li a5,10  (UART0_IRQ) *)
Lemma didc_47a9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x47a9 : mword 16)) s
  = Some (C_LI (mword_of_int 10, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4509  c.li a0,2   (the timer arm's return value) *)
Lemma didc_4509 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4509 : mword 16)) s
  = Some (C_LI (mword_of_int 2, Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xeb09  c.bnez a4,+0x12  (the DEAD printk arm) *)
Lemma didc_eb09 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xeb09 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 9, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa819  c.j +0x16  (uartintr rejoins at the plic_complete) *)
Lemma didc_a819 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa819 : mword 16)) s
  = Some (C_J (mword_of_int 11 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (32-bit) decode facts unique to devintr.                          *)
(* ===================================================================== *)

(* 0x14202773  csrr a4,scause *)
Lemma didb_14202773 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x14202773 : mword 32)) s
  = Some (CSRReg (csr_scause, zreg, Regidx (mword_of_int 14), CSRRS), s).
Proof. decode_bridge_ms. Qed.

(* 0x00f70c63  beq a4,a5,+0x18  (external -> the PLIC arm) *)
Lemma didb_00f70c63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f70c63 : mword 32)) s
  = Some (BTYPE (mword_of_int 24 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x00f50963  beq a0,a5,+0x12  -- BOTH irq tests, at +0x36 and +0x3c *)
Lemma didb_00f50963 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f50963 : mword 32)) s
  = Some (BTYPE (mword_of_int 18 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 10), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* the four jals: plic_claim / uartintr / virtio_disk_intr / plic_complete *)
Lemma didb_795020ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x795020ef : mword 32)) s
  = Some (JAL (mword_of_int 12180 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma didb_c7afe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc7afe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2090106 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma didb_408030ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x408030ef : mword 32)) s
  = Some (JAL (mword_of_int 13320 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma didb_77d020ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x77d020ef : mword 32)) s
  = Some (JAL (mword_of_int 12156 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Section CodeDevintr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation DI := KernelSyms.devintr.

  (* --- prologue (+0x00 .. +0x06): the 32-byte frame, without s1 --- *)
  Lemma dii_00 : kernel_text -∗ instr (mword_of_int (DI + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (DI + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (DI + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma dii_02 : kernel_text -∗ instr (mword_of_int (DI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (DI + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (DI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma dii_04 : kernel_text -∗ instr (mword_of_int (DI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (DI + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (DI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma dii_06 : kernel_text -∗ instr (mword_of_int (DI + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (DI + 0x06)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (DI + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* --- the cause read and the two literal comparisons (+0x08 .. +0x1e) --- *)
  Lemma dii_08 : kernel_text -∗ instr (mword_of_int (DI + 0x08) : mword 64) false (CSRReg (csr_scause, zreg, Regidx (mword_of_int 14), CSRRS)).
  Proof. mk_base (DI + 0x08)%Z (mword_of_int 0x14202773 : mword 32)
    (mword_of_int (DI + 0x08) : mword 64) (CSRReg (csr_scause, zreg, Regidx (mword_of_int 14), CSRRS)) didb_14202773. Qed.

  Lemma dii_0c : kernel_text -∗ instr (mword_of_int (DI + 0x0c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (DI + 0x0c)%Z (mword_of_int 0x57fd : mword 16)
    (mword_of_int (DI + 0x0c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_57fd exec_execute_C_LI. Qed.

  Lemma dii_0e : kernel_text -∗ instr (mword_of_int (DI + 0x0e) : mword 64) true (SHIFTIOP (mword_of_int 63 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (DI + 0x0e)%Z (mword_of_int 0x17fe : mword 16)
    (mword_of_int (DI + 0x0e) : mword 64) (SHIFTIOP (mword_of_int 63 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) didc_17fe exec_execute_C_SLLI. Qed.

  Lemma dii_10 : kernel_text -∗ instr (mword_of_int (DI + 0x10) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 9 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (DI + 0x10)%Z (mword_of_int 0x07a5 : mword 16)
    (mword_of_int (DI + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 9 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) didc_07a5 exec_execute_C_ADDI. Qed.

  Lemma dii_12 : kernel_text -∗ instr (mword_of_int (DI + 0x12) : mword 64) false (BTYPE (mword_of_int 24 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)).
  Proof. mk_base (DI + 0x12)%Z (mword_of_int 0x00f70c63 : mword 32)
    (mword_of_int (DI + 0x12) : mword 64) (BTYPE (mword_of_int 24 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)) didb_00f70c63. Qed.

  Lemma dii_16 : kernel_text -∗ instr (mword_of_int (DI + 0x16) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (DI + 0x16)%Z (mword_of_int 0x57fd : mword 16)
    (mword_of_int (DI + 0x16) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_57fd exec_execute_C_LI. Qed.

  Lemma dii_18 : kernel_text -∗ instr (mword_of_int (DI + 0x18) : mword 64) true (SHIFTIOP (mword_of_int 63 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (DI + 0x18)%Z (mword_of_int 0x17fe : mword 16)
    (mword_of_int (DI + 0x18) : mword 64) (SHIFTIOP (mword_of_int 63 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) didc_17fe exec_execute_C_SLLI. Qed.

  Lemma dii_1a : kernel_text -∗ instr (mword_of_int (DI + 0x1a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (DI + 0x1a)%Z (mword_of_int 0x0795 : mword 16)
    (mword_of_int (DI + 0x1a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) didc_0795 exec_execute_C_ADDI. Qed.

  (* a0 := 0 -- the "not recognised" return value, materialised BEFORE the
     timer test because both remaining paths fall through this instruction *)
  Lemma dii_1c : kernel_text -∗ instr (mword_of_int (DI + 0x1c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (DI + 0x1c)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (DI + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma dii_1e : kernel_text -∗ instr (mword_of_int (DI + 0x1e) : mword 64) false (BTYPE (mword_of_int 80 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)).
  Proof. mk_base (DI + 0x1e)%Z (mword_of_int 0x04f70863 : mword 32)
    (mword_of_int (DI + 0x1e) : mword 64) (BTYPE (mword_of_int 80 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)) bdec_04f70863. Qed.

  (* --- the common epilogue (+0x22 .. +0x28): every path ends here --- *)
  Lemma dii_22 : kernel_text -∗ instr (mword_of_int (DI + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (DI + 0x22)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (DI + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma dii_24 : kernel_text -∗ instr (mword_of_int (DI + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (DI + 0x24)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (DI + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma dii_26 : kernel_text -∗ instr (mword_of_int (DI + 0x26) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (DI + 0x26)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (DI + 0x26) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma dii_28 : kernel_text -∗ instr (mword_of_int (DI + 0x28) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (DI + 0x28)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (DI + 0x28) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- the PLIC arm: save s1, claim, dispatch (+0x2a .. +0x42) --- *)
  Lemma dii_2a : kernel_text -∗ instr (mword_of_int (DI + 0x2a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (DI + 0x2a)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (DI + 0x2a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma dii_2c : kernel_text -∗ instr (mword_of_int (DI + 0x2c) : mword 64) false (JAL (mword_of_int 12180 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (DI + 0x2c)%Z (mword_of_int 0x795020ef : mword 32)
    (mword_of_int (DI + 0x2c) : mword 64) (JAL (mword_of_int 12180 : mword 21, Regidx (mword_of_int 1))) didb_795020ef. Qed.

  Lemma dii_30 : kernel_text -∗ instr (mword_of_int (DI + 0x30) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (DI + 0x30)%Z (mword_of_int 0x872a : mword 16)
    (mword_of_int (DI + 0x30) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 14), ADD)) cdec_872a exec_execute_C_MV. Qed.

  Lemma dii_32 : kernel_text -∗ instr (mword_of_int (DI + 0x32) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (DI + 0x32)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (DI + 0x32) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma dii_34 : kernel_text -∗ instr (mword_of_int (DI + 0x34) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (DI + 0x34)%Z (mword_of_int 0x47a9 : mword 16)
    (mword_of_int (DI + 0x34) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) didc_47a9 exec_execute_C_LI. Qed.

  Lemma dii_36 : kernel_text -∗ instr (mword_of_int (DI + 0x36) : mword 64) false (BTYPE (mword_of_int 18 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 10), BEQ)).
  Proof. mk_base (DI + 0x36)%Z (mword_of_int 0x00f50963 : mword 32)
    (mword_of_int (DI + 0x36) : mword 64) (BTYPE (mword_of_int 18 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 10), BEQ)) didb_00f50963. Qed.

  Lemma dii_3a : kernel_text -∗ instr (mword_of_int (DI + 0x3a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (DI + 0x3a)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (DI + 0x3a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma dii_3c : kernel_text -∗ instr (mword_of_int (DI + 0x3c) : mword 64) false (BTYPE (mword_of_int 18 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 10), BEQ)).
  Proof. mk_base (DI + 0x3c)%Z (mword_of_int 0x00f50963 : mword 32)
    (mword_of_int (DI + 0x3c) : mword 64) (BTYPE (mword_of_int 18 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 10), BEQ)) didb_00f50963. Qed.

  Lemma dii_40 : kernel_text -∗ instr (mword_of_int (DI + 0x40) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (DI + 0x40)%Z (mword_of_int 0x4505 : mword 16)
    (mword_of_int (DI + 0x40) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4505 exec_execute_C_LI. Qed.

  Lemma dii_42 : kernel_text -∗ instr (mword_of_int (DI + 0x42) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 9 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BNE)).
  Proof. mk_rvc (DI + 0x42)%Z (mword_of_int 0xeb09 : mword 16)
    (mword_of_int (DI + 0x42) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 9 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BNE)) didc_eb09 exec_execute_C_BNEZ. Qed.

  (* --- irq == 0: restore s1 and leave, with a0 = 1 (+0x44, +0x46) --- *)
  Lemma dii_44 : kernel_text -∗ instr (mword_of_int (DI + 0x44) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (DI + 0x44)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (DI + 0x44) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma dii_46 : kernel_text -∗ instr (mword_of_int (DI + 0x46) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2030 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (DI + 0x46)%Z (mword_of_int 0xbff1 : mword 16)
    (mword_of_int (DI + 0x46) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2030 : mword 11) ('b"0")), zreg)) cdec_bff1 exec_execute_C_J. Qed.

  (* --- the two device handlers (+0x48 .. +0x52) --- *)
  Lemma dii_48 : kernel_text -∗ instr (mword_of_int (DI + 0x48) : mword 64) false (JAL (mword_of_int 2090106 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (DI + 0x48)%Z (mword_of_int 0xc7afe0ef : mword 32)
    (mword_of_int (DI + 0x48) : mword 64) (JAL (mword_of_int 2090106 : mword 21, Regidx (mword_of_int 1))) didb_c7afe0ef. Qed.

  Lemma dii_4c : kernel_text -∗ instr (mword_of_int (DI + 0x4c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 11 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (DI + 0x4c)%Z (mword_of_int 0xa819 : mword 16)
    (mword_of_int (DI + 0x4c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 11 : mword 11) ('b"0")), zreg)) didc_a819 exec_execute_C_J. Qed.

  Lemma dii_4e : kernel_text -∗ instr (mword_of_int (DI + 0x4e) : mword 64) false (JAL (mword_of_int 13320 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (DI + 0x4e)%Z (mword_of_int 0x408030ef : mword 32)
    (mword_of_int (DI + 0x4e) : mword 64) (JAL (mword_of_int 13320 : mword 21, Regidx (mword_of_int 1))) didb_408030ef. Qed.

  Lemma dii_52 : kernel_text -∗ instr (mword_of_int (DI + 0x52) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (DI + 0x52)%Z (mword_of_int 0xa801 : mword 16)
    (mword_of_int (DI + 0x52) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")), zreg)) cdec_a801 exec_execute_C_J. Qed.

  (* +0x54 .. +0x61: the DEAD printk arm -- see the header. *)

  (* --- plic_complete(irq), then leave with a0 = 1 (+0x62 .. +0x6c) --- *)
  Lemma dii_62 : kernel_text -∗ instr (mword_of_int (DI + 0x62) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (DI + 0x62)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (DI + 0x62) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma dii_64 : kernel_text -∗ instr (mword_of_int (DI + 0x64) : mword 64) false (JAL (mword_of_int 12156 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (DI + 0x64)%Z (mword_of_int 0x77d020ef : mword 32)
    (mword_of_int (DI + 0x64) : mword 64) (JAL (mword_of_int 12156 : mword 21, Regidx (mword_of_int 1))) didb_77d020ef. Qed.

  Lemma dii_68 : kernel_text -∗ instr (mword_of_int (DI + 0x68) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (DI + 0x68)%Z (mword_of_int 0x4505 : mword 16)
    (mword_of_int (DI + 0x68) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4505 exec_execute_C_LI. Qed.

  Lemma dii_6a : kernel_text -∗ instr (mword_of_int (DI + 0x6a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (DI + 0x6a)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (DI + 0x6a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma dii_6c : kernel_text -∗ instr (mword_of_int (DI + 0x6c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2011 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (DI + 0x6c)%Z (mword_of_int 0xbf5d : mword 16)
    (mword_of_int (DI + 0x6c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2011 : mword 11) ('b"0")), zreg)) cdec_bf5d exec_execute_C_J. Qed.

  (* --- the timer arm (+0x6e .. +0x74) --- *)
  Lemma dii_6e : kernel_text -∗ instr (mword_of_int (DI + 0x6e) : mword 64) false (JAL (mword_of_int 2096956 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (DI + 0x6e)%Z (mword_of_int 0xf3dff0ef : mword 32)
    (mword_of_int (DI + 0x6e) : mword 64) (JAL (mword_of_int 2096956 : mword 21, Regidx (mword_of_int 1))) bdec_f3dff0ef. Qed.

  Lemma dii_72 : kernel_text -∗ instr (mword_of_int (DI + 0x72) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (DI + 0x72)%Z (mword_of_int 0x4509 : mword 16)
    (mword_of_int (DI + 0x72) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) didc_4509 exec_execute_C_LI. Qed.

  Lemma dii_74 : kernel_text -∗ instr (mword_of_int (DI + 0x74) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (DI + 0x74)%Z (mword_of_int 0xb77d : mword 16)
    (mword_of_int (DI + 0x74) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")), zreg)) cdec_b77d exec_execute_C_J. Qed.

End CodeDevintr.
