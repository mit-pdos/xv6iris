(* CodePlicinithart.v -- the machine code of plicinithart(): the decode
   templates for the words this function alone uses, and the [instr]
   constructors for its instruction addresses.  Consumed by ProofPlicinithart.v. *)



From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpMmodeLeafBase.
Require Import KernelText.
Require Import WpDecodeBridge.
Require Import KernelRvcDecode KernelBaseDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Notation PH := KernelSyms.plicinithart.

Section CodePlicinithart.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


(* +0x08  c30fc0ef  jal ra,cpuid   (target = pc - 15312) *)
Lemma phdec_jal s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc30fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2081840 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.
(* +0x0c  0085171b  slliw a4,a0,0x8 *)
Lemma phdec_slliw_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0085171b : mword 32)) s
  = Some (SHIFTIWOP (mword_of_int 8 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLLIW), s).
Proof. decode_bridge_ms. Qed.
(* +0x10  0c0027b7  lui a5,0xc002 *)
Lemma phdec_lui_c002 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0c0027b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xc002 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.
(* +0x16  40200713  addi a4,zero,1026 *)
Lemma phdec_li_1026 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40200713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1026 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.
(* +0x28  0007a023  sw zero,0(a5) *)
Lemma phdec_sw_zero s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007a023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.
(* ------------------------------------------------------------------- *)
(* [instr] facts for the eighteen plicinithart instructions.            *)
(* ------------------------------------------------------------------- *)
Lemma phi_00 : kernel_text -∗ instr (mword_of_int (PH + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (PH + 0x00)%Z (mword_of_int 0x1141 : mword 16)
  (mword_of_int (PH + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.
Lemma phi_02 : kernel_text -∗ instr (mword_of_int (PH + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
Proof. mk_rvc (PH + 0x02)%Z (mword_of_int 0xe406 : mword 16)
  (mword_of_int (PH + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.
Lemma phi_04 : kernel_text -∗ instr (mword_of_int (PH + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
Proof. mk_rvc (PH + 0x04)%Z (mword_of_int 0xe022 : mword 16)
  (mword_of_int (PH + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.
Lemma phi_06 : kernel_text -∗ instr (mword_of_int (PH + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
Proof. mk_rvc (PH + 0x06)%Z (mword_of_int 0x0800 : mword 16)
  (mword_of_int (PH + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.
Lemma phi_08 : kernel_text -∗ instr (mword_of_int (PH + 0x08) : mword 64) false (JAL (mword_of_int 2081840 : mword 21, Regidx (mword_of_int 1))).
Proof. mk_base (PH + 0x08)%Z (mword_of_int 0xc30fc0ef : mword 32)
  (mword_of_int (PH + 0x08) : mword 64) (JAL (mword_of_int 2081840 : mword 21, Regidx (mword_of_int 1))) phdec_jal. Qed.
Lemma phi_0c : kernel_text -∗ instr (mword_of_int (PH + 0x0c) : mword 64) false (SHIFTIWOP (mword_of_int 8 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLLIW)).
Proof. mk_base (PH + 0x0c)%Z (mword_of_int 0x0085171b : mword 32)
  (mword_of_int (PH + 0x0c) : mword 64) (SHIFTIWOP (mword_of_int 8 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLLIW)) phdec_slliw_a4. Qed.
Lemma phi_10 : kernel_text -∗ instr (mword_of_int (PH + 0x10) : mword 64) false (UTYPE (mword_of_int 0xc002 : mword 20, Regidx (mword_of_int 15), LUI)).
Proof. mk_base (PH + 0x10)%Z (mword_of_int 0x0c0027b7 : mword 32)
  (mword_of_int (PH + 0x10) : mword 64) (UTYPE (mword_of_int 0xc002 : mword 20, Regidx (mword_of_int 15), LUI)) phdec_lui_c002. Qed.
Lemma phi_14 : kernel_text -∗ instr (mword_of_int (PH + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
Proof. mk_rvc (PH + 0x14)%Z (mword_of_int 0x97ba : mword 16)
  (mword_of_int (PH + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97ba exec_execute_C_ADD. Qed.
Lemma phi_16 : kernel_text -∗ instr (mword_of_int (PH + 0x16) : mword 64) false (ITYPE (mword_of_int 1026 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), ADDI)).
Proof. mk_base (PH + 0x16)%Z (mword_of_int 0x40200713 : mword 32)
  (mword_of_int (PH + 0x16) : mword 64) (ITYPE (mword_of_int 1026 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), ADDI)) phdec_li_1026. Qed.
Lemma phi_1a : kernel_text -∗ instr (mword_of_int (PH + 0x1a) : mword 64) false (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
Proof. mk_base (PH + 0x1a)%Z (mword_of_int 0x08e7a023 : mword 32)
  (mword_of_int (PH + 0x1a) : mword 64) (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) bdec_08e7a023. Qed.
Lemma phi_1e : kernel_text -∗ instr (mword_of_int (PH + 0x1e) : mword 64) false (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLLIW)).
Proof. mk_base (PH + 0x1e)%Z (mword_of_int 0x00d5151b : mword 32)
  (mword_of_int (PH + 0x1e) : mword 64) (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLLIW)) bdec_00d5151b. Qed.
Lemma phi_22 : kernel_text -∗ instr (mword_of_int (PH + 0x22) : mword 64) false (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 15), LUI)).
Proof. mk_base (PH + 0x22)%Z (mword_of_int 0x0c2017b7 : mword 32)
  (mword_of_int (PH + 0x22) : mword 64) (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 15), LUI)) bdec_0c2017b7. Qed.
Lemma phi_26 : kernel_text -∗ instr (mword_of_int (PH + 0x26) : mword 64) true (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
Proof. mk_rvc (PH + 0x26)%Z (mword_of_int 0x97aa : mword 16)
  (mword_of_int (PH + 0x26) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97aa exec_execute_C_ADD. Qed.
Lemma phi_28 : kernel_text -∗ instr (mword_of_int (PH + 0x28) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)).
Proof. mk_base (PH + 0x28)%Z (mword_of_int 0x0007a023 : mword 32)
  (mword_of_int (PH + 0x28) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)) phdec_sw_zero. Qed.
Lemma phi_2c : kernel_text -∗ instr (mword_of_int (PH + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
Proof. mk_rvc (PH + 0x2c)%Z (mword_of_int 0x60a2 : mword 16)
  (mword_of_int (PH + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.
Lemma phi_2e : kernel_text -∗ instr (mword_of_int (PH + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
Proof. mk_rvc (PH + 0x2e)%Z (mword_of_int 0x6402 : mword 16)
  (mword_of_int (PH + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.
Lemma phi_30 : kernel_text -∗ instr (mword_of_int (PH + 0x30) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (PH + 0x30)%Z (mword_of_int 0x0141 : mword 16)
  (mword_of_int (PH + 0x30) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.
Lemma phi_32 : kernel_text -∗ instr (mword_of_int (PH + 0x32) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
Proof. mk_rvc (PH + 0x32)%Z (mword_of_int 0x8082 : mword 16)
  (mword_of_int (PH + 0x32) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodePlicinithart.
