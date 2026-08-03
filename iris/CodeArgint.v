(* CodeArgint.v -- the machine code of argint(): the decode
   templates for the words this function alone uses, and the [instr]
   constructors for its instruction addresses.  Consumed by ProofArgint.v. *)



From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpMmodeLeafBase.
Require Import KernelText.
Require Import KernelRvcDecode WpRvcBridge WpDecodeBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.
Local Notation AI := KernelSyms.argint.

Section CodeArgint.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.


Lemma aidec_jal_argraw s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf0bff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096906 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.
(* +0x10  0xc088  c.sw a0,0(s1)  -- *ip = (int)a0 *)
Lemma aidec_sw_a0_ip s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc088 : mword 16)) s
  = Some (C_SW (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma ai_00 : kernel_text -∗ instr (mword_of_int (AI + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (AI + 0x00)%Z (mword_of_int 0x1101 : mword 16)
  (mword_of_int (AI + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.
Lemma ai_02 : kernel_text -∗ instr (mword_of_int (AI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
Proof. mk_rvc (AI + 0x02)%Z (mword_of_int 0xec06 : mword 16)
  (mword_of_int (AI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.
Lemma ai_04 : kernel_text -∗ instr (mword_of_int (AI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
Proof. mk_rvc (AI + 0x04)%Z (mword_of_int 0xe822 : mword 16)
  (mword_of_int (AI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.
Lemma ai_06 : kernel_text -∗ instr (mword_of_int (AI + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
Proof. mk_rvc (AI + 0x06)%Z (mword_of_int 0xe426 : mword 16)
  (mword_of_int (AI + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.
Lemma ai_08 : kernel_text -∗ instr (mword_of_int (AI + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
Proof. mk_rvc (AI + 0x08)%Z (mword_of_int 0x1000 : mword 16)
  (mword_of_int (AI + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.
Lemma ai_0a : kernel_text -∗ instr (mword_of_int (AI + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)).
Proof. mk_rvc (AI + 0x0a)%Z (mword_of_int 0x84ae : mword 16)
  (mword_of_int (AI + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)) cdec_84ae exec_execute_C_MV. Qed.
Lemma ai_0c : kernel_text -∗ instr (mword_of_int (AI + 0x0c) : mword 64) false (JAL (mword_of_int 2096906 : mword 21, Regidx (mword_of_int 1))).
Proof. mk_base (AI + 0x0c)%Z (mword_of_int 0xf0bff0ef : mword 32)
  (mword_of_int (AI + 0x0c) : mword 64) (JAL (mword_of_int 2096906 : mword 21, Regidx (mword_of_int 1))) aidec_jal_argraw. Qed.
Lemma ai_10 : kernel_text -∗ instr (mword_of_int (AI + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 1)), 4)).
Proof. mk_rvc (AI + 0x10)%Z (mword_of_int 0xc088 : mword 16)
  (mword_of_int (AI + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 1)), 4)) aidec_sw_a0_ip exec_execute_C_SW. Qed.
Lemma ai_12 : kernel_text -∗ instr (mword_of_int (AI + 0x12) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
Proof. mk_rvc (AI + 0x12)%Z (mword_of_int 0x60e2 : mword 16)
  (mword_of_int (AI + 0x12) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.
Lemma ai_14 : kernel_text -∗ instr (mword_of_int (AI + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
Proof. mk_rvc (AI + 0x14)%Z (mword_of_int 0x6442 : mword 16)
  (mword_of_int (AI + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.
Lemma ai_16 : kernel_text -∗ instr (mword_of_int (AI + 0x16) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
Proof. mk_rvc (AI + 0x16)%Z (mword_of_int 0x64a2 : mword 16)
  (mword_of_int (AI + 0x16) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.
Lemma ai_18 : kernel_text -∗ instr (mword_of_int (AI + 0x18) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
Proof. mk_rvc (AI + 0x18)%Z (mword_of_int 0x6105 : mword 16)
  (mword_of_int (AI + 0x18) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.
Lemma ai_1a : kernel_text -∗ instr (mword_of_int (AI + 0x1a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
Proof. mk_rvc (AI + 0x1a)%Z (mword_of_int 0x8082 : mword 16)
  (mword_of_int (AI + 0x1a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeArgint.
