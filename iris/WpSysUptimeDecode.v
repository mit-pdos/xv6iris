(* WpSysUptimeDecode.v -- decode templates + [instr] facts for sys_uptime()'s
   21 instructions at KernelSyms.sys_uptime = 0x80002a74.

   sys_uptime's 32-byte frame prologue/epilogue (c.addi sp,-32 / three c.sdsp /
   c.addi4spn / three c.ldsp / c.addi16sp / c.ret) is byte-identical to
   acquire's and myproc's, so those decodes reuse the shared bit-keyed
   [cdec_<word>] templates from KernelRvcDecode.v, as does the [c.mv s1,a5] at
   +0x1e ([cdec_84be]); the [auipc a0,0x15] that opens each
   &tickslock materialization is [bdec_00015517] in KernelBaseDecode.v, since
   binit contains the same word.  sys_uptime's own words -- the addi halves of
   the two &tickslock pairs, the auipc/addi pair for &ticks, the two jal's, the
   [lw a5,ticks], and the slli/c.srli pair that implements the (uint)->uint64
   return cast -- get fresh [sudec_*] templates here. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode KernelBaseDecode.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

Notation SU := KernelSyms.sys_uptime.

(* ===================================================================== *)
(* Fresh decode templates (bit patterns unique to sys_uptime).            *)
(* ===================================================================== *)

(* +0x0e  0x6fa50513  addi a0,a0,1786  -- a0 := &tickslock *)
Lemma sudec_addi_a0_lk1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6fa50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x6fa : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x12  0x982fe0ef  jal ra,acquire (target 0x80000c08; 2^21 - 7806) *)
Lemma sudec_jal_acq s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x982fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089346 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x16  0x00007797  auipc a5,0x7  (the &ticks high half) *)
Lemma sudec_auipc_a5 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00007797 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x7 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* +0x1a  0x7be7a783  lw a5,1982(a5)  -- a5 := ticks *)
Lemma sudec_lw_ticks s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7be7a783 : mword 32)) s
  = Some (LOAD (mword_of_int 0x7be : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* +0x24  0x6e450513  addi a0,a0,1764  -- a0 := &tickslock (second time) *)
Lemma sudec_addi_a0_lk2 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6e450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x6e4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x28  0x9f4fe0ef  jal ra,release (target 0x80000c90; 2^21 - 7692) *)
Lemma sudec_jal_rel s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9f4fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089460 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x2c  0x02049513  slli a0,s1,0x20  (first half of the (uint) cast) *)
Lemma sudec_slli_a0_s1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02049513 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 10), SLLI), s).
Proof. decode_bridge_ms. Qed.

(* +0x30  0x9101  c.srli a0,a0,0x20  (second half of the (uint) cast) *)
Lemma sudec_srli_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9101 : mword 16)) s
  = Some (C_SRLI (mword_of_int 32, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Section WpSysUptimeDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ---- prologue: 32-byte frame, saves ra/s0/s1 (shared cdec_* decodes) ---- *)
  Lemma sui_00 : kernel_text -∗ instr (mword_of_int (SU + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (SU + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (SU + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma sui_02 : kernel_text -∗ instr (mword_of_int (SU + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (SU + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (SU + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma sui_04 : kernel_text -∗ instr (mword_of_int (SU + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (SU + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (SU + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma sui_06 : kernel_text -∗ instr (mword_of_int (SU + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (SU + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (SU + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma sui_08 : kernel_text -∗ instr (mword_of_int (SU + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (SU + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (SU + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* ---- +0x0a/+0x0e: a0 := &tickslock ---- *)
  Lemma sui_0a : kernel_text -∗ instr (mword_of_int (SU + 0x0a) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (SU + 0x0a)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (SU + 0x0a) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma sui_0e : kernel_text -∗ instr (mword_of_int (SU + 0x0e) : mword 64) false (ITYPE (mword_of_int 0x6fa : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (SU + 0x0e)%Z (mword_of_int 0x6fa50513 : mword 32)
    (mword_of_int (SU + 0x0e) : mword 64) (ITYPE (mword_of_int 0x6fa : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) sudec_addi_a0_lk1. Qed.

  (* ---- +0x12: jal ra,acquire ---- *)
  Lemma sui_12 : kernel_text -∗ instr (mword_of_int (SU + 0x12) : mword 64) false (JAL (mword_of_int 2089346 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SU + 0x12)%Z (mword_of_int 0x982fe0ef : mword 32)
    (mword_of_int (SU + 0x12) : mword 64) (JAL (mword_of_int 2089346 : mword 21, Regidx (mword_of_int 1))) sudec_jal_acq. Qed.

  (* ---- +0x16/+0x1a: a5 := ticks ---- *)
  Lemma sui_16 : kernel_text -∗ instr (mword_of_int (SU + 0x16) : mword 64) false (UTYPE (mword_of_int 0x7 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (SU + 0x16)%Z (mword_of_int 0x00007797 : mword 32)
    (mword_of_int (SU + 0x16) : mword 64) (UTYPE (mword_of_int 0x7 : mword 20, Regidx (mword_of_int 15), AUIPC)) sudec_auipc_a5. Qed.

  Lemma sui_1a : kernel_text -∗ instr (mword_of_int (SU + 0x1a) : mword 64) false (LOAD (mword_of_int 0x7be : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (SU + 0x1a)%Z (mword_of_int 0x7be7a783 : mword 32)
    (mword_of_int (SU + 0x1a) : mword 64) (LOAD (mword_of_int 0x7be : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) sudec_lw_ticks. Qed.

  (* ---- +0x1e: c.mv s1,a5 (shared cdec_84be) ---- *)
  Lemma sui_1e : kernel_text -∗ instr (mword_of_int (SU + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (SU + 0x1e)%Z (mword_of_int 0x84be : mword 16)
    (mword_of_int (SU + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)) cdec_84be exec_execute_C_MV. Qed.

  (* ---- +0x20/+0x24: a0 := &tickslock again ---- *)
  Lemma sui_20 : kernel_text -∗ instr (mword_of_int (SU + 0x20) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (SU + 0x20)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (SU + 0x20) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma sui_24 : kernel_text -∗ instr (mword_of_int (SU + 0x24) : mword 64) false (ITYPE (mword_of_int 0x6e4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (SU + 0x24)%Z (mword_of_int 0x6e450513 : mword 32)
    (mword_of_int (SU + 0x24) : mword 64) (ITYPE (mword_of_int 0x6e4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) sudec_addi_a0_lk2. Qed.

  (* ---- +0x28: jal ra,release ---- *)
  Lemma sui_28 : kernel_text -∗ instr (mword_of_int (SU + 0x28) : mword 64) false (JAL (mword_of_int 2089460 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SU + 0x28)%Z (mword_of_int 0x9f4fe0ef : mword 32)
    (mword_of_int (SU + 0x28) : mword 64) (JAL (mword_of_int 2089460 : mword 21, Regidx (mword_of_int 1))) sudec_jal_rel. Qed.

  (* ---- +0x2c/+0x30: a0 := (uint)s1 (slli 32 / srli 32) ---- *)
  Lemma sui_2c : kernel_text -∗ instr (mword_of_int (SU + 0x2c) : mword 64) false (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 10), SLLI)).
  Proof. mk_base (SU + 0x2c)%Z (mword_of_int 0x02049513 : mword 32)
    (mword_of_int (SU + 0x2c) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 10), SLLI)) sudec_slli_a0_s1. Qed.

  Lemma sui_30 : kernel_text -∗ instr (mword_of_int (SU + 0x30) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), SRLI)).
  Proof. mk_rvc (SU + 0x30)%Z (mword_of_int 0x9101 : mword 16)
    (mword_of_int (SU + 0x30) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), SRLI)) sudec_srli_a0 exec_execute_C_SRLI. Qed.

  (* ---- epilogue: c.ldsp ra/s0/s1 / c.addi16sp sp,32 / c.ret ---- *)
  Lemma sui_32 : kernel_text -∗ instr (mword_of_int (SU + 0x32) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (SU + 0x32)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (SU + 0x32) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma sui_34 : kernel_text -∗ instr (mword_of_int (SU + 0x34) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (SU + 0x34)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (SU + 0x34) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma sui_36 : kernel_text -∗ instr (mword_of_int (SU + 0x36) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (SU + 0x36)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (SU + 0x36) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma sui_38 : kernel_text -∗ instr (mword_of_int (SU + 0x38) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SU + 0x38)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (SU + 0x38) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma sui_3a : kernel_text -∗ instr (mword_of_int (SU + 0x3a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (SU + 0x3a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (SU + 0x3a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End WpSysUptimeDecode.
