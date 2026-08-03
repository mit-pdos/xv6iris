(* CodeClockintr.v -- decode templates + [instr] facts for clockintr()'s
   29 instructions at KernelSyms.clockintr = 0x800024b6.

   clockintr's 16-byte frame prologue/epilogue (c.addi sp,-16 / c.sdsp ra,8 /
   c.sdsp s0,0 / c.addi4spn s0,sp,16 / c.ldsp ra,8 / c.ldsp s0,0 /
   c.addi sp,16 / c.ret) is byte-identical to mycpu's and memset's, so those
   decodes reuse the shared bit-keyed [cdec_<word>] templates from
   KernelRvcDecode.v, as does the [c.add a5,a5,a4] at +0x1a ([cdec_97ba], the
   same word the PLIC context arithmetic steps).  clockintr's own words -- the
   three jal's, the c.beqz over the tick block and the c.j back out of it, the
   two &tickslock and the &ticks auipc/addi pairs, the 1000000 lui/addi pair,
   the rdtime, the csrw stimecmp, and the c.lw/c.addiw/c.sw/c.mv of the
   [ticks++; wakeup(&ticks)] body -- get fresh [cidec_*] templates here. *)
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
Require Import KernelRvcDecode.
Require Import WpRvcBridge.
Require Import WpGprCsrrB WpGprCsrwB.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
From iris.base_logic.lib Require Import invariants.
Require Import KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

Notation CI := KernelSyms.clockintr.

(* ===================================================================== *)
(* Fresh decode templates (bit patterns unique to clockintr).             *)
(* ===================================================================== *)



(* +0x0e  0xc01027f3  rdtime a5  (= csrr a5,time) *)
Lemma cidec_rdtime s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc01027f3 : mword 32)) s
  = Some (CSRReg (csr_time, zreg, Regidx (mword_of_int 15), CSRRS), s).
Proof. decode_bridge_ms. Qed.

(* +0x12  0x000f4737  lui a4,0xf4      (1000000 = 0xf4240, high half) *)
Lemma cidec_lui_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000f4737 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xf4 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.

(* +0x16  0x24070713  addi a4,a4,576   (1000000, low half) *)
Lemma cidec_addi_a4_int s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x24070713 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x240 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x1c  0x14d79073  csrw stimecmp,a5 *)
Lemma cidec_csrw_stimecmp s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x14d79073 : mword 32)) s
  = Some (CSRReg (csr_stimecmp, Regidx (mword_of_int 15), zreg, CSRRW), s).
Proof. decode_bridge_ms. Qed.


(* +0x2c  0xc9a50513  addi a0,a0,-870  -- a0 := &tickslock *)
Lemma cidec_addi_a0_lk1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc9a50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xc9a : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x30  0xf22fe0ef  jal ra,acquire (target 0x80000c08; 2^21 - 6366) *)
Lemma cidec_jal_acq s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf22fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2090786 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x34  0x00008717  auipc a4,0x8  (the &ticks high half) *)
Lemma cidec_auipc_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00008717 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x8 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* +0x38  0xd5e70713  addi a4,a4,-674  -- a4 := &ticks *)
Lemma cidec_addi_a4_ticks s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd5e70713 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xd5e : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.


Lemma cidec_exec_clw s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 14), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* 0x2785 (c.addiw a5,1) is shared with push_off and filedup -- now
   cdec_2785 in KernelRvcDecode. *)

(* +0x40  0xc31c  c.sw a5,0(a4) *)
Lemma cidec_csw_ticks s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc31c : mword 16)) s
  = Some (C_SW (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cidec_exec_csw s :
  exec (execute (C_SW (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* +0x42  0x853a  c.mv a0,a4  -- the wakeup(&ticks) argument *)
Lemma cidec_cmv_a0_a4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x853a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x44  0xa59ff0ef  jal ra,wakeup (target 0x80001f52; 2^21 - 1448) *)
Lemma cidec_jal_wakeup s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa59ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095704 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x4c  0xc7a50513  addi a0,a0,-902  -- a0 := &tickslock (second time) *)
Lemma cidec_addi_a0_lk2 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc7a50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xc7a : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x50  0xf8afe0ef  jal ra,release (target 0x80000c90; 2^21 - 6262) *)
Lemma cidec_jal_rel s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf8afe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2090890 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.


Section CodeClockintr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- prologue: 16-byte frame, saves ra/s0 (shared cdec_* decodes) ---- *)
  Lemma cii_00 : kernel_text -∗ instr (mword_of_int (CI + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (CI + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (CI + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma cii_02 : kernel_text -∗ instr (mword_of_int (CI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (CI + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (CI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma cii_04 : kernel_text -∗ instr (mword_of_int (CI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (CI + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (CI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma cii_06 : kernel_text -∗ instr (mword_of_int (CI + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (CI + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (CI + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  (* ---- +0x08: jal ra,cpuid ; +0x0c: c.beqz a0 over the tick block ---- *)
  Lemma cii_08 : kernel_text -∗ instr (mword_of_int (CI + 0x08) : mword 64) false (JAL (mword_of_int 2094098 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (CI + 0x08)%Z (mword_of_int 0xc12ff0ef : mword 32)
    (mword_of_int (CI + 0x08) : mword 64) (JAL (mword_of_int 2094098 : mword 21, Regidx (mword_of_int 1))) bdec_c12ff0ef. Qed.

  Lemma cii_0c : kernel_text -∗ instr (mword_of_int (CI + 0x0c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (CI + 0x0c)%Z (mword_of_int 0xcd11 : mword 16)
    (mword_of_int (CI + 0x0c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) cdec_cd11 exec_execute_C_BEQZ. Qed.

  (* ---- the timer tail: a5 := time + 1000000; csrw stimecmp,a5 ---- *)
  Lemma cii_0e : kernel_text -∗ instr (mword_of_int (CI + 0x0e) : mword 64) false (CSRReg (csr_time, zreg, Regidx (mword_of_int 15), CSRRS)).
  Proof. mk_base (CI + 0x0e)%Z (mword_of_int 0xc01027f3 : mword 32)
    (mword_of_int (CI + 0x0e) : mword 64) (CSRReg (csr_time, zreg, Regidx (mword_of_int 15), CSRRS)) cidec_rdtime. Qed.

  Lemma cii_12 : kernel_text -∗ instr (mword_of_int (CI + 0x12) : mword 64) false (UTYPE (mword_of_int 0xf4 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (CI + 0x12)%Z (mword_of_int 0x000f4737 : mword 32)
    (mword_of_int (CI + 0x12) : mword 64) (UTYPE (mword_of_int 0xf4 : mword 20, Regidx (mword_of_int 14), LUI)) cidec_lui_a4. Qed.

  Lemma cii_16 : kernel_text -∗ instr (mword_of_int (CI + 0x16) : mword 64) false (ITYPE (mword_of_int 0x240 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (CI + 0x16)%Z (mword_of_int 0x24070713 : mword 32)
    (mword_of_int (CI + 0x16) : mword 64) (ITYPE (mword_of_int 0x240 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) cidec_addi_a4_int. Qed.

  Lemma cii_1a : kernel_text -∗ instr (mword_of_int (CI + 0x1a) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (CI + 0x1a)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (CI + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97ba exec_execute_C_ADD. Qed.

  Lemma cii_1c : kernel_text -∗ instr (mword_of_int (CI + 0x1c) : mword 64) false (CSRReg (csr_stimecmp, Regidx (mword_of_int 15), zreg, CSRRW)).
  Proof. mk_base (CI + 0x1c)%Z (mword_of_int 0x14d79073 : mword 32)
    (mword_of_int (CI + 0x1c) : mword 64) (CSRReg (csr_stimecmp, Regidx (mword_of_int 15), zreg, CSRRW)) cidec_csrw_stimecmp. Qed.

  (* ---- epilogue: c.ldsp ra/s0 / c.addi sp,16 / c.ret ---- *)
  Lemma cii_20 : kernel_text -∗ instr (mword_of_int (CI + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (CI + 0x20)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (CI + 0x20) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma cii_22 : kernel_text -∗ instr (mword_of_int (CI + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (CI + 0x22)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (CI + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma cii_24 : kernel_text -∗ instr (mword_of_int (CI + 0x24) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (CI + 0x24)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (CI + 0x24) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma cii_26 : kernel_text -∗ instr (mword_of_int (CI + 0x26) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (CI + 0x26)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (CI + 0x26) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* ---- the tick block (hart 0 only): a0 := &tickslock ---- *)
  Lemma cii_28 : kernel_text -∗ instr (mword_of_int (CI + 0x28) : mword 64) false (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (CI + 0x28)%Z (mword_of_int 0x00016517 : mword 32)
    (mword_of_int (CI + 0x28) : mword 64) (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00016517. Qed.

  Lemma cii_2c : kernel_text -∗ instr (mword_of_int (CI + 0x2c) : mword 64) false (ITYPE (mword_of_int 0xc9a : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (CI + 0x2c)%Z (mword_of_int 0xc9a50513 : mword 32)
    (mword_of_int (CI + 0x2c) : mword 64) (ITYPE (mword_of_int 0xc9a : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) cidec_addi_a0_lk1. Qed.

  Lemma cii_30 : kernel_text -∗ instr (mword_of_int (CI + 0x30) : mword 64) false (JAL (mword_of_int 2090786 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (CI + 0x30)%Z (mword_of_int 0xf22fe0ef : mword 32)
    (mword_of_int (CI + 0x30) : mword 64) (JAL (mword_of_int 2090786 : mword 21, Regidx (mword_of_int 1))) cidec_jal_acq. Qed.

  (* ---- a4 := &ticks ; ticks++ ; wakeup(&ticks) ---- *)
  Lemma cii_34 : kernel_text -∗ instr (mword_of_int (CI + 0x34) : mword 64) false (UTYPE (mword_of_int 0x8 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (CI + 0x34)%Z (mword_of_int 0x00008717 : mword 32)
    (mword_of_int (CI + 0x34) : mword 64) (UTYPE (mword_of_int 0x8 : mword 20, Regidx (mword_of_int 14), AUIPC)) cidec_auipc_a4. Qed.

  Lemma cii_38 : kernel_text -∗ instr (mword_of_int (CI + 0x38) : mword 64) false (ITYPE (mword_of_int 0xd5e : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (CI + 0x38)%Z (mword_of_int 0xd5e70713 : mword 32)
    (mword_of_int (CI + 0x38) : mword 64) (ITYPE (mword_of_int 0xd5e : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) cidec_addi_a4_ticks. Qed.

  Lemma cii_3c : kernel_text -∗ instr (mword_of_int (CI + 0x3c) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 14), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (CI + 0x3c)%Z (mword_of_int 0x431c : mword 16)
    (mword_of_int (CI + 0x3c) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 14), Regidx (mword_of_int 15), false, 4)) cdec_431c cidec_exec_clw. Qed.

  Lemma cii_3e : kernel_text -∗ instr (mword_of_int (CI + 0x3e) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (CI + 0x3e)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (CI + 0x3e) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  Lemma cii_40 : kernel_text -∗ instr (mword_of_int (CI + 0x40) : mword 64) true (STORE (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (CI + 0x40)%Z (mword_of_int 0xc31c : mword 16)
    (mword_of_int (CI + 0x40) : mword 64) (STORE (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) cidec_csw_ticks cidec_exec_csw. Qed.

  Lemma cii_42 : kernel_text -∗ instr (mword_of_int (CI + 0x42) : mword 64) true (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (CI + 0x42)%Z (mword_of_int 0x853a : mword 16)
    (mword_of_int (CI + 0x42) : mword 64) (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 10), ADD)) cidec_cmv_a0_a4 exec_execute_C_MV. Qed.

  Lemma cii_44 : kernel_text -∗ instr (mword_of_int (CI + 0x44) : mword 64) false (JAL (mword_of_int 2095704 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (CI + 0x44)%Z (mword_of_int 0xa59ff0ef : mword 32)
    (mword_of_int (CI + 0x44) : mword 64) (JAL (mword_of_int 2095704 : mword 21, Regidx (mword_of_int 1))) cidec_jal_wakeup. Qed.

  (* ---- release(&tickslock) and back to the timer tail ---- *)
  Lemma cii_48 : kernel_text -∗ instr (mword_of_int (CI + 0x48) : mword 64) false (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (CI + 0x48)%Z (mword_of_int 0x00016517 : mword 32)
    (mword_of_int (CI + 0x48) : mword 64) (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00016517. Qed.

  Lemma cii_4c : kernel_text -∗ instr (mword_of_int (CI + 0x4c) : mword 64) false (ITYPE (mword_of_int 0xc7a : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (CI + 0x4c)%Z (mword_of_int 0xc7a50513 : mword 32)
    (mword_of_int (CI + 0x4c) : mword 64) (ITYPE (mword_of_int 0xc7a : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) cidec_addi_a0_lk2. Qed.

  Lemma cii_50 : kernel_text -∗ instr (mword_of_int (CI + 0x50) : mword 64) false (JAL (mword_of_int 2090890 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (CI + 0x50)%Z (mword_of_int 0xf8afe0ef : mword 32)
    (mword_of_int (CI + 0x50) : mword 64) (JAL (mword_of_int 2090890 : mword 21, Regidx (mword_of_int 1))) cidec_jal_rel. Qed.

  Lemma cii_54 : kernel_text -∗ instr (mword_of_int (CI + 0x54) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2013 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (CI + 0x54)%Z (mword_of_int 0xbf6d : mword 16)
    (mword_of_int (CI + 0x54) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2013 : mword 11) ('b"0")), zreg)) cdec_bf6d exec_execute_C_J. Qed.

End CodeClockintr.
