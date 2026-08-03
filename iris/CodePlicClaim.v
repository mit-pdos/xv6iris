(* CodePlicClaim.v -- the machine code of plic_claim(): the decode
   templates for the words this function alone uses, and the [instr]
   constructors for its instruction addresses.  Consumed by ProofPlicClaim.v. *)



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
Require Import KernelRvcDecode KernelBaseDecode WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Notation PQ := KernelSyms.plic_claim.

Section CodePlicClaim.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

Lemma pq_imm4 : zero_extend' 12 (concat_vec (mword_of_int 1 : mword 5) ('b"00")) = (mword_of_int 4 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pqexec_lw_a0 s :
exec (execute (C_LW (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)))) s
= Some (ExecuteAs (LOAD (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 10), false, 4)), s).
Proof.
rewrite exec_execute_C_LW. rewrite creg_c7. rewrite creg_c2. rewrite pq_imm4. reflexivity.
Qed.


(* +0x08  bfcfc0ef  jal ra,cpuid *)
Lemma pqdec_jal s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbfcfc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2081788 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.
(* +0x16  43c8  c.lw a0,4(a5) *)
Lemma pqdec_lw_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x43c8 : mword 16)) s
  = Some (C_LW (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* ---- [instr] facts for the thirteen plic_claim instructions ---- *)
Lemma pqi_00 : kernel_text -∗ instr (mword_of_int (PQ + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (PQ + 0x00)%Z (mword_of_int 0x1141 : mword 16)
  (mword_of_int (PQ + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.
Lemma pqi_02 : kernel_text -∗ instr (mword_of_int (PQ + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
Proof. mk_rvc (PQ + 0x02)%Z (mword_of_int 0xe406 : mword 16)
  (mword_of_int (PQ + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.
Lemma pqi_04 : kernel_text -∗ instr (mword_of_int (PQ + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
Proof. mk_rvc (PQ + 0x04)%Z (mword_of_int 0xe022 : mword 16)
  (mword_of_int (PQ + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.
Lemma pqi_06 : kernel_text -∗ instr (mword_of_int (PQ + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
Proof. mk_rvc (PQ + 0x06)%Z (mword_of_int 0x0800 : mword 16)
  (mword_of_int (PQ + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.
Lemma pqi_08 : kernel_text -∗ instr (mword_of_int (PQ + 0x08) : mword 64) false (JAL (mword_of_int 2081788 : mword 21, Regidx (mword_of_int 1))).
Proof. mk_base (PQ + 0x08)%Z (mword_of_int 0xbfcfc0ef : mword 32)
  (mword_of_int (PQ + 0x08) : mword 64) (JAL (mword_of_int 2081788 : mword 21, Regidx (mword_of_int 1))) pqdec_jal. Qed.
Lemma pqi_0c : kernel_text -∗ instr (mword_of_int (PQ + 0x0c) : mword 64) false (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLLIW)).
Proof. mk_base (PQ + 0x0c)%Z (mword_of_int 0x00d5151b : mword 32)
  (mword_of_int (PQ + 0x0c) : mword 64) (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLLIW)) bdec_00d5151b. Qed.
Lemma pqi_10 : kernel_text -∗ instr (mword_of_int (PQ + 0x10) : mword 64) false (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 15), LUI)).
Proof. mk_base (PQ + 0x10)%Z (mword_of_int 0x0c2017b7 : mword 32)
  (mword_of_int (PQ + 0x10) : mword 64) (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 15), LUI)) bdec_0c2017b7. Qed.
Lemma pqi_14 : kernel_text -∗ instr (mword_of_int (PQ + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
Proof. mk_rvc (PQ + 0x14)%Z (mword_of_int 0x97aa : mword 16)
  (mword_of_int (PQ + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97aa exec_execute_C_ADD. Qed.
Lemma pqi_16 : kernel_text -∗ instr (mword_of_int (PQ + 0x16) : mword 64) true (LOAD (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 10), false, 4)).
Proof. mk_rvc (PQ + 0x16)%Z (mword_of_int 0x43c8 : mword 16)
  (mword_of_int (PQ + 0x16) : mword 64) (LOAD (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 10), false, 4)) pqdec_lw_a0 pqexec_lw_a0. Qed.
Lemma pqi_18 : kernel_text -∗ instr (mword_of_int (PQ + 0x18) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
Proof. mk_rvc (PQ + 0x18)%Z (mword_of_int 0x60a2 : mword 16)
  (mword_of_int (PQ + 0x18) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.
Lemma pqi_1a : kernel_text -∗ instr (mword_of_int (PQ + 0x1a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
Proof. mk_rvc (PQ + 0x1a)%Z (mword_of_int 0x6402 : mword 16)
  (mword_of_int (PQ + 0x1a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.
Lemma pqi_1c : kernel_text -∗ instr (mword_of_int (PQ + 0x1c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (PQ + 0x1c)%Z (mword_of_int 0x0141 : mword 16)
  (mword_of_int (PQ + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.
Lemma pqi_1e : kernel_text -∗ instr (mword_of_int (PQ + 0x1e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
Proof. mk_rvc (PQ + 0x1e)%Z (mword_of_int 0x8082 : mword 16)
  (mword_of_int (PQ + 0x1e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodePlicClaim.
