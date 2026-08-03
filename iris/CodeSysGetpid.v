(* CodeSysGetpid.v -- the machine code of sys_getpid(): the decode
   templates for the words this function alone uses, and the [instr]
   constructors for its instruction addresses.  Consumed by ProofSysGetpid.v. *)



From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import InstrBytes WpMmodeLeafBase.
Require Import KernelText.
Require Import KernelRvcDecode WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import KernelBaseDecode.
Import Defs.
Local Open Scope Z_scope.
Local Notation SG := KernelSyms.sys_getpid.

Section CodeSysGetpid.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.


(* +0x0c  0x5908  c.lw a0,48(a0)  -- a0 := myproc()->pid *)
Lemma sgdec_lw_a0_procpid s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x5908 : mword 16)) s
  = Some (C_LW (mword_of_int 12, Cregidx (mword_of_int 2), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* ------------------------------------------------------------------- *)
(* [instr] facts for the ten instructions.                              *)
(* ------------------------------------------------------------------- *)
Lemma sg_00 : kernel_text -∗ instr (mword_of_int (SG + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (SG + 0x00)%Z (mword_of_int 0x1141 : mword 16)
  (mword_of_int (SG + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.
Lemma sg_02 : kernel_text -∗ instr (mword_of_int (SG + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
Proof. mk_rvc (SG + 0x02)%Z (mword_of_int 0xe406 : mword 16)
  (mword_of_int (SG + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.
Lemma sg_04 : kernel_text -∗ instr (mword_of_int (SG + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
Proof. mk_rvc (SG + 0x04)%Z (mword_of_int 0xe022 : mword 16)
  (mword_of_int (SG + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.
Lemma sg_06 : kernel_text -∗ instr (mword_of_int (SG + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
Proof. mk_rvc (SG + 0x06)%Z (mword_of_int 0x0800 : mword 16)
  (mword_of_int (SG + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.
Lemma sg_08 : kernel_text -∗ instr (mword_of_int (SG + 0x08) : mword 64) false (JAL (mword_of_int 2093072 : mword 21, Regidx (mword_of_int 1))).
Proof. mk_base (SG + 0x08)%Z (mword_of_int 0x810ff0ef : mword 32)
  (mword_of_int (SG + 0x08) : mword 64) (JAL (mword_of_int 2093072 : mword 21, Regidx (mword_of_int 1))) bdec_810ff0ef. Qed.
Lemma sg_0c : kernel_text -∗ instr (mword_of_int (SG + 0x0c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 4)).
Proof. mk_rvc (SG + 0x0c)%Z (mword_of_int 0x5908 : mword 16)
  (mword_of_int (SG + 0x0c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 4)) sgdec_lw_a0_procpid exec_execute_C_LW. Qed.
Lemma sg_0e : kernel_text -∗ instr (mword_of_int (SG + 0x0e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
Proof. mk_rvc (SG + 0x0e)%Z (mword_of_int 0x60a2 : mword 16)
  (mword_of_int (SG + 0x0e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.
Lemma sg_10 : kernel_text -∗ instr (mword_of_int (SG + 0x10) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
Proof. mk_rvc (SG + 0x10)%Z (mword_of_int 0x6402 : mword 16)
  (mword_of_int (SG + 0x10) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.
Lemma sg_12 : kernel_text -∗ instr (mword_of_int (SG + 0x12) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (SG + 0x12)%Z (mword_of_int 0x0141 : mword 16)
  (mword_of_int (SG + 0x12) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.
Lemma sg_14 : kernel_text -∗ instr (mword_of_int (SG + 0x14) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
Proof. mk_rvc (SG + 0x14)%Z (mword_of_int 0x8082 : mword 16)
  (mword_of_int (SG + 0x14) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeSysGetpid.
