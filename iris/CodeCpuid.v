(* CodeCpuid.v -- the machine code of cpuid(): the decode
   templates for the words this function alone uses, and the [instr]
   constructors for its instruction addresses.  Consumed by ProofCpuid.v. *)



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
Import Defs.

Section CodeCpuid.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


(* ---- the two a0-flavoured RVC decodes not shared with the frame set ---- *)
(* +0x08  8512  c.mv a0,tp *)
Lemma cdec_mv_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8512 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* +0x0a  2501  c.addiw a0,0 (sext.w a0) *)
Lemma cdec_addiw_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2501 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 0, Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* ------------------------------------------------------------------- *)
(* [instr] facts for the ten cpuid instructions from [kernel_text].     *)
(* Frame decodes reuse KernelRvcDecode's shared templates; the two      *)
(* a0-reads use the local [cdec_*] lemmas above.                        *)
(* ------------------------------------------------------------------- *)
Lemma ci_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (KernelSyms.cpuid + 0x00)%Z (mword_of_int 0x1141 : mword 16)
  (mword_of_int (KernelSyms.cpuid + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.
Lemma ci_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
Proof. mk_rvc (KernelSyms.cpuid + 0x02)%Z (mword_of_int 0xe406 : mword 16)
  (mword_of_int (KernelSyms.cpuid + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.
Lemma ci_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
Proof. mk_rvc (KernelSyms.cpuid + 0x04)%Z (mword_of_int 0xe022 : mword 16)
  (mword_of_int (KernelSyms.cpuid + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.
Lemma ci_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
Proof. mk_rvc (KernelSyms.cpuid + 0x06)%Z (mword_of_int 0x0800 : mword 16)
  (mword_of_int (KernelSyms.cpuid + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.
Lemma ci_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x08) : mword 64) true (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 10), ADD)).
Proof. mk_rvc (KernelSyms.cpuid + 0x08)%Z (mword_of_int 0x8512 : mword 16)
  (mword_of_int (KernelSyms.cpuid + 0x08) : mword 64) (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 10), ADD)) cdec_mv_a0 exec_execute_C_MV. Qed.
Lemma ci_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x0a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10))).
Proof. mk_rvc (KernelSyms.cpuid + 0x0a)%Z (mword_of_int 0x2501 : mword 16)
  (mword_of_int (KernelSyms.cpuid + 0x0a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10))) cdec_addiw_a0 exec_execute_C_ADDIW. Qed.
Lemma ci_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x0c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
Proof. mk_rvc (KernelSyms.cpuid + 0x0c)%Z (mword_of_int 0x60a2 : mword 16)
  (mword_of_int (KernelSyms.cpuid + 0x0c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.
Lemma ci_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x0e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
Proof. mk_rvc (KernelSyms.cpuid + 0x0e)%Z (mword_of_int 0x6402 : mword 16)
  (mword_of_int (KernelSyms.cpuid + 0x0e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.
Lemma ci_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x10) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (KernelSyms.cpuid + 0x10)%Z (mword_of_int 0x0141 : mword 16)
  (mword_of_int (KernelSyms.cpuid + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.
Lemma ci_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x12) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
Proof. mk_rvc (KernelSyms.cpuid + 0x12)%Z (mword_of_int 0x8082 : mword 16)
  (mword_of_int (KernelSyms.cpuid + 0x12) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeCpuid.
