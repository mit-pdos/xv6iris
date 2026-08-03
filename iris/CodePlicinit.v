(* CodePlicinit.v -- the machine code of plicinit(): the decode
   templates for the words this function alone uses, and the [instr]
   constructors for its instruction addresses.  Consumed by ProofPlicinit.v. *)



From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import HartTp WpNext IntrDefs.
Require Import KptPt.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpSmodeIntr.
Require Import WpDecodeBridge.
Require Import KernelRvcDecode WpRvcBridge.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import PlicPlan WpPlic SpecPlicinit.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Notation PL := KernelSyms.plicinit.

Section CodePlicinit.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

Lemma plexec_sw40 s :
exec (execute (C_SW (mword_of_int 10, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
= Some (ExecuteAs (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.
Lemma plexec_sw4 s :
exec (execute (C_SW (mword_of_int 1, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
= Some (ExecuteAs (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.


(* ---- lui a4,0xc000 (0x0c000737): 4-byte U-type decode ---- *)
Lemma pldec_lui_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0c000737 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xc000 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.
(* ---- creg -> reg and immediate helpers for the two c.sw sites ---- *)
(* +0x0e  d71c  c.sw a5,40(a4) *)
Lemma pldec_sw40 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd71c : mword 16)) s
  = Some (C_SW (mword_of_int 10, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* +0x10  c35c  c.sw a5,4(a4) *)
Lemma pldec_sw4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc35c : mword 16)) s
  = Some (C_SW (mword_of_int 1, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* ------------------------------------------------------------------- *)
(* [instr] facts for the twelve plicinit instructions.                  *)
(* Frame decodes reuse KernelRvcDecode's shared templates (byte-        *)
(* identical to cpuid); the middle four are proven here.                *)
(* ------------------------------------------------------------------- *)
Lemma pi_00 : kernel_text -∗ instr (mword_of_int (PL + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (PL + 0x00)%Z (mword_of_int 0x1141 : mword 16)
  (mword_of_int (PL + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.
Lemma pi_02 : kernel_text -∗ instr (mword_of_int (PL + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
Proof. mk_rvc (PL + 0x02)%Z (mword_of_int 0xe406 : mword 16)
  (mword_of_int (PL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.
Lemma pi_04 : kernel_text -∗ instr (mword_of_int (PL + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
Proof. mk_rvc (PL + 0x04)%Z (mword_of_int 0xe022 : mword 16)
  (mword_of_int (PL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.
Lemma pi_06 : kernel_text -∗ instr (mword_of_int (PL + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
Proof. mk_rvc (PL + 0x06)%Z (mword_of_int 0x0800 : mword 16)
  (mword_of_int (PL + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.
Lemma pi_08 : kernel_text -∗ instr (mword_of_int (PL + 0x08) : mword 64) false (UTYPE (mword_of_int 0xc000 : mword 20, Regidx (mword_of_int 14), LUI)).
Proof. mk_base (PL + 0x08)%Z (mword_of_int 0x0c000737 : mword 32)
  (mword_of_int (PL + 0x08) : mword 64) (UTYPE (mword_of_int 0xc000 : mword 20, Regidx (mword_of_int 14), LUI)) pldec_lui_a4. Qed.
Lemma pi_0c : kernel_text -∗ instr (mword_of_int (PL + 0x0c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
Proof. mk_rvc (PL + 0x0c)%Z (mword_of_int 0x4785 : mword 16)
  (mword_of_int (PL + 0x0c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.
Lemma pi_0e : kernel_text -∗ instr (mword_of_int (PL + 0x0e) : mword 64) true (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
Proof. mk_rvc (PL + 0x0e)%Z (mword_of_int 0xd71c : mword 16)
  (mword_of_int (PL + 0x0e) : mword 64) (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) pldec_sw40 plexec_sw40. Qed.
Lemma pi_10 : kernel_text -∗ instr (mword_of_int (PL + 0x10) : mword 64) true (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
Proof. mk_rvc (PL + 0x10)%Z (mword_of_int 0xc35c : mword 16)
  (mword_of_int (PL + 0x10) : mword 64) (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) pldec_sw4 plexec_sw4. Qed.
Lemma pi_12 : kernel_text -∗ instr (mword_of_int (PL + 0x12) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
Proof. mk_rvc (PL + 0x12)%Z (mword_of_int 0x60a2 : mword 16)
  (mword_of_int (PL + 0x12) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.
Lemma pi_14 : kernel_text -∗ instr (mword_of_int (PL + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
Proof. mk_rvc (PL + 0x14)%Z (mword_of_int 0x6402 : mword 16)
  (mword_of_int (PL + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.
Lemma pi_16 : kernel_text -∗ instr (mword_of_int (PL + 0x16) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (PL + 0x16)%Z (mword_of_int 0x0141 : mword 16)
  (mword_of_int (PL + 0x16) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.
Lemma pi_18 : kernel_text -∗ instr (mword_of_int (PL + 0x18) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
Proof. mk_rvc (PL + 0x18)%Z (mword_of_int 0x8082 : mword 16)
  (mword_of_int (PL + 0x18) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodePlicinit.
