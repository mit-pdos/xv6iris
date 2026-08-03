(* CodePlicComplete.v -- the machine code of plic_complete(): the decode
   templates for the words this function alone uses, and the [instr]
   constructors for its instruction addresses.  Consumed by ProofPlicComplete.v. *)



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
Require Import StackOwn CalleeSaved KernelText.
Require Import WpDecodeBridge.
Require Import KernelRvcDecode WpRvcBridge.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import PlicPlan PlicHart DiskPtsto WpUart WpPlic SpecCpuid SpecPlicComplete.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvExtras.
Import Defs.
Local Notation PC := KernelSyms.plic_complete.

Section CodePlicComplete.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

Lemma pc_imm4 : zero_extend' 12 (concat_vec (mword_of_int 1 : mword 5) ('b"00")) = (mword_of_int 4 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcexec_sw_s1 s :
exec (execute (C_SW (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 1)))) s
= Some (ExecuteAs (STORE (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 15), 4)), s).
Proof.
rewrite exec_execute_C_SW. rewrite creg_c7. rewrite creg_c1. rewrite pc_imm4. reflexivity.
Qed.


(* +0x0c  bd8fc0ef  jal ra,cpuid *)
Lemma pcdec_jal s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbd8fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2081752 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.
(* +0x10  00d5179b  slliw a5,a0,0xd *)
Lemma pcdec_slliw_a5 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d5179b : mword 32)) s
  = Some (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLIW), s).
Proof. decode_bridge_ms. Qed.
(* +0x14  0c201737  lui a4,0xc201 *)
Lemma pcdec_lui_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0c201737 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.
(* +0x1a  c3c4  c.sw s1,4(a5) *)
Lemma pcdec_sw_s1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc3c4 : mword 16)) s
  = Some (C_SW (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* ---- [instr] facts for the fifteen plic_complete instructions ---- *)
Lemma pci_00 : kernel_text -∗ instr (mword_of_int (PC + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (PC + 0x00)%Z (mword_of_int 0x1101 : mword 16)
  (mword_of_int (PC + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.
Lemma pci_02 : kernel_text -∗ instr (mword_of_int (PC + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
Proof. mk_rvc (PC + 0x02)%Z (mword_of_int 0xec06 : mword 16)
  (mword_of_int (PC + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.
Lemma pci_04 : kernel_text -∗ instr (mword_of_int (PC + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
Proof. mk_rvc (PC + 0x04)%Z (mword_of_int 0xe822 : mword 16)
  (mword_of_int (PC + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.
Lemma pci_06 : kernel_text -∗ instr (mword_of_int (PC + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
Proof. mk_rvc (PC + 0x06)%Z (mword_of_int 0xe426 : mword 16)
  (mword_of_int (PC + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.
Lemma pci_08 : kernel_text -∗ instr (mword_of_int (PC + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
Proof. mk_rvc (PC + 0x08)%Z (mword_of_int 0x1000 : mword 16)
  (mword_of_int (PC + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.
Lemma pci_0a : kernel_text -∗ instr (mword_of_int (PC + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
Proof. mk_rvc (PC + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
  (mword_of_int (PC + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.
Lemma pci_0c : kernel_text -∗ instr (mword_of_int (PC + 0x0c) : mword 64) false (JAL (mword_of_int 2081752 : mword 21, Regidx (mword_of_int 1))).
Proof. mk_base (PC + 0x0c)%Z (mword_of_int 0xbd8fc0ef : mword 32)
  (mword_of_int (PC + 0x0c) : mword 64) (JAL (mword_of_int 2081752 : mword 21, Regidx (mword_of_int 1))) pcdec_jal. Qed.
Lemma pci_10 : kernel_text -∗ instr (mword_of_int (PC + 0x10) : mword 64) false (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLIW)).
Proof. mk_base (PC + 0x10)%Z (mword_of_int 0x00d5179b : mword 32)
  (mword_of_int (PC + 0x10) : mword 64) (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLIW)) pcdec_slliw_a5. Qed.
Lemma pci_14 : kernel_text -∗ instr (mword_of_int (PC + 0x14) : mword 64) false (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 14), LUI)).
Proof. mk_base (PC + 0x14)%Z (mword_of_int 0x0c201737 : mword 32)
  (mword_of_int (PC + 0x14) : mword 64) (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 14), LUI)) pcdec_lui_a4. Qed.
Lemma pci_18 : kernel_text -∗ instr (mword_of_int (PC + 0x18) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
Proof. mk_rvc (PC + 0x18)%Z (mword_of_int 0x97ba : mword 16)
  (mword_of_int (PC + 0x18) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97ba exec_execute_C_ADD. Qed.
Lemma pci_1a : kernel_text -∗ instr (mword_of_int (PC + 0x1a) : mword 64) true (STORE (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 15), 4)).
Proof. mk_rvc (PC + 0x1a)%Z (mword_of_int 0xc3c4 : mword 16)
  (mword_of_int (PC + 0x1a) : mword 64) (STORE (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 15), 4)) pcdec_sw_s1 pcexec_sw_s1. Qed.
Lemma pci_1c : kernel_text -∗ instr (mword_of_int (PC + 0x1c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
Proof. mk_rvc (PC + 0x1c)%Z (mword_of_int 0x60e2 : mword 16)
  (mword_of_int (PC + 0x1c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.
Lemma pci_1e : kernel_text -∗ instr (mword_of_int (PC + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
Proof. mk_rvc (PC + 0x1e)%Z (mword_of_int 0x6442 : mword 16)
  (mword_of_int (PC + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.
Lemma pci_20 : kernel_text -∗ instr (mword_of_int (PC + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
Proof. mk_rvc (PC + 0x20)%Z (mword_of_int 0x64a2 : mword 16)
  (mword_of_int (PC + 0x20) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.
Lemma pci_22 : kernel_text -∗ instr (mword_of_int (PC + 0x22) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (PC + 0x22)%Z (mword_of_int 0x6105 : mword 16)
  (mword_of_int (PC + 0x22) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.
Lemma pci_24 : kernel_text -∗ instr (mword_of_int (PC + 0x24) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
Proof. mk_rvc (PC + 0x24)%Z (mword_of_int 0x8082 : mword 16)
  (mword_of_int (PC + 0x24) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodePlicComplete.
