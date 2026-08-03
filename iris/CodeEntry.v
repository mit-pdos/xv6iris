(* CodeEntry.v -- the machine code of _entry: the decode templates and the
   [instr] constructors for its instruction addresses.  Split out of WpEntryNew.v,
   which keeps the weakest preconditions over them. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RegFile RiscvPtsto RiscvExec RiscvFetchExec WpDecode WpEntry WpGpr.
Require Import WpAuipc WpMmodeMul WpMmodeJal.
Require Import WpMmodeLeafBase.
Require Import WpMmodeLoad.
Require Import WpGprCsrrA.
Require Import WpMmodeUtype.
Require Import WpMmodeItype.
Require Import WpMmodeRtype.
Require Import InstrBytes KernelText.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Local Open Scope Z_scope.
Section CodeEntry.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

Lemma decode_auipc s :
register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode w_auipc) s = Some (UTYPE (imm_auipc, Regidx i_auipc, AUIPC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; unfold imm_auipc, i_auipc; decode_any s Hpriv ]. Qed.
Lemma decode_ld s :
register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode w_ld) s = Some (LOAD (imm_ld, Regidx i_ld, Regidx i_ld, false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; unfold imm_ld, i_ld; decode_any s Hpriv ]. Qed.
(* PCs of the eight instructions. *)
Definition pc_e0 : mword 64 := mword_of_int (KernelSyms._entry).  (* AUIPC  *)
Definition pc_e1 : mword 64 := mword_of_int (KernelSyms._entry + 0x4).  (* LOAD   *)
Definition pc_e2 : mword 64 := mword_of_int (KernelSyms._entry + 0x8).  (* C.LUI  *)
Definition pc_e3 : mword 64 := mword_of_int (KernelSyms._entry + 0xa).  (* CSRRS  *)
Definition pc_e4 : mword 64 := mword_of_int (KernelSyms._entry + 0xe).  (* C.ADDI *)
Definition pc_e5 : mword 64 := mword_of_int (KernelSyms._entry + 0x10).  (* MUL    *)
Definition pc_e6 : mword 64 := mword_of_int (KernelSyms._entry + 0x14).  (* C.ADD  *)
Definition pc_e7 : mword 64 := mword_of_int (KernelSyms._entry + 0x16).  (* JAL    *)
Definition pc_start : mword 64 := mword_of_int (KernelSyms.start). (* start() *)

(* The value AUIPC writes to sp (= pc0 + (imm_auipc<<12) = 0x8000a000). *)
Definition entry_sp1 : mword 64 := add_vec pc_e0 (auipc_off imm_auipc).
Lemma entry_instr_auipc :
  kernel_text -∗ instr pc_e0 false (UTYPE (imm_auipc, Regidx i_auipc, AUIPC)).
Proof.
  mk_base KernelSyms._entry w_auipc pc_e0
    (UTYPE (imm_auipc, Regidx i_auipc, AUIPC)) decode_auipc.
Qed.
Lemma entry_instr_ld :
  kernel_text -∗ instr pc_e1 false (LOAD (imm_ld, Regidx i_ld, Regidx i_ld, false, 8)).
Proof.
  mk_base (KernelSyms._entry + 0x4)%Z w_ld pc_e1
    (LOAD (imm_ld, Regidx i_ld, Regidx i_ld, false, 8)) decode_ld.
Qed.
Lemma entry_instr_clui :
  kernel_text -∗ instr pc_e2 true (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)).
Proof.
  mk_rvc (KernelSyms._entry + 0x8)%Z h_lui pc_e2
    (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)) decode_C_lui exec_execute_C_LUI.
Qed.
Lemma entry_instr_csrr :
  kernel_text -∗ instr pc_e3 false (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS)).
Proof.
  mk_base (KernelSyms._entry + 0xa)%Z w_csrr pc_e3
    (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS)) decode_csrr.
Qed.
Lemma entry_instr_caddi :
  kernel_text -∗ instr pc_e4 true (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI)).
Proof.
  mk_rvc (KernelSyms._entry + 0xe)%Z h_addi pc_e4
    (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI)) decode_C_ADDI exec_execute_C_ADDI.
Qed.
Lemma entry_instr_mul :
  kernel_text -∗
  instr pc_e5 false (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul)).
Proof.
  mk_base (KernelSyms._entry + 0x10)%Z w_mul pc_e5
    (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul)) decode_mul.
Qed.
Lemma entry_instr_cadd :
  kernel_text -∗ instr pc_e6 true (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)).
Proof.
  mk_rvc (KernelSyms._entry + 0x14)%Z h_add pc_e6
    (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)) decode_C_ADD exec_execute_C_ADD.
Qed.
Lemma entry_instr_jal :
  kernel_text -∗ instr pc_e7 false (JAL (imm_jal, Regidx i_jal)).
Proof.
  mk_base (KernelSyms._entry + 0x16)%Z w_jal pc_e7
    (JAL (imm_jal, Regidx i_jal)) decode_jal.
Qed.

End CodeEntry.
