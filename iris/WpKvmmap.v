(* WpKvmmap.v -- the whole-function proof of kvmmap() (kernel/vm.c):
   a thin wrapper that swaps mappages's size/pa arguments, calls mappages,
   and panics on failure.  Spec of record: KvmSpec.v's [kvmmap_spec].
   The frame decodes are the shared 16-byte templates in KernelRvcDecode;
   only the three arg-shuffling c.mv, the failure c.bnez, and the base jals
   are decoded locally.  The -1 arm is absorbed by [panic_wp].            *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import KernelText WpAuipc.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SRegime.
Require Import SmodeCore.
Require Import WpLock.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import PtTree.
Require Import PtBuild KvmSpec.
Require Import WpSmodePtAlu WpSmodePtBtype WpSmodePtCtl.
Require Import WpSmodePtMemWrap.
Require Import UserBits.
Require Import KernelRvcDecode WpRvcBridge WpDecode WpDecodeBridge.
Require Export WpSmodeLeafBase.
From Kernel Require KernelSyms.
Import Defs.

Section Kvmmap.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation KM := KernelSyms.kvmmap.

  (* ---- the arg-shuffle c.mv decode facts ---- *)
  Lemma kvdec_mv_a5a3 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x87b6 : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 13)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kvdec_mv_a3a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x86b2 : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 13), Regidx (mword_of_int 12)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kvdec_mv_a2a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x863e : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 15)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kvdec_bnez s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe509 : mword 16)) s
    = Some (C_BNEZ (mword_of_int 5, Cregidx (mword_of_int 2)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

  (* ---- the base jals ---- *)
  Lemma kvdec_jal_mp s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xf3dff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2096956 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

  (* ---- instr facts ---- *)
  Local Notation KMP off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KM + off) : mword 64) rvc ast).

  Lemma ki_00 : KMP 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KM + 0x00)%Z (mword_of_int 0x1141 : mword 16) (mword_of_int (KM + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.
  Lemma ki_02 : KMP 0x02 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KM + 0x02)%Z (mword_of_int 0xe406 : mword 16) (mword_of_int (KM + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.
  Lemma ki_04 : KMP 0x04 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KM + 0x04)%Z (mword_of_int 0xe022 : mword 16) (mword_of_int (KM + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.
  Lemma ki_06 : KMP 0x06 true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KM + 0x06)%Z (mword_of_int 0x0800 : mword 16) (mword_of_int (KM + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.
  Lemma ki_08 : KMP 0x08 true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (KM + 0x08)%Z (mword_of_int 0x87b6 : mword 16) (mword_of_int (KM + 0x08) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 15), ADD)) kvdec_mv_a5a3 exec_execute_C_MV. Qed.
  Lemma ki_0a : KMP 0x0a true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (KM + 0x0a)%Z (mword_of_int 0x86b2 : mword 16) (mword_of_int (KM + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 13), ADD)) kvdec_mv_a3a2 exec_execute_C_MV. Qed.
  Lemma ki_0c : KMP 0x0c true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (KM + 0x0c)%Z (mword_of_int 0x863e : mword 16) (mword_of_int (KM + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 12), ADD)) kvdec_mv_a2a5 exec_execute_C_MV. Qed.
  Lemma ki_0e : KMP 0x0e false (JAL (mword_of_int 2096956 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KM + 0x0e)%Z (mword_of_int 0xf3dff0ef : mword 32) (mword_of_int (KM + 0x0e) : mword 64) (JAL (mword_of_int 2096956 : mword 21, Regidx (mword_of_int 1))) kvdec_jal_mp. Qed.
  Lemma ki_12 : KMP 0x12 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).
  Proof. mk_rvc (KM + 0x12)%Z (mword_of_int 0xe509 : mword 16) (mword_of_int (KM + 0x12) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) kvdec_bnez exec_execute_C_BNEZ. Qed.
  Lemma ki_14 : KMP 0x14 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KM + 0x14)%Z (mword_of_int 0x60a2 : mword 16) (mword_of_int (KM + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.
  Lemma ki_16 : KMP 0x16 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KM + 0x16)%Z (mword_of_int 0x6402 : mword 16) (mword_of_int (KM + 0x16) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.
  Lemma ki_18 : KMP 0x18 true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KM + 0x18)%Z (mword_of_int 0x0141 : mword 16) (mword_of_int (KM + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.
  Lemma ki_1a : KMP 0x1a true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KM + 0x1a)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (KM + 0x1a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* ---- the (unreachable-return) panic arm ---- *)
  Lemma kvdec_auipc s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00006517 : mword 32)) s
    = Some (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kvdec_addi s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x01650513 : mword 32)) s
    = Some (ITYPE (mword_of_int 0x16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kvdec_jal_pn s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xf1cff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2094876 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

  Lemma ki_1c : KMP 0x1c false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KM + 0x1c)%Z (mword_of_int 0x00006517 : mword 32) (mword_of_int (KM + 0x1c) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)) kvdec_auipc. Qed.
  Lemma ki_20 : KMP 0x20 false (ITYPE (mword_of_int 0x16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KM + 0x20)%Z (mword_of_int 0x01650513 : mword 32) (mword_of_int (KM + 0x20) : mword 64) (ITYPE (mword_of_int 0x16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) kvdec_addi. Qed.
  Lemma ki_24 : KMP 0x24 false (JAL (mword_of_int 2094876 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KM + 0x24)%Z (mword_of_int 0xf1cff0ef : mword 32) (mword_of_int (KM + 0x24) : mword 64) (JAL (mword_of_int 2094876 : mword 21, Regidx (mword_of_int 1))) kvdec_jal_pn. Qed.

  (* ================================================================= *)
  (* THE WHOLE FUNCTION.                                                 *)
  (* ================================================================= *)

  (* the record spec *)

End Kvmmap.
