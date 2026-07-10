(* WpKallocDecode.v -- the instruction-DECODE layer for xv6's kalloc() and
   kfree().  For EVERY instruction of

     kalloc @ 0x80000b20 .. 0x80000b7a   (offsets 0x00 .. 0x5a)
     kfree  @ 0x80000a38 .. 0x80000aa2   (offsets 0x00 .. 0x68)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([kai_<off>] /
   [kfi_<off>]) plus the per-instruction decode facts they consume.  Pure
   mirror of WpMycpu.v (the [mk_base] / [mk_rvc2] / [mk_rvc4] templates) and
   the decode-fact style of WpPushOffTop / WpAcquireTop / WpRelease.

   Choice of [mk_rvc2] vs [mk_rvc4] for a compressed instruction is purely by
   the pc's 4-alignment: pc = base+off with base 4-aligned, so
       off mod 4 = 0  -> mk_rvc4 (w = (next_halfword << 16) | h),
       off mod 4 = 2  -> mk_rvc2.
   Base (4-byte) instructions always use [mk_base]. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes WpDecodeBridge.
Require Import WpGprRvc WpEntryNew.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Extra ExecuteAs-expansion facts not already in WpGprRvc: the           *)
(* compressed opcodes (c.ld / c.sd / c.bnez / c.beqz / c.j) that kalloc /  *)
(* kfree use.  Representation-independent, mirrors of the WpGprRvc ones.    *)
(* ===================================================================== *)
Lemma exec_execute_C_LD (uimm : mword 5) (rsc rdc : cregidx) s :
  exec (execute (C_LD (uimm, rsc, rdc))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")),
                           creg2reg_idx rsc, creg2reg_idx rdc, false, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_LD. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_SD (uimm : mword 5) (rsc1 rsc2 : cregidx) s :
  exec (execute (C_SD (uimm, rsc1, rsc2))) s
  = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                            creg2reg_idx rsc2, creg2reg_idx rsc1, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_SD. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_BNEZ (imm : mword 8) (rs : cregidx) s :
  exec (execute (C_BNEZ (imm, rs))) s
  = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg, creg2reg_idx rs, BNE)), s).
Proof. unfold execute. cbn match. unfold execute_C_BNEZ. apply exec_returnM. Qed.

Lemma exec_execute_C_BEQZ (imm : mword 8) (rs : cregidx) s :
  exec (execute (C_BEQZ (imm, rs))) s
  = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg, creg2reg_idx rs, BEQ)), s).
Proof. unfold execute. cbn match. unfold execute_C_BEQZ. apply exec_returnM. Qed.

Lemma exec_execute_C_J (imm : mword 11) s :
  exec (execute (C_J imm)) s
  = Some (ExecuteAs (JAL (sign_extend' 21 (concat_vec imm ('b"0")), zreg)), s).
Proof. unfold execute. cbn match. unfold execute_C_J. apply exec_returnM. Qed.

(* ===================================================================== *)
(* Compressed decode facts (one per distinct 16-bit encoding).            *)
(* ===================================================================== *)
Lemma kdc_1101 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1101 : mword 16)) s
  = Some (C_ADDI (mword_of_int 32, Regidx csp_rs1), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_1141 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1141 : mword 16)) s
  = Some (C_ADDI (mword_of_int 48, Regidx csp_rs1), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_ec06 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec06 : mword 16)) s
  = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_e822 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe822 : mword 16)) s
  = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_e426 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe426 : mword 16)) s
  = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_e04a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe04a : mword 16)) s
  = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_1000 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1000 : mword 16)) s
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 8), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_c49d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc49d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 23, Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_609c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x609c : mword 16)) s
  = Some (C_LD (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_6605 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6605 : mword 16)) s
  = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_4595 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4595 : mword 16)) s
  = Some (C_LI (mword_of_int 5, Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_8526 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8526 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_60e2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x60e2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_6442 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6442 : mword 16)) s
  = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_64a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x64a2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_6902 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6902 : mword 16)) s
  = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_6105 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6105 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 2 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_8082 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) s
  = Some (C_JR (Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_b7e5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb7e5 : mword 16)) s
  = Some (C_J (mword_of_int 2036 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_47c5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x47c5 : mword 16)) s
  = Some (C_LI (mword_of_int 17, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_07ee s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x07ee : mword 16)) s
  = Some (C_SLLI (mword_of_int 27, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_17fd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x17fd : mword 16)) s
  = Some (C_ADDI (mword_of_int 63, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_8fd9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8fd9 : mword 16)) s
  = Some (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_ef95 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xef95 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 30, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_84aa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84aa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_eb95 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xeb95 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 26, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_4585 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4585 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_854a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x854a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma kdc_e09c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe09c : mword 16)) s
  = Some (C_SD (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts (one per distinct 32-bit encoding).         *)
(* ===================================================================== *)
Lemma kdb_00011517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00011517 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_00012497 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00012497 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x12 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_00011717 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00011717 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_00023797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00023797 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x23 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_00012917 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00012917 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x12 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_00006517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00006517 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x6 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_7fe50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7fe50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x7fe : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_7de50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7de50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x7de : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_7bc50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7bc50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x7bc : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_b1478793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb1478793 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xb14 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_8ba90913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8ba90913 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x8ba : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_5a050513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5a050513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x5a0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_0c8000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0c8000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xc8 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_130000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x130000ef : mword 32)) s
  = Some (JAL (mword_of_int 0x130 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_15e000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x15e000ef : mword 32)) s
  = Some (JAL (mword_of_int 0x15e : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_10e000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10e000ef : mword 32)) s
  = Some (JAL (mword_of_int 0x10e : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_250000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x250000ef : mword 32)) s
  = Some (JAL (mword_of_int 0x250 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_182000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x182000ef : mword 32)) s
  = Some (JAL (mword_of_int 0x182 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_1fa000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x1fa000ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fa : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_d79ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd79ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1ffd78 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_80a4b483 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x80a4b483 : mword 32)) s
  = Some (LOAD (mword_of_int 0x80a : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_01893783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01893783 : mword 32)) s
  = Some (LOAD (mword_of_int 0x18 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), false, 8), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_7ef73f23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7ef73f23 : mword 32)) s
  = Some (STORE (mword_of_int 0x7fe : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 8), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_00993c23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00993c23 : mword 32)) s
  = Some (STORE (mword_of_int 0x18 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 18), 8), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_00f53733 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f53733 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLTU), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_00a7b7b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00a7b7b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLTU), s).
Proof. decode_bridge_ms. Qed.

Lemma kdb_03451793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03451793 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLI), s).
Proof. decode_bridge_ms. Qed.

Section WpKallocDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* The three [instr]-builder templates, copied verbatim from WpMycpu.   *)
  (* ------------------------------------------------------------------- *)
  Local Ltac mk_rvc4 A h w pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hsub := fresh "Hsub" in let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = true) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hsub : subrange_vec_dec w 15 0 = h) by (apply bv_eq; vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc4 pc h w H2al H4al Hrvc Hsub);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_rvc2 A h pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = false) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte h j))
      by (intros j Hj;
          do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc2 pc h H2al H4al Hrvc);
      iApply (kernel_window_pc A h 2 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_base A w pc ast decname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let Hnrvc := fresh "Hnrvc" in let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (Hnrvc : isRVC (subrange_vec_dec w 15 0) = false) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_Base w);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_base pc w H2al Hnrvc);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; apply decname; assumption ].

  Notation KA := KernelSyms.kalloc.
  Notation KF := KernelSyms.kfree.

  (* =================================================================== *)
  (*  kalloc @ 0x80000b20, offsets 0x00 .. 0x5a.                          *)
  (* =================================================================== *)
  Lemma kai_00 : kernel_text -∗ instr (mword_of_int (KA + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc4 (KA + 0x00)%Z (mword_of_int 0x1101 : mword 16) (mword_of_int 0xec061101 : mword 32)
    (mword_of_int (KA + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) kdc_1101 exec_execute_C_ADDI. Qed.

  Lemma kai_02 : kernel_text -∗ instr (mword_of_int (KA + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc2 (KA + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KA + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) kdc_ec06 exec_execute_C_SDSP. Qed.

  Lemma kai_04 : kernel_text -∗ instr (mword_of_int (KA + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc4 (KA + 0x04)%Z (mword_of_int 0xe822 : mword 16) (mword_of_int 0xe426e822 : mword 32)
    (mword_of_int (KA + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) kdc_e822 exec_execute_C_SDSP. Qed.

  Lemma kai_06 : kernel_text -∗ instr (mword_of_int (KA + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc2 (KA + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KA + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) kdc_e426 exec_execute_C_SDSP. Qed.

  Lemma kai_08 : kernel_text -∗ instr (mword_of_int (KA + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc4 (KA + 0x08)%Z (mword_of_int 0x1000 : mword 16) (mword_of_int 0x15171000 : mword 32)
    (mword_of_int (KA + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) kdc_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma kai_0a : kernel_text -∗ instr (mword_of_int (KA + 0x0a) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KA + 0x0a)%Z (mword_of_int 0x00011517 : mword 32)
    (mword_of_int (KA + 0x0a) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)) kdb_00011517. Qed.

  Lemma kai_0e : kernel_text -∗ instr (mword_of_int (KA + 0x0e) : mword 64) false (ITYPE (mword_of_int 0x7fe : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KA + 0x0e)%Z (mword_of_int 0x7fe50513 : mword 32)
    (mword_of_int (KA + 0x0e) : mword 64) (ITYPE (mword_of_int 0x7fe : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) kdb_7fe50513. Qed.

  Lemma kai_12 : kernel_text -∗ instr (mword_of_int (KA + 0x12) : mword 64) false (JAL (mword_of_int 0xc8 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KA + 0x12)%Z (mword_of_int 0x0c8000ef : mword 32)
    (mword_of_int (KA + 0x12) : mword 64) (JAL (mword_of_int 0xc8 : mword 21, Regidx (mword_of_int 1))) kdb_0c8000ef. Qed.

  Lemma kai_16 : kernel_text -∗ instr (mword_of_int (KA + 0x16) : mword 64) false (UTYPE (mword_of_int 0x12 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (KA + 0x16)%Z (mword_of_int 0x00012497 : mword 32)
    (mword_of_int (KA + 0x16) : mword 64) (UTYPE (mword_of_int 0x12 : mword 20, Regidx (mword_of_int 9), AUIPC)) kdb_00012497. Qed.

  Lemma kai_1a : kernel_text -∗ instr (mword_of_int (KA + 0x1a) : mword 64) false (LOAD (mword_of_int 0x80a : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)).
  Proof. mk_base (KA + 0x1a)%Z (mword_of_int 0x80a4b483 : mword 32)
    (mword_of_int (KA + 0x1a) : mword 64) (LOAD (mword_of_int 0x80a : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)) kdb_80a4b483. Qed.

  Lemma kai_1e : kernel_text -∗ instr (mword_of_int (KA + 0x1e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 23 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BEQ)).
  Proof. mk_rvc2 (KA + 0x1e)%Z (mword_of_int 0xc49d : mword 16)
    (mword_of_int (KA + 0x1e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 23 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BEQ)) kdc_c49d exec_execute_C_BEQZ. Qed.

  Lemma kai_20 : kernel_text -∗ instr (mword_of_int (KA + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc4 (KA + 0x20)%Z (mword_of_int 0x609c : mword 16) (mword_of_int 0x1717609c : mword 32)
    (mword_of_int (KA + 0x20) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) kdc_609c exec_execute_C_LD. Qed.

  Lemma kai_22 : kernel_text -∗ instr (mword_of_int (KA + 0x22) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (KA + 0x22)%Z (mword_of_int 0x00011717 : mword 32)
    (mword_of_int (KA + 0x22) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 14), AUIPC)) kdb_00011717. Qed.

  Lemma kai_26 : kernel_text -∗ instr (mword_of_int (KA + 0x26) : mword 64) false (STORE (mword_of_int 0x7fe : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 8)).
  Proof. mk_base (KA + 0x26)%Z (mword_of_int 0x7ef73f23 : mword 32)
    (mword_of_int (KA + 0x26) : mword 64) (STORE (mword_of_int 0x7fe : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 8)) kdb_7ef73f23. Qed.

  Lemma kai_2a : kernel_text -∗ instr (mword_of_int (KA + 0x2a) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KA + 0x2a)%Z (mword_of_int 0x00011517 : mword 32)
    (mword_of_int (KA + 0x2a) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)) kdb_00011517. Qed.

  Lemma kai_2e : kernel_text -∗ instr (mword_of_int (KA + 0x2e) : mword 64) false (ITYPE (mword_of_int 0x7de : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KA + 0x2e)%Z (mword_of_int 0x7de50513 : mword 32)
    (mword_of_int (KA + 0x2e) : mword 64) (ITYPE (mword_of_int 0x7de : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) kdb_7de50513. Qed.

  Lemma kai_32 : kernel_text -∗ instr (mword_of_int (KA + 0x32) : mword 64) false (JAL (mword_of_int 0x130 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KA + 0x32)%Z (mword_of_int 0x130000ef : mword 32)
    (mword_of_int (KA + 0x32) : mword 64) (JAL (mword_of_int 0x130 : mword 21, Regidx (mword_of_int 1))) kdb_130000ef. Qed.

  Lemma kai_36 : kernel_text -∗ instr (mword_of_int (KA + 0x36) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).
  Proof. mk_rvc2 (KA + 0x36)%Z (mword_of_int 0x6605 : mword 16)
    (mword_of_int (KA + 0x36) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) kdc_6605 exec_execute_C_LUI. Qed.

  Lemma kai_38 : kernel_text -∗ instr (mword_of_int (KA + 0x38) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc4 (KA + 0x38)%Z (mword_of_int 0x4595 : mword 16) (mword_of_int 0x85264595 : mword 32)
    (mword_of_int (KA + 0x38) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) kdc_4595 exec_execute_C_LI. Qed.

  Lemma kai_3a : kernel_text -∗ instr (mword_of_int (KA + 0x3a) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc2 (KA + 0x3a)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KA + 0x3a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) kdc_8526 exec_execute_C_MV. Qed.

  Lemma kai_3c : kernel_text -∗ instr (mword_of_int (KA + 0x3c) : mword 64) false (JAL (mword_of_int 0x15e : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KA + 0x3c)%Z (mword_of_int 0x15e000ef : mword 32)
    (mword_of_int (KA + 0x3c) : mword 64) (JAL (mword_of_int 0x15e : mword 21, Regidx (mword_of_int 1))) kdb_15e000ef. Qed.

  Lemma kai_40 : kernel_text -∗ instr (mword_of_int (KA + 0x40) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc4 (KA + 0x40)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int 0x60e28526 : mword 32)
    (mword_of_int (KA + 0x40) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) kdc_8526 exec_execute_C_MV. Qed.

  Lemma kai_42 : kernel_text -∗ instr (mword_of_int (KA + 0x42) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc2 (KA + 0x42)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KA + 0x42) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) kdc_60e2 exec_execute_C_LDSP. Qed.

  Lemma kai_44 : kernel_text -∗ instr (mword_of_int (KA + 0x44) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc4 (KA + 0x44)%Z (mword_of_int 0x6442 : mword 16) (mword_of_int 0x64a26442 : mword 32)
    (mword_of_int (KA + 0x44) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) kdc_6442 exec_execute_C_LDSP. Qed.

  Lemma kai_46 : kernel_text -∗ instr (mword_of_int (KA + 0x46) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc2 (KA + 0x46)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KA + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) kdc_64a2 exec_execute_C_LDSP. Qed.

  Lemma kai_48 : kernel_text -∗ instr (mword_of_int (KA + 0x48) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc4 (KA + 0x48)%Z (mword_of_int 0x6105 : mword 16) (mword_of_int 0x80826105 : mword 32)
    (mword_of_int (KA + 0x48) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) kdc_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma kai_4a : kernel_text -∗ instr (mword_of_int (KA + 0x4a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc2 (KA + 0x4a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KA + 0x4a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) kdc_8082 exec_execute_C_JR. Qed.

  Lemma kai_4c : kernel_text -∗ instr (mword_of_int (KA + 0x4c) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KA + 0x4c)%Z (mword_of_int 0x00011517 : mword 32)
    (mword_of_int (KA + 0x4c) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)) kdb_00011517. Qed.

  Lemma kai_50 : kernel_text -∗ instr (mword_of_int (KA + 0x50) : mword 64) false (ITYPE (mword_of_int 0x7bc : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KA + 0x50)%Z (mword_of_int 0x7bc50513 : mword 32)
    (mword_of_int (KA + 0x50) : mword 64) (ITYPE (mword_of_int 0x7bc : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) kdb_7bc50513. Qed.

  Lemma kai_54 : kernel_text -∗ instr (mword_of_int (KA + 0x54) : mword 64) false (JAL (mword_of_int 0x10e : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KA + 0x54)%Z (mword_of_int 0x10e000ef : mword 32)
    (mword_of_int (KA + 0x54) : mword 64) (JAL (mword_of_int 0x10e : mword 21, Regidx (mword_of_int 1))) kdb_10e000ef. Qed.

  Lemma kai_58 : kernel_text -∗ instr (mword_of_int (KA + 0x58) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc4 (KA + 0x58)%Z (mword_of_int 0xb7e5 : mword 16) (mword_of_int 0x1141b7e5 : mword 32)
    (mword_of_int (KA + 0x58) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")), zreg)) kdc_b7e5 exec_execute_C_J. Qed.

  (* =================================================================== *)
  (*  kfree @ 0x80000a38, offsets 0x00 .. 0x68.                           *)
  (* =================================================================== *)
  Lemma kfi_00 : kernel_text -∗ instr (mword_of_int (KF + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc4 (KF + 0x00)%Z (mword_of_int 0x1101 : mword 16) (mword_of_int 0xec061101 : mword 32)
    (mword_of_int (KF + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) kdc_1101 exec_execute_C_ADDI. Qed.

  Lemma kfi_02 : kernel_text -∗ instr (mword_of_int (KF + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc2 (KF + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KF + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) kdc_ec06 exec_execute_C_SDSP. Qed.

  Lemma kfi_04 : kernel_text -∗ instr (mword_of_int (KF + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc4 (KF + 0x04)%Z (mword_of_int 0xe822 : mword 16) (mword_of_int 0xe426e822 : mword 32)
    (mword_of_int (KF + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) kdc_e822 exec_execute_C_SDSP. Qed.

  Lemma kfi_06 : kernel_text -∗ instr (mword_of_int (KF + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc2 (KF + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KF + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) kdc_e426 exec_execute_C_SDSP. Qed.

  Lemma kfi_08 : kernel_text -∗ instr (mword_of_int (KF + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc4 (KF + 0x08)%Z (mword_of_int 0xe04a : mword 16) (mword_of_int 0x1000e04a : mword 32)
    (mword_of_int (KF + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) kdc_e04a exec_execute_C_SDSP. Qed.

  Lemma kfi_0a : kernel_text -∗ instr (mword_of_int (KF + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc2 (KF + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KF + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) kdc_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma kfi_0c : kernel_text -∗ instr (mword_of_int (KF + 0x0c) : mword 64) false (UTYPE (mword_of_int 0x23 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (KF + 0x0c)%Z (mword_of_int 0x00023797 : mword 32)
    (mword_of_int (KF + 0x0c) : mword 64) (UTYPE (mword_of_int 0x23 : mword 20, Regidx (mword_of_int 15), AUIPC)) kdb_00023797. Qed.

  Lemma kfi_10 : kernel_text -∗ instr (mword_of_int (KF + 0x10) : mword 64) false (ITYPE (mword_of_int 0xb14 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (KF + 0x10)%Z (mword_of_int 0xb1478793 : mword 32)
    (mword_of_int (KF + 0x10) : mword 64) (ITYPE (mword_of_int 0xb14 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) kdb_b1478793. Qed.

  Lemma kfi_14 : kernel_text -∗ instr (mword_of_int (KF + 0x14) : mword 64) false (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLTU)).
  Proof. mk_base (KF + 0x14)%Z (mword_of_int 0x00f53733 : mword 32)
    (mword_of_int (KF + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLTU)) kdb_00f53733. Qed.

  Lemma kfi_18 : kernel_text -∗ instr (mword_of_int (KF + 0x18) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 17 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc4 (KF + 0x18)%Z (mword_of_int 0x47c5 : mword 16) (mword_of_int 0x07ee47c5 : mword 32)
    (mword_of_int (KF + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 17 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) kdc_47c5 exec_execute_C_LI. Qed.

  Lemma kfi_1a : kernel_text -∗ instr (mword_of_int (KF + 0x1a) : mword 64) true (SHIFTIOP (mword_of_int 27 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc2 (KF + 0x1a)%Z (mword_of_int 0x07ee : mword 16)
    (mword_of_int (KF + 0x1a) : mword 64) (SHIFTIOP (mword_of_int 27 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) kdc_07ee exec_execute_C_SLLI. Qed.

  Lemma kfi_1c : kernel_text -∗ instr (mword_of_int (KF + 0x1c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc4 (KF + 0x1c)%Z (mword_of_int 0x17fd : mword 16) (mword_of_int 0xb7b317fd : mword 32)
    (mword_of_int (KF + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) kdc_17fd exec_execute_C_ADDI. Qed.

  Lemma kfi_1e : kernel_text -∗ instr (mword_of_int (KF + 0x1e) : mword 64) false (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLTU)).
  Proof. mk_base (KF + 0x1e)%Z (mword_of_int 0x00a7b7b3 : mword 32)
    (mword_of_int (KF + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLTU)) kdb_00a7b7b3. Qed.

  Lemma kfi_22 : kernel_text -∗ instr (mword_of_int (KF + 0x22) : mword 64) true (RTYPE (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), OR)).
  Proof. mk_rvc2 (KF + 0x22)%Z (mword_of_int 0x8fd9 : mword 16)
    (mword_of_int (KF + 0x22) : mword 64) (RTYPE (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), OR)) kdc_8fd9 exec_execute_C_OR. Qed.

  Lemma kfi_24 : kernel_text -∗ instr (mword_of_int (KF + 0x24) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 30 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc4 (KF + 0x24)%Z (mword_of_int 0xef95 : mword 16) (mword_of_int 0x84aaef95 : mword 32)
    (mword_of_int (KF + 0x24) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 30 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) kdc_ef95 exec_execute_C_BNEZ. Qed.

  Lemma kfi_26 : kernel_text -∗ instr (mword_of_int (KF + 0x26) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc2 (KF + 0x26)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (KF + 0x26) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) kdc_84aa exec_execute_C_MV. Qed.

  Lemma kfi_28 : kernel_text -∗ instr (mword_of_int (KF + 0x28) : mword 64) false (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_base (KF + 0x28)%Z (mword_of_int 0x03451793 : mword 32)
    (mword_of_int (KF + 0x28) : mword 64) (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLI)) kdb_03451793. Qed.

  Lemma kfi_2c : kernel_text -∗ instr (mword_of_int (KF + 0x2c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 26 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc4 (KF + 0x2c)%Z (mword_of_int 0xeb95 : mword 16) (mword_of_int 0x6605eb95 : mword 32)
    (mword_of_int (KF + 0x2c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 26 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) kdc_eb95 exec_execute_C_BNEZ. Qed.

  Lemma kfi_2e : kernel_text -∗ instr (mword_of_int (KF + 0x2e) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).
  Proof. mk_rvc2 (KF + 0x2e)%Z (mword_of_int 0x6605 : mword 16)
    (mword_of_int (KF + 0x2e) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) kdc_6605 exec_execute_C_LUI. Qed.

  Lemma kfi_30 : kernel_text -∗ instr (mword_of_int (KF + 0x30) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc4 (KF + 0x30)%Z (mword_of_int 0x4585 : mword 16) (mword_of_int 0x00ef4585 : mword 32)
    (mword_of_int (KF + 0x30) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) kdc_4585 exec_execute_C_LI. Qed.

  Lemma kfi_32 : kernel_text -∗ instr (mword_of_int (KF + 0x32) : mword 64) false (JAL (mword_of_int 0x250 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KF + 0x32)%Z (mword_of_int 0x250000ef : mword 32)
    (mword_of_int (KF + 0x32) : mword 64) (JAL (mword_of_int 0x250 : mword 21, Regidx (mword_of_int 1))) kdb_250000ef. Qed.

  Lemma kfi_36 : kernel_text -∗ instr (mword_of_int (KF + 0x36) : mword 64) false (UTYPE (mword_of_int 0x12 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (KF + 0x36)%Z (mword_of_int 0x00012917 : mword 32)
    (mword_of_int (KF + 0x36) : mword 64) (UTYPE (mword_of_int 0x12 : mword 20, Regidx (mword_of_int 18), AUIPC)) kdb_00012917. Qed.

  Lemma kfi_3a : kernel_text -∗ instr (mword_of_int (KF + 0x3a) : mword 64) false (ITYPE (mword_of_int 0x8ba : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (KF + 0x3a)%Z (mword_of_int 0x8ba90913 : mword 32)
    (mword_of_int (KF + 0x3a) : mword 64) (ITYPE (mword_of_int 0x8ba : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) kdb_8ba90913. Qed.

  Lemma kfi_3e : kernel_text -∗ instr (mword_of_int (KF + 0x3e) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc2 (KF + 0x3e)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (KF + 0x3e) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) kdc_854a exec_execute_C_MV. Qed.

  Lemma kfi_40 : kernel_text -∗ instr (mword_of_int (KF + 0x40) : mword 64) false (JAL (mword_of_int 0x182 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KF + 0x40)%Z (mword_of_int 0x182000ef : mword 32)
    (mword_of_int (KF + 0x40) : mword 64) (JAL (mword_of_int 0x182 : mword 21, Regidx (mword_of_int 1))) kdb_182000ef. Qed.

  Lemma kfi_44 : kernel_text -∗ instr (mword_of_int (KF + 0x44) : mword 64) false (LOAD (mword_of_int 0x18 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (KF + 0x44)%Z (mword_of_int 0x01893783 : mword 32)
    (mword_of_int (KF + 0x44) : mword 64) (LOAD (mword_of_int 0x18 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), false, 8)) kdb_01893783. Qed.

  Lemma kfi_48 : kernel_text -∗ instr (mword_of_int (KF + 0x48) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 1)), 8)).
  Proof. mk_rvc4 (KF + 0x48)%Z (mword_of_int 0xe09c : mword 16) (mword_of_int 0x3c23e09c : mword 32)
    (mword_of_int (KF + 0x48) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 1)), 8)) kdc_e09c exec_execute_C_SD. Qed.

  Lemma kfi_4a : kernel_text -∗ instr (mword_of_int (KF + 0x4a) : mword 64) false (STORE (mword_of_int 0x18 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 18), 8)).
  Proof. mk_base (KF + 0x4a)%Z (mword_of_int 0x00993c23 : mword 32)
    (mword_of_int (KF + 0x4a) : mword 64) (STORE (mword_of_int 0x18 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 18), 8)) kdb_00993c23. Qed.

  Lemma kfi_4e : kernel_text -∗ instr (mword_of_int (KF + 0x4e) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc2 (KF + 0x4e)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (KF + 0x4e) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) kdc_854a exec_execute_C_MV. Qed.

  Lemma kfi_50 : kernel_text -∗ instr (mword_of_int (KF + 0x50) : mword 64) false (JAL (mword_of_int 0x1fa : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KF + 0x50)%Z (mword_of_int 0x1fa000ef : mword 32)
    (mword_of_int (KF + 0x50) : mword 64) (JAL (mword_of_int 0x1fa : mword 21, Regidx (mword_of_int 1))) kdb_1fa000ef. Qed.

  Lemma kfi_54 : kernel_text -∗ instr (mword_of_int (KF + 0x54) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc4 (KF + 0x54)%Z (mword_of_int 0x60e2 : mword 16) (mword_of_int 0x644260e2 : mword 32)
    (mword_of_int (KF + 0x54) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) kdc_60e2 exec_execute_C_LDSP. Qed.

  Lemma kfi_56 : kernel_text -∗ instr (mword_of_int (KF + 0x56) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc2 (KF + 0x56)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KF + 0x56) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) kdc_6442 exec_execute_C_LDSP. Qed.

  Lemma kfi_58 : kernel_text -∗ instr (mword_of_int (KF + 0x58) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc4 (KF + 0x58)%Z (mword_of_int 0x64a2 : mword 16) (mword_of_int 0x690264a2 : mword 32)
    (mword_of_int (KF + 0x58) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) kdc_64a2 exec_execute_C_LDSP. Qed.

  Lemma kfi_5a : kernel_text -∗ instr (mword_of_int (KF + 0x5a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc2 (KF + 0x5a)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (KF + 0x5a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) kdc_6902 exec_execute_C_LDSP. Qed.

  Lemma kfi_5c : kernel_text -∗ instr (mword_of_int (KF + 0x5c) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc4 (KF + 0x5c)%Z (mword_of_int 0x6105 : mword 16) (mword_of_int 0x80826105 : mword 32)
    (mword_of_int (KF + 0x5c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) kdc_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma kfi_5e : kernel_text -∗ instr (mword_of_int (KF + 0x5e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc2 (KF + 0x5e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KF + 0x5e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) kdc_8082 exec_execute_C_JR. Qed.

End WpKallocDecode.
