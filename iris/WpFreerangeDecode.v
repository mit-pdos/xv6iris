(* WpFreerangeDecode.v -- the instruction-DECODE layer for xv6's freerange().
   For every instruction of

     freerange @ 0x80000ab2 .. 0x80000af8   (offsets 0x00 .. 0x46)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([fri_<off>]) plus
   the per-instruction decode facts they consume ([fdc_<word>] compressed /
   [fdb_<word>] base).  Pure mirror of WpKallocDecode.v. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpDecodeBridge.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts (one per distinct 16-bit encoding).            *)
(* ===================================================================== *)
Lemma fdc_7179 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7179 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 61 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_f406 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf406 : mword 16)) s
  = Some (C_SDSP (mword_of_int 5, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_f022 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf022 : mword 16)) s
  = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_ec26 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec26 : mword 16)) s
  = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_1800 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1800 : mword 16)) s
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 12 : mword 8), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_6785 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6785 : mword 16)) s
  = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_777d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x777d : mword 16)) s
  = Some (C_LUI (mword_of_int 63, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_8cf9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8cf9 : mword 16)) s
  = Some (C_AND (Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_94be s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x94be : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 9), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_94ce s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x94ce : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 9), Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_e84a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe84a : mword 16)) s
  = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_e44e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe44e : mword 16)) s
  = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_e052 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe052 : mword 16)) s
  = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_892e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x892e : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 18), Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_8a3a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8a3a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 20), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_89be s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x89be : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 19), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_6942 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6942 : mword 16)) s
  = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_69a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x69a2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_6a02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6a02 : mword 16)) s
  = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_70a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x70a2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_7402 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7402 : mword 16)) s
  = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_64e2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x64e2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_6145 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6145 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 3 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_8082 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) s
  = Some (C_JR (Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (32-bit) decode facts.                                            *)
(* ===================================================================== *)
Lemma fdb_fff78713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfff78713 : mword 32)) s
  = Some (ITYPE (mword_of_int 4095 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_00e504b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e504b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 10), Regidx (mword_of_int 9), ADD), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_01448533 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01448533 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADD), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_0295e263 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0295e263 : mword 32)) s
  = Some (BTYPE (mword_of_int 36 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 11), BLTU), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_fe997be3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe997be3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 18), BGEU), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_f67ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf67ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096998 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Section WpFreerangeDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation FR := KernelSyms.freerange.

  Lemma fri_00 : kernel_text -∗ instr (mword_of_int (FR + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (FR + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (FR + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) fdc_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma fri_02 : kernel_text -∗ instr (mword_of_int (FR + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (FR + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (FR + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) fdc_f406 exec_execute_C_SDSP. Qed.

  Lemma fri_04 : kernel_text -∗ instr (mword_of_int (FR + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (FR + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (FR + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) fdc_f022 exec_execute_C_SDSP. Qed.

  Lemma fri_06 : kernel_text -∗ instr (mword_of_int (FR + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (FR + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (FR + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) fdc_ec26 exec_execute_C_SDSP. Qed.

  Lemma fri_08 : kernel_text -∗ instr (mword_of_int (FR + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (FR + 0x08)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (FR + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) fdc_1800 exec_execute_C_ADDI4SPN. Qed.

  Lemma fri_0a : kernel_text -∗ instr (mword_of_int (FR + 0x0a) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), LUI)).
  Proof. mk_rvc (FR + 0x0a)%Z (mword_of_int 0x6785 : mword 16)
    (mword_of_int (FR + 0x0a) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), LUI)) fdc_6785 exec_execute_C_LUI. Qed.

  Lemma fri_0c : kernel_text -∗ instr (mword_of_int (FR + 0x0c) : mword 64) false (ITYPE (mword_of_int 4095 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (FR + 0x0c)%Z (mword_of_int 0xfff78713 : mword 32)
    (mword_of_int (FR + 0x0c) : mword 64) (ITYPE (mword_of_int 4095 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) fdb_fff78713. Qed.

  Lemma fri_10 : kernel_text -∗ instr (mword_of_int (FR + 0x10) : mword 64) false (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 10), Regidx (mword_of_int 9), ADD)).
  Proof. mk_base (FR + 0x10)%Z (mword_of_int 0x00e504b3 : mword 32)
    (mword_of_int (FR + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 10), Regidx (mword_of_int 9), ADD)) fdb_00e504b3. Qed.

  Lemma fri_14 : kernel_text -∗ instr (mword_of_int (FR + 0x14) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 14), LUI)).
  Proof. mk_rvc (FR + 0x14)%Z (mword_of_int 0x777d : mword 16)
    (mword_of_int (FR + 0x14) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 14), LUI)) fdc_777d exec_execute_C_LUI. Qed.

  Lemma fri_16 : kernel_text -∗ instr (mword_of_int (FR + 0x16) : mword 64) true (RTYPE (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 1)), AND)).
  Proof. mk_rvc (FR + 0x16)%Z (mword_of_int 0x8cf9 : mword 16)
    (mword_of_int (FR + 0x16) : mword 64) (RTYPE (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 1)), AND)) fdc_8cf9 exec_execute_C_AND. Qed.

  Lemma fri_18 : kernel_text -∗ instr (mword_of_int (FR + 0x18) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (FR + 0x18)%Z (mword_of_int 0x94be : mword 16)
    (mword_of_int (FR + 0x18) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)) fdc_94be exec_execute_C_ADD. Qed.

  Lemma fri_1a : kernel_text -∗ instr (mword_of_int (FR + 0x1a) : mword 64) false (BTYPE (mword_of_int 36 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 11), BLTU)).
  Proof. mk_base (FR + 0x1a)%Z (mword_of_int 0x0295e263 : mword 32)
    (mword_of_int (FR + 0x1a) : mword 64) (BTYPE (mword_of_int 36 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 11), BLTU)) fdb_0295e263. Qed.

  Lemma fri_1e : kernel_text -∗ instr (mword_of_int (FR + 0x1e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (FR + 0x1e)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (FR + 0x1e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) fdc_e84a exec_execute_C_SDSP. Qed.

  Lemma fri_20 : kernel_text -∗ instr (mword_of_int (FR + 0x20) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (FR + 0x20)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (FR + 0x20) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) fdc_e44e exec_execute_C_SDSP. Qed.

  Lemma fri_22 : kernel_text -∗ instr (mword_of_int (FR + 0x22) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (FR + 0x22)%Z (mword_of_int 0xe052 : mword 16)
    (mword_of_int (FR + 0x22) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) fdc_e052 exec_execute_C_SDSP. Qed.

  Lemma fri_24 : kernel_text -∗ instr (mword_of_int (FR + 0x24) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (FR + 0x24)%Z (mword_of_int 0x892e : mword 16)
    (mword_of_int (FR + 0x24) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)) fdc_892e exec_execute_C_MV. Qed.

  Lemma fri_26 : kernel_text -∗ instr (mword_of_int (FR + 0x26) : mword 64) true (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (FR + 0x26)%Z (mword_of_int 0x8a3a : mword 16)
    (mword_of_int (FR + 0x26) : mword 64) (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 20), ADD)) fdc_8a3a exec_execute_C_MV. Qed.

  Lemma fri_28 : kernel_text -∗ instr (mword_of_int (FR + 0x28) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (FR + 0x28)%Z (mword_of_int 0x89be : mword 16)
    (mword_of_int (FR + 0x28) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 19), ADD)) fdc_89be exec_execute_C_MV. Qed.

  Lemma fri_2a : kernel_text -∗ instr (mword_of_int (FR + 0x2a) : mword 64) false (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADD)).
  Proof. mk_base (FR + 0x2a)%Z (mword_of_int 0x01448533 : mword 32)
    (mword_of_int (FR + 0x2a) : mword 64) (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADD)) fdb_01448533. Qed.

  Lemma fri_2e : kernel_text -∗ instr (mword_of_int (FR + 0x2e) : mword 64) false (JAL (mword_of_int 2096998 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FR + 0x2e)%Z (mword_of_int 0xf67ff0ef : mword 32)
    (mword_of_int (FR + 0x2e) : mword 64) (JAL (mword_of_int 2096998 : mword 21, Regidx (mword_of_int 1))) fdb_f67ff0ef. Qed.

  Lemma fri_32 : kernel_text -∗ instr (mword_of_int (FR + 0x32) : mword 64) true (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (FR + 0x32)%Z (mword_of_int 0x94ce : mword 16)
    (mword_of_int (FR + 0x32) : mword 64) (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)) fdc_94ce exec_execute_C_ADD. Qed.

  Lemma fri_34 : kernel_text -∗ instr (mword_of_int (FR + 0x34) : mword 64) false (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 18), BGEU)).
  Proof. mk_base (FR + 0x34)%Z (mword_of_int 0xfe997be3 : mword 32)
    (mword_of_int (FR + 0x34) : mword 64) (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 18), BGEU)) fdb_fe997be3. Qed.

  Lemma fri_38 : kernel_text -∗ instr (mword_of_int (FR + 0x38) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (FR + 0x38)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (FR + 0x38) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) fdc_6942 exec_execute_C_LDSP. Qed.

  Lemma fri_3a : kernel_text -∗ instr (mword_of_int (FR + 0x3a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (FR + 0x3a)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (FR + 0x3a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) fdc_69a2 exec_execute_C_LDSP. Qed.

  Lemma fri_3c : kernel_text -∗ instr (mword_of_int (FR + 0x3c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (FR + 0x3c)%Z (mword_of_int 0x6a02 : mword 16)
    (mword_of_int (FR + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) fdc_6a02 exec_execute_C_LDSP. Qed.

  Lemma fri_3e : kernel_text -∗ instr (mword_of_int (FR + 0x3e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (FR + 0x3e)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (FR + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) fdc_70a2 exec_execute_C_LDSP. Qed.

  Lemma fri_40 : kernel_text -∗ instr (mword_of_int (FR + 0x40) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (FR + 0x40)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (FR + 0x40) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) fdc_7402 exec_execute_C_LDSP. Qed.

  Lemma fri_42 : kernel_text -∗ instr (mword_of_int (FR + 0x42) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (FR + 0x42)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (FR + 0x42) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) fdc_64e2 exec_execute_C_LDSP. Qed.

  Lemma fri_44 : kernel_text -∗ instr (mword_of_int (FR + 0x44) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (FR + 0x44)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (FR + 0x44) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) fdc_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma fri_46 : kernel_text -∗ instr (mword_of_int (FR + 0x46) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (FR + 0x46)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (FR + 0x46) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) fdc_8082 exec_execute_C_JR. Qed.

End WpFreerangeDecode.
