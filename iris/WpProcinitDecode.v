(* WpProcinitDecode.v -- the instruction-DECODE layer for xv6's procinit().

     procinit @ 0x8000181a .. 0x800018ce   (offsets 0x00 .. 0xb4)

   Two initlock calls for pid_lock / wait_lock, then a do-while over the 64
   [struct proc]s: initlock(&p->lock,"proc"); p->state = UNUSED;
   p->kstack = KSTACK(i).

   Most of the words are already shared.  The standard 64-byte frame
   (7139 / fc06.. / 0080 / 70e2.. / 6121 / 8082) and the KSTACK sequence
   procinit shares with proc_mapstacks (000a57b7, fa578793, 07b2, 4fa50937,
   a4f90913, 1902, 993e, 040009b7, 19fd, 09b2, 16848493) come from
   KernelRvcDecode / KernelBaseDecode; only procinit's own words are here.

   What the KSTACK sequence COMPUTES is KstackArith.v, not this file: gcc
   divides [p - proc] by 360 with a multiply by the modular inverse of 45. *)
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
Require Import ExecCommon.
Require Import WpRvcBridge.
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode facts for procinit's own words.                                 *)
(* ===================================================================== *)

Lemma pidc_8aa6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8aa6 : mword 16)) s = Some (C_MV (Regidx (mword_of_int 21), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma pidc_85da s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x85da : mword 16)) s = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma pidc_878d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x878d : mword 16)) s = Some (C_SRAI (mword_of_int 3, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma pidc_07b6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x07b6 : mword 16)) s = Some (C_SLLI (mword_of_int 13, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma pidc_6709 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6709 : mword 16)) s = Some (C_LUI (mword_of_int 2, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma pidc_9fb9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9fb9 : mword 16)) s = Some (C_ADDW (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma pidc_e0bc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe0bc : mword 16)) s = Some (C_SD (mword_of_int 8, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma pidb_93258593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x93258593 : mword 32)) s = Some (ITYPE (mword_of_int 0x932 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_00011517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00011517 : mword 32)) s = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_b1250513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb1250513 : mword 32)) s = Some (ITYPE (mword_of_int 0xb12 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_b4aff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb4aff0ef : mword 32)) s = Some (JAL (mword_of_int 0x1ff34a : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_92658593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x92658593 : mword 32)) s = Some (ITYPE (mword_of_int 0x926 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_b1650513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb1650513 : mword 32)) s = Some (ITYPE (mword_of_int 0xb16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_b36ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb36ff0ef : mword 32)) s = Some (JAL (mword_of_int 0x1ff336 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_00011497 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00011497 : mword 32)) s = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_f2248493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf2248493 : mword 32)) s = Some (ITYPE (mword_of_int 0xf22 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_00006b17 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00006b17 : mword 32)) s = Some (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 22), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_91ab0b13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x91ab0b13 : mword 32)) s = Some (ITYPE (mword_of_int 0x91a : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 22), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_00017a17 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00017a17 : mword 32)) s = Some (UTYPE (mword_of_int 0x17 : mword 20, Regidx (mword_of_int 20), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_8eea0a13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8eea0a13 : mword 32)) s = Some (ITYPE (mword_of_int 0x8ee : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_af2ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xaf2ff0ef : mword 32)) s = Some (JAL (mword_of_int 0x1ff2f2 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_0004ac23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004ac23 : mword 32)) s = Some (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_415487b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x415487b3 : mword 32)) s = Some (RTYPE (Regidx (mword_of_int 21), Regidx (mword_of_int 9), Regidx (mword_of_int 15), SUB), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_032787b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x032787b3 : mword 32)) s = Some (MUL (Regidx (mword_of_int 18), Regidx (mword_of_int 15), Regidx (mword_of_int 15), mulop_mul), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_40f987b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40f987b3 : mword 32)) s = Some (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 19), Regidx (mword_of_int 15), SUB), s).
Proof. decode_bridge_ms. Qed.

Lemma pidb_fd449de3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd449de3 : mword 32)) s = Some (BTYPE (mword_of_int 8154 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 9), BNE), s).
Proof. decode_bridge_ms. Qed.

(* the [sd a5,64(s1)] expansion in leaf form: one instance of
   WpMmodeLeafBase's [exec_execute_C_SD_leaf] at offset 64 / s1 / a5. *)
Lemma pidexec_e0bc s :
  exec (execute (C_SD (mword_of_int 8, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section ProcinitInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation PI := KernelSyms.procinit.

  Lemma pii_00 : kernel_text -∗ instr (mword_of_int (PI + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PI + 0x00)%Z (mword_of_int 0x7139 : mword 16)
    (mword_of_int (PI + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)) cdec_7139 exec_execute_C_ADDI16SP. Qed.

  Lemma pii_02 : kernel_text -∗ instr (mword_of_int (PI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PI + 0x02)%Z (mword_of_int 0xfc06 : mword 16)
    (mword_of_int (PI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_fc06 exec_execute_C_SDSP. Qed.

  Lemma pii_04 : kernel_text -∗ instr (mword_of_int (PI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PI + 0x04)%Z (mword_of_int 0xf822 : mword 16)
    (mword_of_int (PI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f822 exec_execute_C_SDSP. Qed.

  Lemma pii_06 : kernel_text -∗ instr (mword_of_int (PI + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (PI + 0x06)%Z (mword_of_int 0xf426 : mword 16)
    (mword_of_int (PI + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_f426 exec_execute_C_SDSP. Qed.

  Lemma pii_08 : kernel_text -∗ instr (mword_of_int (PI + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (PI + 0x08)%Z (mword_of_int 0xf04a : mword 16)
    (mword_of_int (PI + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f04a exec_execute_C_SDSP. Qed.

  Lemma pii_0a : kernel_text -∗ instr (mword_of_int (PI + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (PI + 0x0a)%Z (mword_of_int 0xec4e : mword 16)
    (mword_of_int (PI + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_ec4e exec_execute_C_SDSP. Qed.

  Lemma pii_0c : kernel_text -∗ instr (mword_of_int (PI + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (PI + 0x0c)%Z (mword_of_int 0xe852 : mword 16)
    (mword_of_int (PI + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e852 exec_execute_C_SDSP. Qed.

  Lemma pii_0e : kernel_text -∗ instr (mword_of_int (PI + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (PI + 0x0e)%Z (mword_of_int 0xe456 : mword 16)
    (mword_of_int (PI + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_e456 exec_execute_C_SDSP. Qed.

  Lemma pii_10 : kernel_text -∗ instr (mword_of_int (PI + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (PI + 0x10)%Z (mword_of_int 0xe05a : mword 16)
    (mword_of_int (PI + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_e05a exec_execute_C_SDSP. Qed.

  Lemma pii_12 : kernel_text -∗ instr (mword_of_int (PI + 0x12) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PI + 0x12)%Z (mword_of_int 0x0080 : mword 16)
    (mword_of_int (PI + 0x12) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0080 exec_execute_C_ADDI4SPN. Qed.

  Lemma pii_14 : kernel_text -∗ instr (mword_of_int (PI + 0x14) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (PI + 0x14)%Z (mword_of_int 0x00006597 : mword 32)
    (mword_of_int (PI + 0x14) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC)) bdec_00006597. Qed.

  Lemma pii_18 : kernel_text -∗ instr (mword_of_int (PI + 0x18) : mword 64) false (ITYPE (mword_of_int 0x932 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (PI + 0x18)%Z (mword_of_int 0x93258593 : mword 32)
    (mword_of_int (PI + 0x18) : mword 64) (ITYPE (mword_of_int 0x932 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) pidb_93258593. Qed.

  Lemma pii_1c : kernel_text -∗ instr (mword_of_int (PI + 0x1c) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (PI + 0x1c)%Z (mword_of_int 0x00011517 : mword 32)
    (mword_of_int (PI + 0x1c) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)) pidb_00011517. Qed.

  Lemma pii_20 : kernel_text -∗ instr (mword_of_int (PI + 0x20) : mword 64) false (ITYPE (mword_of_int 0xb12 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PI + 0x20)%Z (mword_of_int 0xb1250513 : mword 32)
    (mword_of_int (PI + 0x20) : mword 64) (ITYPE (mword_of_int 0xb12 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) pidb_b1250513. Qed.

  Lemma pii_24 : kernel_text -∗ instr (mword_of_int (PI + 0x24) : mword 64) false (JAL (mword_of_int 0x1ff34a : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PI + 0x24)%Z (mword_of_int 0xb4aff0ef : mword 32)
    (mword_of_int (PI + 0x24) : mword 64) (JAL (mword_of_int 0x1ff34a : mword 21, Regidx (mword_of_int 1))) pidb_b4aff0ef. Qed.

  Lemma pii_28 : kernel_text -∗ instr (mword_of_int (PI + 0x28) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (PI + 0x28)%Z (mword_of_int 0x00006597 : mword 32)
    (mword_of_int (PI + 0x28) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC)) bdec_00006597. Qed.

  Lemma pii_2c : kernel_text -∗ instr (mword_of_int (PI + 0x2c) : mword 64) false (ITYPE (mword_of_int 0x926 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (PI + 0x2c)%Z (mword_of_int 0x92658593 : mword 32)
    (mword_of_int (PI + 0x2c) : mword 64) (ITYPE (mword_of_int 0x926 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) pidb_92658593. Qed.

  Lemma pii_30 : kernel_text -∗ instr (mword_of_int (PI + 0x30) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (PI + 0x30)%Z (mword_of_int 0x00011517 : mword 32)
    (mword_of_int (PI + 0x30) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)) pidb_00011517. Qed.

  Lemma pii_34 : kernel_text -∗ instr (mword_of_int (PI + 0x34) : mword 64) false (ITYPE (mword_of_int 0xb16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PI + 0x34)%Z (mword_of_int 0xb1650513 : mword 32)
    (mword_of_int (PI + 0x34) : mword 64) (ITYPE (mword_of_int 0xb16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) pidb_b1650513. Qed.

  Lemma pii_38 : kernel_text -∗ instr (mword_of_int (PI + 0x38) : mword 64) false (JAL (mword_of_int 0x1ff336 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PI + 0x38)%Z (mword_of_int 0xb36ff0ef : mword 32)
    (mword_of_int (PI + 0x38) : mword 64) (JAL (mword_of_int 0x1ff336 : mword 21, Regidx (mword_of_int 1))) pidb_b36ff0ef. Qed.

  Lemma pii_3c : kernel_text -∗ instr (mword_of_int (PI + 0x3c) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (PI + 0x3c)%Z (mword_of_int 0x00011497 : mword 32)
    (mword_of_int (PI + 0x3c) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC)) pidb_00011497. Qed.

  Lemma pii_40 : kernel_text -∗ instr (mword_of_int (PI + 0x40) : mword 64) false (ITYPE (mword_of_int 0xf22 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (PI + 0x40)%Z (mword_of_int 0xf2248493 : mword 32)
    (mword_of_int (PI + 0x40) : mword 64) (ITYPE (mword_of_int 0xf22 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) pidb_f2248493. Qed.

  Lemma pii_44 : kernel_text -∗ instr (mword_of_int (PI + 0x44) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 22), AUIPC)).
  Proof. mk_base (PI + 0x44)%Z (mword_of_int 0x00006b17 : mword 32)
    (mword_of_int (PI + 0x44) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 22), AUIPC)) pidb_00006b17. Qed.

  Lemma pii_48 : kernel_text -∗ instr (mword_of_int (PI + 0x48) : mword 64) false (ITYPE (mword_of_int 0x91a : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 22), ADDI)).
  Proof. mk_base (PI + 0x48)%Z (mword_of_int 0x91ab0b13 : mword 32)
    (mword_of_int (PI + 0x48) : mword 64) (ITYPE (mword_of_int 0x91a : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 22), ADDI)) pidb_91ab0b13. Qed.

  Lemma pii_4c : kernel_text -∗ instr (mword_of_int (PI + 0x4c) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 21), ADD)).
  Proof. mk_rvc (PI + 0x4c)%Z (mword_of_int 0x8aa6 : mword 16)
    (mword_of_int (PI + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 21), ADD)) pidc_8aa6 exec_execute_C_MV. Qed.

  Lemma pii_4e : kernel_text -∗ instr (mword_of_int (PI + 0x4e) : mword 64) false (UTYPE (mword_of_int 165 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (PI + 0x4e)%Z (mword_of_int 0x000a57b7 : mword 32)
    (mword_of_int (PI + 0x4e) : mword 64) (UTYPE (mword_of_int 165 : mword 20, Regidx (mword_of_int 15), LUI)) bdec_000a57b7. Qed.

  Lemma pii_52 : kernel_text -∗ instr (mword_of_int (PI + 0x52) : mword 64) false (ITYPE (mword_of_int 0xfa5 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (PI + 0x52)%Z (mword_of_int 0xfa578793 : mword 32)
    (mword_of_int (PI + 0x52) : mword 64) (ITYPE (mword_of_int 0xfa5 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bdec_fa578793. Qed.

  Lemma pii_56 : kernel_text -∗ instr (mword_of_int (PI + 0x56) : mword 64) true (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (PI + 0x56)%Z (mword_of_int 0x07b2 : mword 16)
    (mword_of_int (PI + 0x56) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_07b2 exec_execute_C_SLLI. Qed.

  Lemma pii_58 : kernel_text -∗ instr (mword_of_int (PI + 0x58) : mword 64) false (ITYPE (mword_of_int 0xfa5 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (PI + 0x58)%Z (mword_of_int 0xfa578793 : mword 32)
    (mword_of_int (PI + 0x58) : mword 64) (ITYPE (mword_of_int 0xfa5 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bdec_fa578793. Qed.

  Lemma pii_5c : kernel_text -∗ instr (mword_of_int (PI + 0x5c) : mword 64) false (UTYPE (mword_of_int 0x4fa50 : mword 20, Regidx (mword_of_int 18), LUI)).
  Proof. mk_base (PI + 0x5c)%Z (mword_of_int 0x4fa50937 : mword 32)
    (mword_of_int (PI + 0x5c) : mword 64) (UTYPE (mword_of_int 0x4fa50 : mword 20, Regidx (mword_of_int 18), LUI)) bdec_4fa50937. Qed.

  Lemma pii_60 : kernel_text -∗ instr (mword_of_int (PI + 0x60) : mword 64) false (ITYPE (mword_of_int 0xa4f : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (PI + 0x60)%Z (mword_of_int 0xa4f90913 : mword 32)
    (mword_of_int (PI + 0x60) : mword 64) (ITYPE (mword_of_int 0xa4f : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) bdec_a4f90913. Qed.

  Lemma pii_64 : kernel_text -∗ instr (mword_of_int (PI + 0x64) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 18), Regidx (mword_of_int 18), SLLI)).
  Proof. mk_rvc (PI + 0x64)%Z (mword_of_int 0x1902 : mword 16)
    (mword_of_int (PI + 0x64) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 18), Regidx (mword_of_int 18), SLLI)) cdec_1902 exec_execute_C_SLLI. Qed.

  Lemma pii_66 : kernel_text -∗ instr (mword_of_int (PI + 0x66) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (PI + 0x66)%Z (mword_of_int 0x993e : mword 16)
    (mword_of_int (PI + 0x66) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)) cdec_993e exec_execute_C_ADD. Qed.

  Lemma pii_68 : kernel_text -∗ instr (mword_of_int (PI + 0x68) : mword 64) false (UTYPE (mword_of_int 0x4000 : mword 20, Regidx (mword_of_int 19), LUI)).
  Proof. mk_base (PI + 0x68)%Z (mword_of_int 0x040009b7 : mword 32)
    (mword_of_int (PI + 0x68) : mword 64) (UTYPE (mword_of_int 0x4000 : mword 20, Regidx (mword_of_int 19), LUI)) bdec_040009b7. Qed.

  Lemma pii_6c : kernel_text -∗ instr (mword_of_int (PI + 0x6c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc (PI + 0x6c)%Z (mword_of_int 0x19fd : mword 16)
    (mword_of_int (PI + 0x6c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)) cdec_19fd exec_execute_C_ADDI. Qed.

  Lemma pii_6e : kernel_text -∗ instr (mword_of_int (PI + 0x6e) : mword 64) true (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 19), SLLI)).
  Proof. mk_rvc (PI + 0x6e)%Z (mword_of_int 0x09b2 : mword 16)
    (mword_of_int (PI + 0x6e) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 19), SLLI)) cdec_09b2 exec_execute_C_SLLI. Qed.

  Lemma pii_70 : kernel_text -∗ instr (mword_of_int (PI + 0x70) : mword 64) false (UTYPE (mword_of_int 0x17 : mword 20, Regidx (mword_of_int 20), AUIPC)).
  Proof. mk_base (PI + 0x70)%Z (mword_of_int 0x00017a17 : mword 32)
    (mword_of_int (PI + 0x70) : mword 64) (UTYPE (mword_of_int 0x17 : mword 20, Regidx (mword_of_int 20), AUIPC)) pidb_00017a17. Qed.

  Lemma pii_74 : kernel_text -∗ instr (mword_of_int (PI + 0x74) : mword 64) false (ITYPE (mword_of_int 0x8ee : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)).
  Proof. mk_base (PI + 0x74)%Z (mword_of_int 0x8eea0a13 : mword 32)
    (mword_of_int (PI + 0x74) : mword 64) (ITYPE (mword_of_int 0x8ee : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)) pidb_8eea0a13. Qed.

  Lemma pii_78 : kernel_text -∗ instr (mword_of_int (PI + 0x78) : mword 64) true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (PI + 0x78)%Z (mword_of_int 0x85da : mword 16)
    (mword_of_int (PI + 0x78) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)) pidc_85da exec_execute_C_MV. Qed.

  Lemma pii_7a : kernel_text -∗ instr (mword_of_int (PI + 0x7a) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PI + 0x7a)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (PI + 0x7a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma pii_7c : kernel_text -∗ instr (mword_of_int (PI + 0x7c) : mword 64) false (JAL (mword_of_int 0x1ff2f2 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PI + 0x7c)%Z (mword_of_int 0xaf2ff0ef : mword 32)
    (mword_of_int (PI + 0x7c) : mword 64) (JAL (mword_of_int 0x1ff2f2 : mword 21, Regidx (mword_of_int 1))) pidb_af2ff0ef. Qed.

  Lemma pii_80 : kernel_text -∗ instr (mword_of_int (PI + 0x80) : mword 64) false (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (PI + 0x80)%Z (mword_of_int 0x0004ac23 : mword 32)
    (mword_of_int (PI + 0x80) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)) pidb_0004ac23. Qed.

  Lemma pii_84 : kernel_text -∗ instr (mword_of_int (PI + 0x84) : mword 64) false (RTYPE (Regidx (mword_of_int 21), Regidx (mword_of_int 9), Regidx (mword_of_int 15), SUB)).
  Proof. mk_base (PI + 0x84)%Z (mword_of_int 0x415487b3 : mword 32)
    (mword_of_int (PI + 0x84) : mword 64) (RTYPE (Regidx (mword_of_int 21), Regidx (mword_of_int 9), Regidx (mword_of_int 15), SUB)) pidb_415487b3. Qed.

  Lemma pii_88 : kernel_text -∗ instr (mword_of_int (PI + 0x88) : mword 64) true (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SRAI)).
  Proof. mk_rvc (PI + 0x88)%Z (mword_of_int 0x878d : mword 16)
    (mword_of_int (PI + 0x88) : mword 64) (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SRAI)) pidc_878d exec_execute_C_SRAI. Qed.

  Lemma pii_8a : kernel_text -∗ instr (mword_of_int (PI + 0x8a) : mword 64) false (MUL (Regidx (mword_of_int 18), Regidx (mword_of_int 15), Regidx (mword_of_int 15), mulop_mul)).
  Proof. mk_base (PI + 0x8a)%Z (mword_of_int 0x032787b3 : mword 32)
    (mword_of_int (PI + 0x8a) : mword 64) (MUL (Regidx (mword_of_int 18), Regidx (mword_of_int 15), Regidx (mword_of_int 15), mulop_mul)) pidb_032787b3. Qed.

  Lemma pii_8e : kernel_text -∗ instr (mword_of_int (PI + 0x8e) : mword 64) true (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (PI + 0x8e)%Z (mword_of_int 0x07b6 : mword 16)
    (mword_of_int (PI + 0x8e) : mword 64) (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) pidc_07b6 exec_execute_C_SLLI. Qed.

  Lemma pii_90 : kernel_text -∗ instr (mword_of_int (PI + 0x90) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 2 : mword 6), Regidx (mword_of_int 14), LUI)).
  Proof. mk_rvc (PI + 0x90)%Z (mword_of_int 0x6709 : mword 16)
    (mword_of_int (PI + 0x90) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 2 : mword 6), Regidx (mword_of_int 14), LUI)) pidc_6709 exec_execute_C_LUI. Qed.

  Lemma pii_92 : kernel_text -∗ instr (mword_of_int (PI + 0x92) : mword 64) true (RTYPEW (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDW)).
  Proof. mk_rvc (PI + 0x92)%Z (mword_of_int 0x9fb9 : mword 16)
    (mword_of_int (PI + 0x92) : mword 64) (RTYPEW (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDW)) pidc_9fb9 exec_execute_C_ADDW. Qed.

  Lemma pii_94 : kernel_text -∗ instr (mword_of_int (PI + 0x94) : mword 64) false (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 19), Regidx (mword_of_int 15), SUB)).
  Proof. mk_base (PI + 0x94)%Z (mword_of_int 0x40f987b3 : mword 32)
    (mword_of_int (PI + 0x94) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 19), Regidx (mword_of_int 15), SUB)) pidb_40f987b3. Qed.

  Lemma pii_98 : kernel_text -∗ instr (mword_of_int (PI + 0x98) : mword 64) true (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (PI + 0x98)%Z (mword_of_int 0xe0bc : mword 16)
    (mword_of_int (PI + 0x98) : mword 64) (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)) pidc_e0bc pidexec_e0bc. Qed.

  Lemma pii_9a : kernel_text -∗ instr (mword_of_int (PI + 0x9a) : mword 64) false (ITYPE (mword_of_int 0x168 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (PI + 0x9a)%Z (mword_of_int 0x16848493 : mword 32)
    (mword_of_int (PI + 0x9a) : mword 64) (ITYPE (mword_of_int 0x168 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) bdec_16848493. Qed.

  Lemma pii_9e : kernel_text -∗ instr (mword_of_int (PI + 0x9e) : mword 64) false (BTYPE (mword_of_int 8154 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 9), BNE)).
  Proof. mk_base (PI + 0x9e)%Z (mword_of_int 0xfd449de3 : mword 32)
    (mword_of_int (PI + 0x9e) : mword 64) (BTYPE (mword_of_int 8154 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 9), BNE)) pidb_fd449de3. Qed.

  Lemma pii_a2 : kernel_text -∗ instr (mword_of_int (PI + 0xa2) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PI + 0xa2)%Z (mword_of_int 0x70e2 : mword 16)
    (mword_of_int (PI + 0xa2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70e2 exec_execute_C_LDSP. Qed.

  Lemma pii_a4 : kernel_text -∗ instr (mword_of_int (PI + 0xa4) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PI + 0xa4)%Z (mword_of_int 0x7442 : mword 16)
    (mword_of_int (PI + 0xa4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7442 exec_execute_C_LDSP. Qed.

  Lemma pii_a6 : kernel_text -∗ instr (mword_of_int (PI + 0xa6) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (PI + 0xa6)%Z (mword_of_int 0x74a2 : mword 16)
    (mword_of_int (PI + 0xa6) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74a2 exec_execute_C_LDSP. Qed.

  Lemma pii_a8 : kernel_text -∗ instr (mword_of_int (PI + 0xa8) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (PI + 0xa8)%Z (mword_of_int 0x7902 : mword 16)
    (mword_of_int (PI + 0xa8) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_7902 exec_execute_C_LDSP. Qed.

  Lemma pii_aa : kernel_text -∗ instr (mword_of_int (PI + 0xaa) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (PI + 0xaa)%Z (mword_of_int 0x69e2 : mword 16)
    (mword_of_int (PI + 0xaa) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69e2 exec_execute_C_LDSP. Qed.

  Lemma pii_ac : kernel_text -∗ instr (mword_of_int (PI + 0xac) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (PI + 0xac)%Z (mword_of_int 0x6a42 : mword 16)
    (mword_of_int (PI + 0xac) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a42 exec_execute_C_LDSP. Qed.

  Lemma pii_ae : kernel_text -∗ instr (mword_of_int (PI + 0xae) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (PI + 0xae)%Z (mword_of_int 0x6aa2 : mword 16)
    (mword_of_int (PI + 0xae) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_6aa2 exec_execute_C_LDSP. Qed.

  Lemma pii_b0 : kernel_text -∗ instr (mword_of_int (PI + 0xb0) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (PI + 0xb0)%Z (mword_of_int 0x6b02 : mword 16)
    (mword_of_int (PI + 0xb0) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_6b02 exec_execute_C_LDSP. Qed.

  Lemma pii_b2 : kernel_text -∗ instr (mword_of_int (PI + 0xb2) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PI + 0xb2)%Z (mword_of_int 0x6121 : mword 16)
    (mword_of_int (PI + 0xb2) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)) cdec_6121 exec_execute_C_ADDI16SP. Qed.

  Lemma pii_b4 : kernel_text -∗ instr (mword_of_int (PI + 0xb4) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PI + 0xb4)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PI + 0xb4) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End ProcinitInstrs.
