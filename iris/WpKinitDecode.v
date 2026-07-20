(* WpKinitDecode.v -- the instruction-DECODE layer for xv6's kinit().
   For every instruction of

     kinit @ 0x80000afa .. 0x80000b2c   (offsets 0x00 .. 0x32)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([kii_<off>]).  The
   common compressed encodings (c.addi sp, c.sdsp/c.ldsp ra/s0, c.addi4spn, c.jr)
   reuse the shared [mdec_*] helpers from KernelRvcDecode; only c.li / c.slli and
   the eight base auipc/addi/jal words get fresh decode helpers here. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes WpDecodeBridge.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts unique to kinit (c.li a1,17 / c.slli a1,a1,27). *)
(* ===================================================================== *)
Lemma fdc_45c5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x45c5 : mword 16)) s
  = Some (C_LI (mword_of_int 17, Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_05ee s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x05ee : mword 16)) s
  = Some (C_SLLI (mword_of_int 27, Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (32-bit) decode facts.                                            *)
(* ===================================================================== *)
Lemma fdb_00006597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00006597 : mword 32)) s
  = Some (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_53e58593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x53e58593 : mword 32)) s
  = Some (ITYPE (mword_of_int 1342 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_00012517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00012517 : mword 32)) s
  = Some (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_81e50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x81e50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 2078 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_076000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x076000ef : mword 32)) s
  = Some (JAL (mword_of_int 118 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_00023517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00023517 : mword 32)) s
  = Some (UTYPE (mword_of_int 35 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_a3e50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa3e50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 2622 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma fdb_f91ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf91ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2097040 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Section WpKinitDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation KI := KernelSyms.kinit.

  Lemma kii_00 : kernel_text -∗ instr (mword_of_int (KI + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KI + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (KI + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  Lemma kii_02 : kernel_text -∗ instr (mword_of_int (KI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KI + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (KI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  Lemma kii_04 : kernel_text -∗ instr (mword_of_int (KI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KI + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (KI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  Lemma kii_06 : kernel_text -∗ instr (mword_of_int (KI + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KI + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (KI + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  Lemma kii_08 : kernel_text -∗ instr (mword_of_int (KI + 0x08) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (KI + 0x08)%Z (mword_of_int 0x00006597 : mword 32)
    (mword_of_int (KI + 0x08) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC)) fdb_00006597. Qed.

  Lemma kii_0c : kernel_text -∗ instr (mword_of_int (KI + 0x0c) : mword 64) false (ITYPE (mword_of_int 1342 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (KI + 0x0c)%Z (mword_of_int 0x53e58593 : mword 32)
    (mword_of_int (KI + 0x0c) : mword 64) (ITYPE (mword_of_int 1342 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) fdb_53e58593. Qed.

  Lemma kii_10 : kernel_text -∗ instr (mword_of_int (KI + 0x10) : mword 64) false (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KI + 0x10)%Z (mword_of_int 0x00012517 : mword 32)
    (mword_of_int (KI + 0x10) : mword 64) (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)) fdb_00012517. Qed.

  Lemma kii_14 : kernel_text -∗ instr (mword_of_int (KI + 0x14) : mword 64) false (ITYPE (mword_of_int 2078 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KI + 0x14)%Z (mword_of_int 0x81e50513 : mword 32)
    (mword_of_int (KI + 0x14) : mword 64) (ITYPE (mword_of_int 2078 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) fdb_81e50513. Qed.

  Lemma kii_18 : kernel_text -∗ instr (mword_of_int (KI + 0x18) : mword 64) false (JAL (mword_of_int 118 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KI + 0x18)%Z (mword_of_int 0x076000ef : mword 32)
    (mword_of_int (KI + 0x18) : mword 64) (JAL (mword_of_int 118 : mword 21, Regidx (mword_of_int 1))) fdb_076000ef. Qed.

  Lemma kii_1c : kernel_text -∗ instr (mword_of_int (KI + 0x1c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 17 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (KI + 0x1c)%Z (mword_of_int 0x45c5 : mword 16)
    (mword_of_int (KI + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 17 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) fdc_45c5 exec_execute_C_LI. Qed.

  Lemma kii_1e : kernel_text -∗ instr (mword_of_int (KI + 0x1e) : mword 64) true (SHIFTIOP (mword_of_int 27 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)).
  Proof. mk_rvc (KI + 0x1e)%Z (mword_of_int 0x05ee : mword 16)
    (mword_of_int (KI + 0x1e) : mword 64) (SHIFTIOP (mword_of_int 27 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)) fdc_05ee exec_execute_C_SLLI. Qed.

  Lemma kii_20 : kernel_text -∗ instr (mword_of_int (KI + 0x20) : mword 64) false (UTYPE (mword_of_int 35 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KI + 0x20)%Z (mword_of_int 0x00023517 : mword 32)
    (mword_of_int (KI + 0x20) : mword 64) (UTYPE (mword_of_int 35 : mword 20, Regidx (mword_of_int 10), AUIPC)) fdb_00023517. Qed.

  Lemma kii_24 : kernel_text -∗ instr (mword_of_int (KI + 0x24) : mword 64) false (ITYPE (mword_of_int 2622 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KI + 0x24)%Z (mword_of_int 0xa3e50513 : mword 32)
    (mword_of_int (KI + 0x24) : mword 64) (ITYPE (mword_of_int 2622 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) fdb_a3e50513. Qed.

  Lemma kii_28 : kernel_text -∗ instr (mword_of_int (KI + 0x28) : mword 64) false (JAL (mword_of_int 2097040 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KI + 0x28)%Z (mword_of_int 0xf91ff0ef : mword 32)
    (mword_of_int (KI + 0x28) : mword 64) (JAL (mword_of_int 2097040 : mword 21, Regidx (mword_of_int 1))) fdb_f91ff0ef. Qed.

  Lemma kii_2c : kernel_text -∗ instr (mword_of_int (KI + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KI + 0x2c)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (KI + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  Lemma kii_2e : kernel_text -∗ instr (mword_of_int (KI + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KI + 0x2e)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (KI + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  Lemma kii_30 : kernel_text -∗ instr (mword_of_int (KI + 0x30) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KI + 0x30)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (KI + 0x30) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  Lemma kii_32 : kernel_text -∗ instr (mword_of_int (KI + 0x32) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KI + 0x32)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KI + 0x32) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

End WpKinitDecode.
