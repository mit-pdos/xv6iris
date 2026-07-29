(* WpConsputcDecode.v -- the instruction-DECODE layer for xv6's consputc().
   For every instruction of

     consputc @ 0x8000027c .. 0x800002ac   (offsets 0x00 .. 0x30)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([cpi_<off>]) plus
   the per-instruction decode facts they consume ([cpdc_<word>] compressed /
   [cpdb_<word>] base).

   consputc uses the standard 16-byte / 2-slot frame, so every frame word is one
   of the shared [cdec_*] templates in KernelRvcDecode.v; the four
   uartputc_sync call sites, the BACKSPACE test and the three character
   materializations carry consputc's own encodings and are proved here. *)
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
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts unique to consputc.                            *)
(* ===================================================================== *)

(* 0x4521  c.li a0,8   (the '\b' the two backspace calls pass) *)
Lemma cpdc_4521 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4521 : mword 16)) s
  = Some (C_LI (mword_of_int 8, Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb7d5  c.j -28  (backspace arm -> the shared epilogue) *)
(* [cdec_b7d5] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* ===================================================================== *)
(* Base (32-bit) decode facts unique to consputc.                         *)
(* ===================================================================== *)

(* li a5,256 -- BACKSPACE *)
Lemma cpdb_10000793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10000793 : mword 32)) s
  = Some (ITYPE (mword_of_int 256 : mword 12, zreg, Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* beq a0,a5,+16 -- the BACKSPACE test *)
Lemma cpdb_00f50863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f50863 : mword 32)) s
  = Some (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 10), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* li a0,32 -- the ' ' the middle backspace call passes *)
Lemma cpdb_02000513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02000513 : mword 32)) s
  = Some (ITYPE (mword_of_int 32 : mword 12, zreg, Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* the four `jal ra,uartputc_sync` -- one displacement each *)
Lemma cpdb_6e4000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6e4000ef : mword 32)) s
  = Some (JAL (mword_of_int 1764 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma cpdb_6d6000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6d6000ef : mword 32)) s
  = Some (JAL (mword_of_int 1750 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma cpdb_6ce000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6ce000ef : mword 32)) s
  = Some (JAL (mword_of_int 1742 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma cpdb_6c8000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6c8000ef : mword 32)) s
  = Some (JAL (mword_of_int 1736 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Section WpConsputcDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation CP := KernelSyms.consputc.

  (* ---- prologue: 2-slot frame push, save ra/s0, set up s0 ---- *)

  Lemma cpi_00 : kernel_text -∗ instr (mword_of_int CP : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc CP (mword_of_int 0x1141 : mword 16)
    (mword_of_int CP : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma cpi_02 : kernel_text -∗ instr (mword_of_int (CP + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (CP + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (CP + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma cpi_04 : kernel_text -∗ instr (mword_of_int (CP + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (CP + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (CP + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma cpi_06 : kernel_text -∗ instr (mword_of_int (CP + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (CP + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (CP + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  (* ---- if (c == BACKSPACE) ---- *)

  Lemma cpi_08 : kernel_text -∗ instr (mword_of_int (CP + 0x08) : mword 64) false (ITYPE (mword_of_int 256 : mword 12, zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (CP + 0x08)%Z (mword_of_int 0x10000793 : mword 32)
    (mword_of_int (CP + 0x08) : mword 64) (ITYPE (mword_of_int 256 : mword 12, zreg, Regidx (mword_of_int 15), ADDI)) cpdb_10000793. Qed.

  Lemma cpi_0c : kernel_text -∗ instr (mword_of_int (CP + 0x0c) : mword 64) false (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 10), BEQ)).
  Proof. mk_base (CP + 0x0c)%Z (mword_of_int 0x00f50863 : mword 32)
    (mword_of_int (CP + 0x0c) : mword 64) (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 10), BEQ)) cpdb_00f50863. Qed.

  (* ---- the ordinary arm: uartputc_sync(c) ---- *)

  Lemma cpi_10 : kernel_text -∗ instr (mword_of_int (CP + 0x10) : mword 64) false (JAL (mword_of_int 1764 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (CP + 0x10)%Z (mword_of_int 0x6e4000ef : mword 32)
    (mword_of_int (CP + 0x10) : mword 64) (JAL (mword_of_int 1764 : mword 21, Regidx (mword_of_int 1))) cpdb_6e4000ef. Qed.

  (* ---- the shared epilogue ---- *)

  Lemma cpi_14 : kernel_text -∗ instr (mword_of_int (CP + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (CP + 0x14)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (CP + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma cpi_16 : kernel_text -∗ instr (mword_of_int (CP + 0x16) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (CP + 0x16)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (CP + 0x16) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma cpi_18 : kernel_text -∗ instr (mword_of_int (CP + 0x18) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (CP + 0x18)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (CP + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma cpi_1a : kernel_text -∗ instr (mword_of_int (CP + 0x1a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (CP + 0x1a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (CP + 0x1a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* ---- the BACKSPACE arm: '\b', ' ', '\b' ---- *)

  Lemma cpi_1c : kernel_text -∗ instr (mword_of_int (CP + 0x1c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (CP + 0x1c)%Z (mword_of_int 0x4521 : mword 16)
    (mword_of_int (CP + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cpdc_4521 exec_execute_C_LI. Qed.

  Lemma cpi_1e : kernel_text -∗ instr (mword_of_int (CP + 0x1e) : mword 64) false (JAL (mword_of_int 1750 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (CP + 0x1e)%Z (mword_of_int 0x6d6000ef : mword 32)
    (mword_of_int (CP + 0x1e) : mword 64) (JAL (mword_of_int 1750 : mword 21, Regidx (mword_of_int 1))) cpdb_6d6000ef. Qed.

  Lemma cpi_22 : kernel_text -∗ instr (mword_of_int (CP + 0x22) : mword 64) false (ITYPE (mword_of_int 32 : mword 12, zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (CP + 0x22)%Z (mword_of_int 0x02000513 : mword 32)
    (mword_of_int (CP + 0x22) : mword 64) (ITYPE (mword_of_int 32 : mword 12, zreg, Regidx (mword_of_int 10), ADDI)) cpdb_02000513. Qed.

  Lemma cpi_26 : kernel_text -∗ instr (mword_of_int (CP + 0x26) : mword 64) false (JAL (mword_of_int 1742 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (CP + 0x26)%Z (mword_of_int 0x6ce000ef : mword 32)
    (mword_of_int (CP + 0x26) : mword 64) (JAL (mword_of_int 1742 : mword 21, Regidx (mword_of_int 1))) cpdb_6ce000ef. Qed.

  Lemma cpi_2a : kernel_text -∗ instr (mword_of_int (CP + 0x2a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (CP + 0x2a)%Z (mword_of_int 0x4521 : mword 16)
    (mword_of_int (CP + 0x2a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cpdc_4521 exec_execute_C_LI. Qed.

  Lemma cpi_2c : kernel_text -∗ instr (mword_of_int (CP + 0x2c) : mword 64) false (JAL (mword_of_int 1736 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (CP + 0x2c)%Z (mword_of_int 0x6c8000ef : mword 32)
    (mword_of_int (CP + 0x2c) : mword 64) (JAL (mword_of_int 1736 : mword 21, Regidx (mword_of_int 1))) cpdb_6c8000ef. Qed.

  Lemma cpi_30 : kernel_text -∗ instr (mword_of_int (CP + 0x30) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (CP + 0x30)%Z (mword_of_int 0xb7d5 : mword 16)
    (mword_of_int (CP + 0x30) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")), zreg)) cdec_b7d5 exec_execute_C_J. Qed.

End WpConsputcDecode.
