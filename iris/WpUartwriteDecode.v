(* WpUartwriteDecode.v -- the instruction-DECODE layer for xv6's uartwrite().
   For every instruction of

     uartwrite @ 0x800008dc .. 0x8000096e   (offsets 0x00 .. 0x92)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([uwi_<off>]).

   uartwrite's 80-byte frame is BYTE-IDENTICAL to copyinstr's (same slots, same
   registers, same order: ra@72 s0@64 s1@56 s2@48 s3@40 s4@32 s5@24 s6@16
   s7@8), so the whole prologue/epilogue reuses KernelRvcDecode's shared
   [cdec_*] helpers; only the interior compressed words (the two c.mv pairs,
   c.add, c.li, the three jumps and the two c.bnez back edges) and the base
   words get fresh decode lemmas here.

   Note the shrink-wrapping: s2/s3/s4/s6/s7 are saved at +0x20..+0x28, AFTER
   the [blez] at +0x1c, and restored at +0x72..+0x7a -- so the n = 0 path
   never touches those five slots. *)
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
Require Import KernelRvcDecode KernelBaseDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts unique to uartwrite.                           *)
(* ===================================================================== *)

(* 0x8aaa  c.mv s5,a0 *)
Lemma uwdc_8aaa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8aaa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 21), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8a56  c.mv s4,s5 *)
Lemma uwdc_8a56 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8a56 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 20), Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x9aa6  c.add s5,s5,s1 *)
Lemma uwdc_9aa6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9aa6 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 21), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4b05  c.li s6,1 *)
Lemma uwdc_4b05 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4b05 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa005  c.j +32   (+0x4c -> the loop head at +0x6c) *)
Lemma uwdc_a005 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa005 : mword 16)) s
  = Some (C_J (mword_of_int 16 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x85ce  c.mv a1,s3 *)
Lemma uwdc_85ce s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x85ce : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xfbfd  c.bnez a5,-10  (+0x58 -> the sleep block at +0x4e) *)
Lemma uwdc_fbfd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfbfd : mword 16)) s
  = Some (C_BNEZ (mword_of_int 251, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf3e5  c.bnez a5,-32  (+0x6e -> the sleep block at +0x4e) *)
Lemma uwdc_f3e5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf3e5 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 240, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb7ed  c.j -22  (+0x70 -> the body at +0x5a) *)
Lemma uwdc_b7ed s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb7ed : mword 16)) s
  = Some (C_J (mword_of_int 2037), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0a05  c.addi s4,s4,1 *)
Lemma uwdc_0a05 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0a05 : mword 16)) s
  = Some (C_ADDI (mword_of_int 1, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (32-bit) decode facts.                                            *)
(* ===================================================================== *)

(* addi a0,a0,-1500  -> &tx_lock *)
Lemma uwdb_a2450513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa2450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xa24 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,acquire *)
Lemma uwdb_314000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x314000ef : mword 32)) s
  = Some (JAL (mword_of_int 788 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* blez s1,+0x60  =  bge x0,s1 *)
Lemma uwdb_06905063 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06905063 : mword 32)) s
  = Some (BTYPE (mword_of_int 96 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.

(* auipc s1,0xa / addi s1,s1,-1758  -> &tx_busy *)
Lemma uwdb_0000a497 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0000a497 : mword 32)) s
  = Some (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma uwdb_92248493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x92248493 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x922 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc s3,0x12 / addi s3,s3,-1538  -> &tx_lock (kept for the sleep calls) *)
Lemma uwdb_00012997 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00012997 : mword 32)) s
  = Some (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 19), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma uwdb_9fe98993 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9fe98993 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x9fe : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc s2,0xa / addi s2,s2,-1778  -> &tx_chan (the sleep channel) *)
Lemma uwdb_0000a917 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0000a917 : mword 32)) s
  = Some (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma uwdb_90e90913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x90e90913 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x90e : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* lui s7,0x10000  -> UART0 (the THR base, kept in a register across the loop) *)
Lemma uwdb_10000bb7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10000bb7 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 23), LUI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,sleep *)
Lemma uwdb_5d8010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5d8010ef : mword 32)) s
  = Some (JAL (mword_of_int 5592 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* lbu a5,0(s4)  -- the buffer read *)
Lemma uwdb_000a4783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000a4783 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* sb a5,0(s7)  -- the THR write *)
Lemma uwdb_00fb8023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00fb8023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 23), 1), s).
Proof. decode_bridge_ms. Qed.

(* sw s6,0(s1)  -- tx_busy = 1 *)
Lemma uwdb_0164a023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0164a023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 9), 4), s).
Proof. decode_bridge_ms. Qed.

(* beq s4,s5,+10  -- the loop-exit test *)
Lemma uwdb_015a0563 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x015a0563 : mword 32)) s
  = Some (BTYPE (mword_of_int 10 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 20), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,a0,-1608  -> &tx_lock (the release argument) *)
Lemma uwdb_9b850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9b850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x9b8 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,release *)
Lemma uwdb_330000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x330000ef : mword 32)) s
  = Some (JAL (mword_of_int 816 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Section WpUartwriteDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation UW := KernelSyms.uartwrite.

  (* --- prologue (+0x00 .. +0x0e) --- *)
  Lemma uwi_00 : kernel_text -∗ instr (mword_of_int (UW + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (UW + 0x00)%Z (mword_of_int 0x715d : mword 16)
    (mword_of_int (UW + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)) cdec_715d exec_execute_C_ADDI16SP. Qed.

  Lemma uwi_02 : kernel_text -∗ instr (mword_of_int (UW + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (UW + 0x02)%Z (mword_of_int 0xe486 : mword 16)
    (mword_of_int (UW + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e486 exec_execute_C_SDSP. Qed.

  Lemma uwi_04 : kernel_text -∗ instr (mword_of_int (UW + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (UW + 0x04)%Z (mword_of_int 0xe0a2 : mword 16)
    (mword_of_int (UW + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e0a2 exec_execute_C_SDSP. Qed.

  Lemma uwi_06 : kernel_text -∗ instr (mword_of_int (UW + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (UW + 0x06)%Z (mword_of_int 0xfc26 : mword 16)
    (mword_of_int (UW + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_fc26 exec_execute_C_SDSP. Qed.

  Lemma uwi_08 : kernel_text -∗ instr (mword_of_int (UW + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (UW + 0x08)%Z (mword_of_int 0xec56 : mword 16)
    (mword_of_int (UW + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_ec56 exec_execute_C_SDSP. Qed.

  Lemma uwi_0a : kernel_text -∗ instr (mword_of_int (UW + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (UW + 0x0a)%Z (mword_of_int 0x0880 : mword 16)
    (mword_of_int (UW + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0880 exec_execute_C_ADDI4SPN. Qed.

  Lemma uwi_0c : kernel_text -∗ instr (mword_of_int (UW + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 21), ADD)).
  Proof. mk_rvc (UW + 0x0c)%Z (mword_of_int 0x8aaa : mword 16)
    (mword_of_int (UW + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 21), ADD)) uwdc_8aaa exec_execute_C_MV. Qed.

  Lemma uwi_0e : kernel_text -∗ instr (mword_of_int (UW + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (UW + 0x0e)%Z (mword_of_int 0x84ae : mword 16)
    (mword_of_int (UW + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)) cdec_84ae exec_execute_C_MV. Qed.

  (* --- acquire(&tx_lock) and the n <= 0 guard (+0x10 .. +0x1c) --- *)
  Lemma uwi_10 : kernel_text -∗ instr (mword_of_int (UW + 0x10) : mword 64) false (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (UW + 0x10)%Z (mword_of_int 0x00012517 : mword 32)
    (mword_of_int (UW + 0x10) : mword 64) (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00012517. Qed.

  Lemma uwi_14 : kernel_text -∗ instr (mword_of_int (UW + 0x14) : mword 64) false (ITYPE (mword_of_int 0xa24 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (UW + 0x14)%Z (mword_of_int 0xa2450513 : mword 32)
    (mword_of_int (UW + 0x14) : mword 64) (ITYPE (mword_of_int 0xa24 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) uwdb_a2450513. Qed.

  Lemma uwi_18 : kernel_text -∗ instr (mword_of_int (UW + 0x18) : mword 64) false (JAL (mword_of_int 788 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UW + 0x18)%Z (mword_of_int 0x314000ef : mword 32)
    (mword_of_int (UW + 0x18) : mword 64) (JAL (mword_of_int 788 : mword 21, Regidx (mword_of_int 1))) uwdb_314000ef. Qed.

  Lemma uwi_1c : kernel_text -∗ instr (mword_of_int (UW + 0x1c) : mword 64) false (BTYPE (mword_of_int 96 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (UW + 0x1c)%Z (mword_of_int 0x06905063 : mword 32)
    (mword_of_int (UW + 0x1c) : mword 64) (BTYPE (mword_of_int 96 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 0), BGE)) uwdb_06905063. Qed.

  (* --- the shrink-wrapped saves (+0x20 .. +0x28) --- *)
  Lemma uwi_20 : kernel_text -∗ instr (mword_of_int (UW + 0x20) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (UW + 0x20)%Z (mword_of_int 0xf84a : mword 16)
    (mword_of_int (UW + 0x20) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f84a exec_execute_C_SDSP. Qed.

  Lemma uwi_22 : kernel_text -∗ instr (mword_of_int (UW + 0x22) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (UW + 0x22)%Z (mword_of_int 0xf44e : mword 16)
    (mword_of_int (UW + 0x22) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_f44e exec_execute_C_SDSP. Qed.

  Lemma uwi_24 : kernel_text -∗ instr (mword_of_int (UW + 0x24) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (UW + 0x24)%Z (mword_of_int 0xf052 : mword 16)
    (mword_of_int (UW + 0x24) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_f052 exec_execute_C_SDSP. Qed.

  Lemma uwi_26 : kernel_text -∗ instr (mword_of_int (UW + 0x26) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (UW + 0x26)%Z (mword_of_int 0xe85a : mword 16)
    (mword_of_int (UW + 0x26) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_e85a exec_execute_C_SDSP. Qed.

  Lemma uwi_28 : kernel_text -∗ instr (mword_of_int (UW + 0x28) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (UW + 0x28)%Z (mword_of_int 0xe45e : mword 16)
    (mword_of_int (UW + 0x28) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_e45e exec_execute_C_SDSP. Qed.

  (* --- the loop's register setup (+0x2a .. +0x4c) --- *)
  Lemma uwi_2a : kernel_text -∗ instr (mword_of_int (UW + 0x2a) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (UW + 0x2a)%Z (mword_of_int 0x8a56 : mword 16)
    (mword_of_int (UW + 0x2a) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 20), ADD)) uwdc_8a56 exec_execute_C_MV. Qed.

  Lemma uwi_2c : kernel_text -∗ instr (mword_of_int (UW + 0x2c) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADD)).
  Proof. mk_rvc (UW + 0x2c)%Z (mword_of_int 0x9aa6 : mword 16)
    (mword_of_int (UW + 0x2c) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADD)) uwdc_9aa6 exec_execute_C_ADD. Qed.

  Lemma uwi_2e : kernel_text -∗ instr (mword_of_int (UW + 0x2e) : mword 64) false (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (UW + 0x2e)%Z (mword_of_int 0x0000a497 : mword 32)
    (mword_of_int (UW + 0x2e) : mword 64) (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 9), AUIPC)) uwdb_0000a497. Qed.

  Lemma uwi_32 : kernel_text -∗ instr (mword_of_int (UW + 0x32) : mword 64) false (ITYPE (mword_of_int 0x922 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (UW + 0x32)%Z (mword_of_int 0x92248493 : mword 32)
    (mword_of_int (UW + 0x32) : mword 64) (ITYPE (mword_of_int 0x922 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) uwdb_92248493. Qed.

  Lemma uwi_36 : kernel_text -∗ instr (mword_of_int (UW + 0x36) : mword 64) false (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 19), AUIPC)).
  Proof. mk_base (UW + 0x36)%Z (mword_of_int 0x00012997 : mword 32)
    (mword_of_int (UW + 0x36) : mword 64) (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 19), AUIPC)) uwdb_00012997. Qed.

  Lemma uwi_3a : kernel_text -∗ instr (mword_of_int (UW + 0x3a) : mword 64) false (ITYPE (mword_of_int 0x9fe : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)).
  Proof. mk_base (UW + 0x3a)%Z (mword_of_int 0x9fe98993 : mword 32)
    (mword_of_int (UW + 0x3a) : mword 64) (ITYPE (mword_of_int 0x9fe : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)) uwdb_9fe98993. Qed.

  Lemma uwi_3e : kernel_text -∗ instr (mword_of_int (UW + 0x3e) : mword 64) false (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (UW + 0x3e)%Z (mword_of_int 0x0000a917 : mword 32)
    (mword_of_int (UW + 0x3e) : mword 64) (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 18), AUIPC)) uwdb_0000a917. Qed.

  Lemma uwi_42 : kernel_text -∗ instr (mword_of_int (UW + 0x42) : mword 64) false (ITYPE (mword_of_int 0x90e : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (UW + 0x42)%Z (mword_of_int 0x90e90913 : mword 32)
    (mword_of_int (UW + 0x42) : mword 64) (ITYPE (mword_of_int 0x90e : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) uwdb_90e90913. Qed.

  Lemma uwi_46 : kernel_text -∗ instr (mword_of_int (UW + 0x46) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 23), LUI)).
  Proof. mk_base (UW + 0x46)%Z (mword_of_int 0x10000bb7 : mword 32)
    (mword_of_int (UW + 0x46) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 23), LUI)) uwdb_10000bb7. Qed.

  Lemma uwi_4a : kernel_text -∗ instr (mword_of_int (UW + 0x4a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 22), ADDI)).
  Proof. mk_rvc (UW + 0x4a)%Z (mword_of_int 0x4b05 : mword 16)
    (mword_of_int (UW + 0x4a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 22), ADDI)) uwdc_4b05 exec_execute_C_LI. Qed.

  Lemma uwi_4c : kernel_text -∗ instr (mword_of_int (UW + 0x4c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 16 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (UW + 0x4c)%Z (mword_of_int 0xa005 : mword 16)
    (mword_of_int (UW + 0x4c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 16 : mword 11) ('b"0")), zreg)) uwdc_a005 exec_execute_C_J. Qed.

  (* --- the sleep block (+0x4e .. +0x58) --- *)
  Lemma uwi_4e : kernel_text -∗ instr (mword_of_int (UW + 0x4e) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (UW + 0x4e)%Z (mword_of_int 0x85ce : mword 16)
    (mword_of_int (UW + 0x4e) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)) uwdc_85ce exec_execute_C_MV. Qed.

  Lemma uwi_50 : kernel_text -∗ instr (mword_of_int (UW + 0x50) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (UW + 0x50)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (UW + 0x50) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma uwi_52 : kernel_text -∗ instr (mword_of_int (UW + 0x52) : mword 64) false (JAL (mword_of_int 5592 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UW + 0x52)%Z (mword_of_int 0x5d8010ef : mword 32)
    (mword_of_int (UW + 0x52) : mword 64) (JAL (mword_of_int 5592 : mword 21, Regidx (mword_of_int 1))) uwdb_5d8010ef. Qed.

  Lemma uwi_56 : kernel_text -∗ instr (mword_of_int (UW + 0x56) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)).
  Proof. mk_rvc (UW + 0x56)%Z (mword_of_int 0x409c : mword 16)
    (mword_of_int (UW + 0x56) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) cdec_409c exec_execute_C_LW. Qed.

  Lemma uwi_58 : kernel_text -∗ instr (mword_of_int (UW + 0x58) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (UW + 0x58)%Z (mword_of_int 0xfbfd : mword 16)
    (mword_of_int (UW + 0x58) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) uwdc_fbfd exec_execute_C_BNEZ. Qed.

  (* --- the loop body (+0x5a .. +0x68) --- *)
  Lemma uwi_5a : kernel_text -∗ instr (mword_of_int (UW + 0x5a) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), true, 1)).
  Proof. mk_base (UW + 0x5a)%Z (mword_of_int 0x000a4783 : mword 32)
    (mword_of_int (UW + 0x5a) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), true, 1)) uwdb_000a4783. Qed.

  Lemma uwi_5e : kernel_text -∗ instr (mword_of_int (UW + 0x5e) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 23), 1)).
  Proof. mk_base (UW + 0x5e)%Z (mword_of_int 0x00fb8023 : mword 32)
    (mword_of_int (UW + 0x5e) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 23), 1)) uwdb_00fb8023. Qed.

  Lemma uwi_62 : kernel_text -∗ instr (mword_of_int (UW + 0x62) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (UW + 0x62)%Z (mword_of_int 0x0164a023 : mword 32)
    (mword_of_int (UW + 0x62) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 9), 4)) uwdb_0164a023. Qed.

  Lemma uwi_66 : kernel_text -∗ instr (mword_of_int (UW + 0x66) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)).
  Proof. mk_rvc (UW + 0x66)%Z (mword_of_int 0x0a05 : mword 16)
    (mword_of_int (UW + 0x66) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)) uwdc_0a05 exec_execute_C_ADDI. Qed.

  Lemma uwi_68 : kernel_text -∗ instr (mword_of_int (UW + 0x68) : mword 64) false (BTYPE (mword_of_int 10 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 20), BEQ)).
  Proof. mk_base (UW + 0x68)%Z (mword_of_int 0x015a0563 : mword 32)
    (mword_of_int (UW + 0x68) : mword 64) (BTYPE (mword_of_int 10 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 20), BEQ)) uwdb_015a0563. Qed.

  (* --- the loop head (+0x6c .. +0x70) --- *)
  Lemma uwi_6c : kernel_text -∗ instr (mword_of_int (UW + 0x6c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)).
  Proof. mk_rvc (UW + 0x6c)%Z (mword_of_int 0x409c : mword 16)
    (mword_of_int (UW + 0x6c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) cdec_409c exec_execute_C_LW. Qed.

  Lemma uwi_6e : kernel_text -∗ instr (mword_of_int (UW + 0x6e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 240 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (UW + 0x6e)%Z (mword_of_int 0xf3e5 : mword 16)
    (mword_of_int (UW + 0x6e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 240 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) uwdc_f3e5 exec_execute_C_BNEZ. Qed.

  Lemma uwi_70 : kernel_text -∗ instr (mword_of_int (UW + 0x70) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (UW + 0x70)%Z (mword_of_int 0xb7ed : mword 16)
    (mword_of_int (UW + 0x70) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0")), zreg)) uwdc_b7ed exec_execute_C_J. Qed.

  (* --- the shrink-wrapped restores (+0x72 .. +0x7a) --- *)
  Lemma uwi_72 : kernel_text -∗ instr (mword_of_int (UW + 0x72) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (UW + 0x72)%Z (mword_of_int 0x7942 : mword 16)
    (mword_of_int (UW + 0x72) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_7942 exec_execute_C_LDSP. Qed.

  Lemma uwi_74 : kernel_text -∗ instr (mword_of_int (UW + 0x74) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (UW + 0x74)%Z (mword_of_int 0x79a2 : mword 16)
    (mword_of_int (UW + 0x74) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_79a2 exec_execute_C_LDSP. Qed.

  Lemma uwi_76 : kernel_text -∗ instr (mword_of_int (UW + 0x76) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (UW + 0x76)%Z (mword_of_int 0x7a02 : mword 16)
    (mword_of_int (UW + 0x76) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_7a02 exec_execute_C_LDSP. Qed.

  Lemma uwi_78 : kernel_text -∗ instr (mword_of_int (UW + 0x78) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (UW + 0x78)%Z (mword_of_int 0x6b42 : mword 16)
    (mword_of_int (UW + 0x78) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_6b42 exec_execute_C_LDSP. Qed.

  Lemma uwi_7a : kernel_text -∗ instr (mword_of_int (UW + 0x7a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (UW + 0x7a)%Z (mword_of_int 0x6ba2 : mword 16)
    (mword_of_int (UW + 0x7a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) cdec_6ba2 exec_execute_C_LDSP. Qed.

  (* --- release(&tx_lock) and the epilogue (+0x7c .. +0x92) --- *)
  Lemma uwi_7c : kernel_text -∗ instr (mword_of_int (UW + 0x7c) : mword 64) false (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (UW + 0x7c)%Z (mword_of_int 0x00012517 : mword 32)
    (mword_of_int (UW + 0x7c) : mword 64) (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00012517. Qed.

  Lemma uwi_80 : kernel_text -∗ instr (mword_of_int (UW + 0x80) : mword 64) false (ITYPE (mword_of_int 0x9b8 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (UW + 0x80)%Z (mword_of_int 0x9b850513 : mword 32)
    (mword_of_int (UW + 0x80) : mword 64) (ITYPE (mword_of_int 0x9b8 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) uwdb_9b850513. Qed.

  Lemma uwi_84 : kernel_text -∗ instr (mword_of_int (UW + 0x84) : mword 64) false (JAL (mword_of_int 816 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UW + 0x84)%Z (mword_of_int 0x330000ef : mword 32)
    (mword_of_int (UW + 0x84) : mword 64) (JAL (mword_of_int 816 : mword 21, Regidx (mword_of_int 1))) uwdb_330000ef. Qed.

  Lemma uwi_88 : kernel_text -∗ instr (mword_of_int (UW + 0x88) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (UW + 0x88)%Z (mword_of_int 0x60a6 : mword 16)
    (mword_of_int (UW + 0x88) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a6 exec_execute_C_LDSP. Qed.

  Lemma uwi_8a : kernel_text -∗ instr (mword_of_int (UW + 0x8a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (UW + 0x8a)%Z (mword_of_int 0x6406 : mword 16)
    (mword_of_int (UW + 0x8a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6406 exec_execute_C_LDSP. Qed.

  Lemma uwi_8c : kernel_text -∗ instr (mword_of_int (UW + 0x8c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (UW + 0x8c)%Z (mword_of_int 0x74e2 : mword 16)
    (mword_of_int (UW + 0x8c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74e2 exec_execute_C_LDSP. Qed.

  Lemma uwi_8e : kernel_text -∗ instr (mword_of_int (UW + 0x8e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (UW + 0x8e)%Z (mword_of_int 0x6ae2 : mword 16)
    (mword_of_int (UW + 0x8e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_6ae2 exec_execute_C_LDSP. Qed.

  Lemma uwi_90 : kernel_text -∗ instr (mword_of_int (UW + 0x90) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (UW + 0x90)%Z (mword_of_int 0x6161 : mword 16)
    (mword_of_int (UW + 0x90) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)) cdec_6161 exec_execute_C_ADDI16SP. Qed.

  Lemma uwi_92 : kernel_text -∗ instr (mword_of_int (UW + 0x92) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (UW + 0x92)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (UW + 0x92) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End WpUartwriteDecode.
