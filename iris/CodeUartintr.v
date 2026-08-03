(* CodeUartintr.v -- the instruction-DECODE layer for xv6's uartintr().
   For every instruction of

     uartintr @ 0x800009ce .. 0x80000a44   (offsets 0x00 .. 0x76)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([uii2_<off>]).

   The 32-byte frame (ra/s0/s1/s2) is KernelRvcDecode's shared [cdec_*] set;
   the four base words that uartintr shares with another function
   ([lui a5,0x10000] with uartinit and uartputc_sync, [andi a5,a5,32] with
   uartputc_sync, [auipc a5,0xa] with printk and uartputc_sync,
   [lbu a0,0(s2)] with printk, [auipc a0,0x12] with four others) come from
   KernelBaseDecode.v; the rest are uartintr's own.

   NOTE for the next decode sweep: the private copies of the first four words
   in CodeUartinit.v / CodeUartPutcSync.v / CodePrintk.v are now
   redundant with the KernelBaseDecode entries added here and can be retired.

   +0x44..+0x54 is uartgetc, which gcc INLINED (there is no such symbol in the
   image): the rx-ready poll, the [beqz] that is the C's [c == -1] test, and
   the RHR read whose byte goes straight to consoleintr. *)
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
(* Compressed decode facts unique to uartintr.                            *)
(* ===================================================================== *)

(* 0xe78d  c.bnez a5,+0x2a  (THRE set -> the tx branch at +0x56) *)
Lemma uidc2_e78d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe78d : mword 16)) s
  = Some (C_BNEZ (mword_of_int 21, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0495  c.addi s1,s1,5  (s1 := UART0 + LSR) *)
Lemma uidc2_0495 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0495 : mword 16)) s
  = Some (C_ADDI (mword_of_int 5, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.



(* 0xb7d1  c.j -0x3c  (the tx branch rejoins at the release) *)
Lemma uidc2_b7d1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb7d1 : mword 16)) s
  = Some (C_J (mword_of_int 2018), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (32-bit) decode facts unique to uartintr.                         *)
(* ===================================================================== *)

(* lbu a5,2(a5) -- the ISR read that "acknowledges the interrupt" *)
Lemma uidb2_0027c783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0027c783 : mword 32)) s
  = Some (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* lbu a5,5(a5) -- the LSR read under tx_lock *)
Lemma uidb2_0057c783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0057c783 : mword 32)) s
  = Some (LOAD (mword_of_int 5 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,a0,-1746 / -1772 -- &tx_lock, twice *)
Lemma uidb2_92e50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x92e50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x92e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb2_91450513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x91450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x914 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,acquire / release / consoleintr / wakeup *)
Lemma uidb2_21e000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x21e000ef : mword 32)) s
  = Some (JAL (mword_of_int 542 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb2_28c000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x28c000ef : mword 32)) s
  = Some (JAL (mword_of_int 652 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb2_891ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x891ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095248 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb2_51e010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x51e010ef : mword 32)) s
  = Some (JAL (mword_of_int 5406 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* lui s1,0x10000 / lui s2,0x10000 -- the two rx-loop bases *)
Lemma uidb2_100004b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x100004b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 9), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb2_10000937 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10000937 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 18), LUI), s).
Proof. decode_bridge_ms. Qed.

(* lbu a5,0(s1) -- uartgetc's rx-ready poll *)
Lemma uidb2_0004c783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004c783 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* sw zero,-2040(a5) -- tx_busy = 0 *)
Lemma uidb2_8007a423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8007a423 : mword 32)) s
  = Some (STORE (mword_of_int 0x808 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

(* auipc a0,0x9 / addi a0,a0,2044 -- &tx_chan, the wakeup channel *)
Lemma uidb2_00009517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00009517 : mword 32)) s
  = Some (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb2_7fc50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7fc50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x7fc : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Section CodeUartintr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation UI := KernelSyms.uartintr.

  (* --- prologue (+0x00 .. +0x0a): the 32-byte frame --- *)
  Lemma uii2_00 : kernel_text -∗ instr (mword_of_int (UI + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (UI + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (UI + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma uii2_02 : kernel_text -∗ instr (mword_of_int (UI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (UI + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (UI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma uii2_04 : kernel_text -∗ instr (mword_of_int (UI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (UI + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (UI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma uii2_06 : kernel_text -∗ instr (mword_of_int (UI + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (UI + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (UI + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma uii2_08 : kernel_text -∗ instr (mword_of_int (UI + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (UI + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (UI + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma uii2_0a : kernel_text -∗ instr (mword_of_int (UI + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (UI + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (UI + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* --- the ISR acknowledge (+0x0c .. +0x10) --- *)
  Lemma uii2_0c : kernel_text -∗ instr (mword_of_int (UI + 0x0c) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (UI + 0x0c)%Z (mword_of_int 0x100007b7 : mword 32)
    (mword_of_int (UI + 0x0c) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI)) bdec_100007b7. Qed.

  Lemma uii2_10 : kernel_text -∗ instr (mword_of_int (UI + 0x10) : mword 64) false (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1)).
  Proof. mk_base (UI + 0x10)%Z (mword_of_int 0x0027c783 : mword 32)
    (mword_of_int (UI + 0x10) : mword 64) (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1)) uidb2_0027c783. Qed.

  (* --- acquire(&tx_lock) (+0x14 .. +0x1c) --- *)
  Lemma uii2_14 : kernel_text -∗ instr (mword_of_int (UI + 0x14) : mword 64) false (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (UI + 0x14)%Z (mword_of_int 0x00012517 : mword 32)
    (mword_of_int (UI + 0x14) : mword 64) (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00012517. Qed.

  Lemma uii2_18 : kernel_text -∗ instr (mword_of_int (UI + 0x18) : mword 64) false (ITYPE (mword_of_int 0x92e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (UI + 0x18)%Z (mword_of_int 0x92e50513 : mword 32)
    (mword_of_int (UI + 0x18) : mword 64) (ITYPE (mword_of_int 0x92e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) uidb2_92e50513. Qed.

  Lemma uii2_1c : kernel_text -∗ instr (mword_of_int (UI + 0x1c) : mword 64) false (JAL (mword_of_int 542 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UI + 0x1c)%Z (mword_of_int 0x21e000ef : mword 32)
    (mword_of_int (UI + 0x1c) : mword 64) (JAL (mword_of_int 542 : mword 21, Regidx (mword_of_int 1))) uidb2_21e000ef. Qed.

  (* --- the THRE test (+0x20 .. +0x2c) --- *)
  Lemma uii2_20 : kernel_text -∗ instr (mword_of_int (UI + 0x20) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (UI + 0x20)%Z (mword_of_int 0x100007b7 : mword 32)
    (mword_of_int (UI + 0x20) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI)) bdec_100007b7. Qed.

  Lemma uii2_24 : kernel_text -∗ instr (mword_of_int (UI + 0x24) : mword 64) false (LOAD (mword_of_int 5 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1)).
  Proof. mk_base (UI + 0x24)%Z (mword_of_int 0x0057c783 : mword 32)
    (mword_of_int (UI + 0x24) : mword 64) (LOAD (mword_of_int 5 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1)) uidb2_0057c783. Qed.

  Lemma uii2_28 : kernel_text -∗ instr (mword_of_int (UI + 0x28) : mword 64) false (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_base (UI + 0x28)%Z (mword_of_int 0x0207f793 : mword 32)
    (mword_of_int (UI + 0x28) : mword 64) (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) bdec_0207f793. Qed.

  Lemma uii2_2c : kernel_text -∗ instr (mword_of_int (UI + 0x2c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 21 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (UI + 0x2c)%Z (mword_of_int 0xe78d : mword 16)
    (mword_of_int (UI + 0x2c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 21 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) uidc2_e78d exec_execute_C_BNEZ. Qed.

  (* --- release(&tx_lock) (+0x2e .. +0x36) --- *)
  Lemma uii2_2e : kernel_text -∗ instr (mword_of_int (UI + 0x2e) : mword 64) false (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (UI + 0x2e)%Z (mword_of_int 0x00012517 : mword 32)
    (mword_of_int (UI + 0x2e) : mword 64) (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00012517. Qed.

  Lemma uii2_32 : kernel_text -∗ instr (mword_of_int (UI + 0x32) : mword 64) false (ITYPE (mword_of_int 0x914 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (UI + 0x32)%Z (mword_of_int 0x91450513 : mword 32)
    (mword_of_int (UI + 0x32) : mword 64) (ITYPE (mword_of_int 0x914 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) uidb2_91450513. Qed.

  Lemma uii2_36 : kernel_text -∗ instr (mword_of_int (UI + 0x36) : mword 64) false (JAL (mword_of_int 652 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UI + 0x36)%Z (mword_of_int 0x28c000ef : mword 32)
    (mword_of_int (UI + 0x36) : mword 64) (JAL (mword_of_int 652 : mword 21, Regidx (mword_of_int 1))) uidb2_28c000ef. Qed.

  (* --- the rx loop's two bases (+0x3a .. +0x40) --- *)
  Lemma uii2_3a : kernel_text -∗ instr (mword_of_int (UI + 0x3a) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 9), LUI)).
  Proof. mk_base (UI + 0x3a)%Z (mword_of_int 0x100004b7 : mword 32)
    (mword_of_int (UI + 0x3a) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 9), LUI)) uidb2_100004b7. Qed.

  Lemma uii2_3e : kernel_text -∗ instr (mword_of_int (UI + 0x3e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_rvc (UI + 0x3e)%Z (mword_of_int 0x0495 : mword 16)
    (mword_of_int (UI + 0x3e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) uidc2_0495 exec_execute_C_ADDI. Qed.

  Lemma uii2_40 : kernel_text -∗ instr (mword_of_int (UI + 0x40) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 18), LUI)).
  Proof. mk_base (UI + 0x40)%Z (mword_of_int 0x10000937 : mword 32)
    (mword_of_int (UI + 0x40) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 18), LUI)) uidb2_10000937. Qed.

  (* --- uartgetc, INLINED (+0x44 .. +0x54) --- *)
  Lemma uii2_44 : kernel_text -∗ instr (mword_of_int (UI + 0x44) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), true, 1)).
  Proof. mk_base (UI + 0x44)%Z (mword_of_int 0x0004c783 : mword 32)
    (mword_of_int (UI + 0x44) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), true, 1)) uidb2_0004c783. Qed.

  Lemma uii2_48 : kernel_text -∗ instr (mword_of_int (UI + 0x48) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), ANDI)).
  Proof. mk_rvc (UI + 0x48)%Z (mword_of_int 0x8b85 : mword 16)
    (mword_of_int (UI + 0x48) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), ANDI)) cdec_8b85 exec_execute_C_ANDI. Qed.

  Lemma uii2_4a : kernel_text -∗ instr (mword_of_int (UI + 0x4a) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 17 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (UI + 0x4a)%Z (mword_of_int 0xc38d : mword 16)
    (mword_of_int (UI + 0x4a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 17 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) cdec_c38d exec_execute_C_BEQZ. Qed.

  Lemma uii2_4c : kernel_text -∗ instr (mword_of_int (UI + 0x4c) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), true, 1)).
  Proof. mk_base (UI + 0x4c)%Z (mword_of_int 0x00094503 : mword 32)
    (mword_of_int (UI + 0x4c) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), true, 1)) bdec_00094503. Qed.

  Lemma uii2_50 : kernel_text -∗ instr (mword_of_int (UI + 0x50) : mword 64) false (JAL (mword_of_int 2095248 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UI + 0x50)%Z (mword_of_int 0x891ff0ef : mword 32)
    (mword_of_int (UI + 0x50) : mword 64) (JAL (mword_of_int 2095248 : mword 21, Regidx (mword_of_int 1))) uidb2_891ff0ef. Qed.

  Lemma uii2_54 : kernel_text -∗ instr (mword_of_int (UI + 0x54) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (UI + 0x54)%Z (mword_of_int 0xbfc5 : mword 16)
    (mword_of_int (UI + 0x54) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0")), zreg)) cdec_bfc5 exec_execute_C_J. Qed.

  (* --- the tx branch (+0x56 .. +0x6a) --- *)
  Lemma uii2_56 : kernel_text -∗ instr (mword_of_int (UI + 0x56) : mword 64) false (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (UI + 0x56)%Z (mword_of_int 0x0000a797 : mword 32)
    (mword_of_int (UI + 0x56) : mword 64) (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0000a797. Qed.

  Lemma uii2_5a : kernel_text -∗ instr (mword_of_int (UI + 0x5a) : mword 64) false (STORE (mword_of_int 0x808 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (UI + 0x5a)%Z (mword_of_int 0x8007a423 : mword 32)
    (mword_of_int (UI + 0x5a) : mword 64) (STORE (mword_of_int 0x808 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)) uidb2_8007a423. Qed.

  Lemma uii2_5e : kernel_text -∗ instr (mword_of_int (UI + 0x5e) : mword 64) false (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (UI + 0x5e)%Z (mword_of_int 0x00009517 : mword 32)
    (mword_of_int (UI + 0x5e) : mword 64) (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 10), AUIPC)) uidb2_00009517. Qed.

  Lemma uii2_62 : kernel_text -∗ instr (mword_of_int (UI + 0x62) : mword 64) false (ITYPE (mword_of_int 0x7fc : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (UI + 0x62)%Z (mword_of_int 0x7fc50513 : mword 32)
    (mword_of_int (UI + 0x62) : mword 64) (ITYPE (mword_of_int 0x7fc : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) uidb2_7fc50513. Qed.

  Lemma uii2_66 : kernel_text -∗ instr (mword_of_int (UI + 0x66) : mword 64) false (JAL (mword_of_int 5406 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UI + 0x66)%Z (mword_of_int 0x51e010ef : mword 32)
    (mword_of_int (UI + 0x66) : mword 64) (JAL (mword_of_int 5406 : mword 21, Regidx (mword_of_int 1))) uidb2_51e010ef. Qed.

  Lemma uii2_6a : kernel_text -∗ instr (mword_of_int (UI + 0x6a) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2018 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (UI + 0x6a)%Z (mword_of_int 0xb7d1 : mword 16)
    (mword_of_int (UI + 0x6a) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2018 : mword 11) ('b"0")), zreg)) uidc2_b7d1 exec_execute_C_J. Qed.

  (* --- epilogue (+0x6c .. +0x76) --- *)
  Lemma uii2_6c : kernel_text -∗ instr (mword_of_int (UI + 0x6c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (UI + 0x6c)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (UI + 0x6c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma uii2_6e : kernel_text -∗ instr (mword_of_int (UI + 0x6e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (UI + 0x6e)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (UI + 0x6e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma uii2_70 : kernel_text -∗ instr (mword_of_int (UI + 0x70) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (UI + 0x70)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (UI + 0x70) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma uii2_72 : kernel_text -∗ instr (mword_of_int (UI + 0x72) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (UI + 0x72)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (UI + 0x72) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma uii2_74 : kernel_text -∗ instr (mword_of_int (UI + 0x74) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (UI + 0x74)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (UI + 0x74) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma uii2_76 : kernel_text -∗ instr (mword_of_int (UI + 0x76) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (UI + 0x76)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (UI + 0x76) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeUartintr.
