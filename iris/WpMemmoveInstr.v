(* WpMemmoveInstr.v -- discharge the instruction DECODINGS for the memmove
   instructions the proof actually steps (0x80000d28 .. 0x80000d66) from
   [kernel_text].

   Only the ASCENDING copy is decoded.  memmove's descending loop
   (memmove+0x3e..+0x5e) runs exactly when [src < dst && src + n > dst], which
   the non-overlapping contract (SpecMemmove) refutes from the two separately
   owned buffers -- the proof closes that arm before the branch steps, so those
   words are never fetched and need no decode.

   The eight 16-byte-frame prologue/epilogue words and the c.slli/c.srli
   (unsigned int) count-truncation pair are shared, so their [cdec_<word>]
   decodes come from KernelRvcDecode.v; the words unique to memmove get fresh
   decodes here, named by instruction BITS with a file-local prefix
   ([mmdc_<word>] compressed, [mmdb_<word>] base). *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode.
Require Import WpMmodeLeafBase.
Require Import SmodeCore KernelText.
Require Import WpRvcBridge.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Local Open Scope Z_scope.
Import Defs.

Notation MM := KernelSyms.memmove.

(* ===================================================================== *)
(* Fresh decode templates (bit patterns unique to memmove).              *)
(* ===================================================================== *)

(* +0x08  0xc205  c.beqz a2,+0x20  (the n == 0 test) *)
Lemma mmdc_c205 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc205 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 16, Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x16  0x872a  c.mv a4,a0  (the dst cursor) *)
Lemma mmdc_872a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x872a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 14), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x18  0x0585  c.addi a1,1  (src++) *)
Lemma mmdc_0585 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0585 : mword 16)) s
  = Some (C_ADDI (mword_of_int 1, Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x1a  0x0705  c.addi a4,1  (dst++) *)
Lemma mmdc_0705 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0705 : mword 16)) s
  = Some (C_ADDI (mword_of_int 1, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x34  0x9281  c.srli a3,32  (second half of the overlap test's cast) *)
Lemma mmdc_9281 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9281 : mword 16)) s
  = Some (C_SRLI (mword_of_int 32, Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x0a  0x02a5e363  bltu a1,a0,+0x26  (src < dst?) *)
Lemma mmdb_02a5e363 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02a5e363 : mword 32)) s
  = Some (BTYPE (mword_of_int 0x26, Regidx (mword_of_int 10), Regidx (mword_of_int 11), BLTU), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x12  0x00c587b3  add a5,a1,a2  (src end) *)
Lemma mmdb_00c587b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c587b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 12), Regidx (mword_of_int 11), Regidx (mword_of_int 15), ADD), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x1c  0xfff5c683  lbu a3,-1(a1) *)
Lemma mmdb_fff5c683 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfff5c683 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfff, Regidx (mword_of_int 11), Regidx (mword_of_int 13), true, 1), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x20  0xfed70fa3  sb a3,-1(a4) *)
Lemma mmdb_fed70fa3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfed70fa3 : mword 32)) s
  = Some (STORE (mword_of_int 0xfff, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 1), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x24  0xfeb79ae3  bne a5,a1,-12  (the loop back edge) *)
Lemma mmdb_feb79ae3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfeb79ae3 : mword 32)) s
  = Some (BTYPE (mword_of_int 0x1ff4, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BNE), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x30  0x02061693  slli a3,a2,32  (first half of the overlap test's cast) *)
Lemma mmdb_02061693 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02061693 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 13), SLLI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x36  0x00d58733  add a4,a1,a3  (src + n) *)
Lemma mmdb_00d58733 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d58733 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 11), Regidx (mword_of_int 14), ADD), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x3a  0xfce57ae3  bgeu a0,a4,-44  (dst >= src + n?  -- no overlap) *)
Lemma mmdb_fce57ae3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfce57ae3 : mword 32)) s
  = Some (BTYPE (mword_of_int 0x1fd4, Regidx (mword_of_int 14), Regidx (mword_of_int 10), BGEU), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* ===================================================================== *)
(* [instr] constructors from [kernel_text].                              *)
(*                                                                        *)
(* [mk_rvc] targets the ExecuteAs-EXPANDED base instruction               *)
(* ([instr pc true base]): [decname] decodes the compressed word and      *)
(* [expname] is its [exec_execute_C_*] expansion into [base].              *)
(* ===================================================================== *)
Section WpMemmoveInstr.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* +0x00  c.addi16sp sp,-16  ->  addi sp,sp,-16 *)
  Lemma minstr_mm_00 : kernel_text -∗ instr (mword_of_int (MM + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (MM + 0x00)%Z (mword_of_int 0x1141 : mword 16)
           (mword_of_int (MM + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  (* +0x02  c.sdsp ra,8(sp) *)
  Lemma minstr_mm_02 : kernel_text -∗ instr (mword_of_int (MM + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (MM + 0x02)%Z (mword_of_int 0xe406 : mword 16)
           (mword_of_int (MM + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  (* +0x04  c.sdsp s0,0(sp) *)
  Lemma minstr_mm_04 : kernel_text -∗ instr (mword_of_int (MM + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (MM + 0x04)%Z (mword_of_int 0xe022 : mword 16)
           (mword_of_int (MM + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  (* +0x06  c.addi4spn s0,sp,16 *)
  Lemma minstr_mm_06 : kernel_text -∗ instr (mword_of_int (MM + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (MM + 0x06)%Z (mword_of_int 0x0800 : mword 16)
           (mword_of_int (MM + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  (* +0x08  c.beqz a2,+0x20 *)
  Lemma minstr_mm_08 : kernel_text -∗ instr (mword_of_int (MM + 0x08) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 16 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)).
  Proof. mk_rvc (MM + 0x08)%Z (mword_of_int 0xc205 : mword 16)
           (mword_of_int (MM + 0x08) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 16 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)) mmdc_c205 exec_execute_C_BEQZ. Qed.

  (* +0x0a  bltu a1,a0,+0x26 *)
  Lemma minstr_mm_0a : kernel_text -∗ instr (mword_of_int (MM + 0x0a) : mword 64) false (BTYPE (mword_of_int 0x26, Regidx (mword_of_int 10), Regidx (mword_of_int 11), BLTU)).
  Proof. mk_base (MM + 0x0a)%Z (mword_of_int 0x02a5e363 : mword 32)
           (mword_of_int (MM + 0x0a) : mword 64) (BTYPE (mword_of_int 0x26, Regidx (mword_of_int 10), Regidx (mword_of_int 11), BLTU)) mmdb_02a5e363. Qed.

  (* +0x0e  c.slli a2,32 *)
  Lemma minstr_mm_0e : kernel_text -∗ instr (mword_of_int (MM + 0x0e) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)).
  Proof. mk_rvc (MM + 0x0e)%Z (mword_of_int 0x1602 : mword 16)
           (mword_of_int (MM + 0x0e) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)) cdec_1602 exec_execute_C_SLLI. Qed.

  (* +0x10  c.srli a2,32 *)
  Lemma minstr_mm_10 : kernel_text -∗ instr (mword_of_int (MM + 0x10) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 4)), creg2reg_idx (Cregidx (mword_of_int 4)), SRLI)).
  Proof. mk_rvc (MM + 0x10)%Z (mword_of_int 0x9201 : mword 16)
           (mword_of_int (MM + 0x10) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 4)), creg2reg_idx (Cregidx (mword_of_int 4)), SRLI)) cdec_9201 exec_execute_C_SRLI. Qed.

  (* +0x12  add a5,a1,a2 *)
  Lemma minstr_mm_12 : kernel_text -∗ instr (mword_of_int (MM + 0x12) : mword 64) false (RTYPE (Regidx (mword_of_int 12), Regidx (mword_of_int 11), Regidx (mword_of_int 15), ADD)).
  Proof. mk_base (MM + 0x12)%Z (mword_of_int 0x00c587b3 : mword 32)
           (mword_of_int (MM + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 12), Regidx (mword_of_int 11), Regidx (mword_of_int 15), ADD)) mmdb_00c587b3. Qed.

  (* +0x16  c.mv a4,a0 *)
  Lemma minstr_mm_16 : kernel_text -∗ instr (mword_of_int (MM + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (MM + 0x16)%Z (mword_of_int 0x872a : mword 16)
           (mword_of_int (MM + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 14), ADD)) mmdc_872a exec_execute_C_MV. Qed.

  (* +0x18  c.addi a1,1 *)
  Lemma minstr_mm_18 : kernel_text -∗ instr (mword_of_int (MM + 0x18) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (MM + 0x18)%Z (mword_of_int 0x0585 : mword 16)
           (mword_of_int (MM + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) mmdc_0585 exec_execute_C_ADDI. Qed.

  (* +0x1a  c.addi a4,1 *)
  Lemma minstr_mm_1a : kernel_text -∗ instr (mword_of_int (MM + 0x1a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (MM + 0x1a)%Z (mword_of_int 0x0705 : mword 16)
           (mword_of_int (MM + 0x1a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) mmdc_0705 exec_execute_C_ADDI. Qed.

  (* +0x1c  lbu a3,-1(a1) *)
  Lemma minstr_mm_1c : kernel_text -∗ instr (mword_of_int (MM + 0x1c) : mword 64) false (LOAD (mword_of_int 0xfff, Regidx (mword_of_int 11), Regidx (mword_of_int 13), true, 1)).
  Proof. mk_base (MM + 0x1c)%Z (mword_of_int 0xfff5c683 : mword 32)
           (mword_of_int (MM + 0x1c) : mword 64) (LOAD (mword_of_int 0xfff, Regidx (mword_of_int 11), Regidx (mword_of_int 13), true, 1)) mmdb_fff5c683. Qed.

  (* +0x20  sb a3,-1(a4) *)
  Lemma minstr_mm_20 : kernel_text -∗ instr (mword_of_int (MM + 0x20) : mword 64) false (STORE (mword_of_int 0xfff, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 1)).
  Proof. mk_base (MM + 0x20)%Z (mword_of_int 0xfed70fa3 : mword 32)
           (mword_of_int (MM + 0x20) : mword 64) (STORE (mword_of_int 0xfff, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 1)) mmdb_fed70fa3. Qed.

  (* +0x24  bne a5,a1,-12 *)
  Lemma minstr_mm_24 : kernel_text -∗ instr (mword_of_int (MM + 0x24) : mword 64) false (BTYPE (mword_of_int 0x1ff4, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (MM + 0x24)%Z (mword_of_int 0xfeb79ae3 : mword 32)
           (mword_of_int (MM + 0x24) : mword 64) (BTYPE (mword_of_int 0x1ff4, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BNE)) mmdb_feb79ae3. Qed.

  (* +0x28  c.ldsp ra,8(sp) *)
  Lemma minstr_mm_28 : kernel_text -∗ instr (mword_of_int (MM + 0x28) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (MM + 0x28)%Z (mword_of_int 0x60a2 : mword 16)
           (mword_of_int (MM + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  (* +0x2a  c.ldsp s0,0(sp) *)
  Lemma minstr_mm_2a : kernel_text -∗ instr (mword_of_int (MM + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (MM + 0x2a)%Z (mword_of_int 0x6402 : mword 16)
           (mword_of_int (MM + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  (* +0x2c  c.addi16sp sp,16 *)
  Lemma minstr_mm_2c : kernel_text -∗ instr (mword_of_int (MM + 0x2c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (MM + 0x2c)%Z (mword_of_int 0x0141 : mword 16)
           (mword_of_int (MM + 0x2c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  (* +0x2e  c.jr ra *)
  Lemma minstr_mm_2e : kernel_text -∗ instr (mword_of_int (MM + 0x2e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (MM + 0x2e)%Z (mword_of_int 0x8082 : mword 16)
           (mword_of_int (MM + 0x2e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* +0x30  slli a3,a2,32 *)
  Lemma minstr_mm_30 : kernel_text -∗ instr (mword_of_int (MM + 0x30) : mword 64) false (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 13), SLLI)).
  Proof. mk_base (MM + 0x30)%Z (mword_of_int 0x02061693 : mword 32)
           (mword_of_int (MM + 0x30) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 13), SLLI)) mmdb_02061693. Qed.

  (* +0x34  c.srli a3,32 *)
  Lemma minstr_mm_34 : kernel_text -∗ instr (mword_of_int (MM + 0x34) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 5)), creg2reg_idx (Cregidx (mword_of_int 5)), SRLI)).
  Proof. mk_rvc (MM + 0x34)%Z (mword_of_int 0x9281 : mword 16)
           (mword_of_int (MM + 0x34) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 5)), creg2reg_idx (Cregidx (mword_of_int 5)), SRLI)) mmdc_9281 exec_execute_C_SRLI. Qed.

  (* +0x36  add a4,a1,a3 *)
  Lemma minstr_mm_36 : kernel_text -∗ instr (mword_of_int (MM + 0x36) : mword 64) false (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 11), Regidx (mword_of_int 14), ADD)).
  Proof. mk_base (MM + 0x36)%Z (mword_of_int 0x00d58733 : mword 32)
           (mword_of_int (MM + 0x36) : mword 64) (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 11), Regidx (mword_of_int 14), ADD)) mmdb_00d58733. Qed.

  (* +0x3a  bgeu a0,a4,-44 *)
  Lemma minstr_mm_3a : kernel_text -∗ instr (mword_of_int (MM + 0x3a) : mword 64) false (BTYPE (mword_of_int 0x1fd4, Regidx (mword_of_int 14), Regidx (mword_of_int 10), BGEU)).
  Proof. mk_base (MM + 0x3a)%Z (mword_of_int 0xfce57ae3 : mword 32)
           (mword_of_int (MM + 0x3a) : mword 64) (BTYPE (mword_of_int 0x1fd4, Regidx (mword_of_int 14), Regidx (mword_of_int 10), BGEU)) mmdb_fce57ae3. Qed.

End WpMemmoveInstr.
