(* CodeSleep.v -- decode templates + [instr] facts for sleep()'s 26
   instructions at KernelSyms.sleep = 0x80001f06.

   sleep's 48-byte frame prologue/epilogue (c.addi16sp -48 / five c.sdsp /
   c.addi4spn / five c.ldsp / c.addi16sp +48 / c.ret) is byte-identical to
   sched's/freerange's, so those decodes come from the shared [cdec_*]
   templates in KernelRvcDecode.v; the remaining
   words -- the four c.mv's, the six jal's, the c.li a5,2, the c.sw a5,24(s1)
   and the two 8-byte sd's (chan := chan / chan := 0) -- are sleep's own and
   get fresh templates here. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode KernelText.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
From iris.base_logic.lib Require Import invariants.
Require Import KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

Notation SL := KernelSyms.sleep.

(* ===================================================================== *)
(* Fresh compressed decode templates.                                     *)
(* ===================================================================== *)

(* +0x0e  0x89aa  c.mv s3,a0 -- [cdec_89aa] (KernelRvcDecode.v) *)

(* +0x26  0x4789  c.li a5,2 *)
Lemma sldec_li_a5_2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4789 : mword 16)) s
  = Some (C_LI (mword_of_int 2, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Fresh base (32-bit) decode templates.                                  *)
(* ===================================================================== *)

(* +0x12  0x9edff0ef  jal ra,myproc (target 0x80001904; offset -1556) *)
Lemma sldec_jal_myproc s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9edff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095596 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x18  0xcebfe0ef  jal ra,acquire (target 0x80000c08; offset -4886) *)
Lemma sldec_jal_acquire1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xcebfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092266 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x1e  0xd6dfe0ef  jal ra,release (target 0x80000c90; offset -4756) *)
Lemma sldec_jal_release1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd6dfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092396 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x22  0x0334b023  sd s3,32(s1) *)
Lemma sldec_sd_s3_32 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0334b023 : mword 32)) s
  = Some (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.


(* +0x2e  0x0204b023  sd x0,32(s1) *)
Lemma sldec_sd_x0_32 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0204b023 : mword 32)) s
  = Some (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x34  0xd57fe0ef  jal ra,release (target 0x80000c90; offset -4778) *)
Lemma sldec_jal_release2 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd57fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092374 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x3a  0xcc9fe0ef  jal ra,acquire (target 0x80000c08; offset -4920) *)
Lemma sldec_jal_acquire2 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xcc9fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092232 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Section CodeSleep.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- prologue: 48-byte frame, saves ra/s0/s1/s2/s3 (freerange decodes) ---- *)
  Lemma sli_00 : kernel_text -∗ instr (mword_of_int (SL + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SL + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (SL + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma sli_02 : kernel_text -∗ instr (mword_of_int (SL + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (SL + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (SL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma sli_04 : kernel_text -∗ instr (mword_of_int (SL + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (SL + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (SL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma sli_06 : kernel_text -∗ instr (mword_of_int (SL + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (SL + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (SL + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma sli_08 : kernel_text -∗ instr (mword_of_int (SL + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (SL + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (SL + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  Lemma sli_0a : kernel_text -∗ instr (mword_of_int (SL + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (SL + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (SL + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  Lemma sli_0c : kernel_text -∗ instr (mword_of_int (SL + 0x0c) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (SL + 0x0c)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (SL + 0x0c) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  (* ---- +0x0e: c.mv s3,a0 ---- *)
  Lemma sli_0e : kernel_text -∗ instr (mword_of_int (SL + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (SL + 0x0e)%Z (mword_of_int 0x89aa : mword 16)
    (mword_of_int (SL + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)) cdec_89aa exec_execute_C_MV. Qed.

  (* ---- +0x10: c.mv s2,a1 ---- *)
  Lemma sli_10 : kernel_text -∗ instr (mword_of_int (SL + 0x10) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (SL + 0x10)%Z (mword_of_int 0x892e : mword 16)
    (mword_of_int (SL + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)) cdec_892e exec_execute_C_MV. Qed.

  (* ---- +0x12: jal myproc ---- *)
  Lemma sli_12 : kernel_text -∗ instr (mword_of_int (SL + 0x12) : mword 64) false (JAL (mword_of_int 2095596 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SL + 0x12)%Z (mword_of_int 0x9edff0ef : mword 32)
    (mword_of_int (SL + 0x12) : mword 64) (JAL (mword_of_int 2095596 : mword 21, Regidx (mword_of_int 1))) sldec_jal_myproc. Qed.

  (* ---- +0x16: c.mv s1,a0 ---- *)
  Lemma sli_16 : kernel_text -∗ instr (mword_of_int (SL + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (SL + 0x16)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (SL + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* ---- +0x18: jal acquire ---- *)
  Lemma sli_18 : kernel_text -∗ instr (mword_of_int (SL + 0x18) : mword 64) false (JAL (mword_of_int 2092266 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SL + 0x18)%Z (mword_of_int 0xcebfe0ef : mword 32)
    (mword_of_int (SL + 0x18) : mword 64) (JAL (mword_of_int 2092266 : mword 21, Regidx (mword_of_int 1))) sldec_jal_acquire1. Qed.

  (* ---- +0x1c: c.mv a0,s2 ---- *)
  Lemma sli_1c : kernel_text -∗ instr (mword_of_int (SL + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SL + 0x1c)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (SL + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  (* ---- +0x1e: jal release ---- *)
  Lemma sli_1e : kernel_text -∗ instr (mword_of_int (SL + 0x1e) : mword 64) false (JAL (mword_of_int 2092396 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SL + 0x1e)%Z (mword_of_int 0xd6dfe0ef : mword 32)
    (mword_of_int (SL + 0x1e) : mword 64) (JAL (mword_of_int 2092396 : mword 21, Regidx (mword_of_int 1))) sldec_jal_release1. Qed.

  (* ---- +0x22: sd s3,32(s1) ---- *)
  Lemma sli_22 : kernel_text -∗ instr (mword_of_int (SL + 0x22) : mword 64) false (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), 8)).
  Proof. mk_base (SL + 0x22)%Z (mword_of_int 0x0334b023 : mword 32)
    (mword_of_int (SL + 0x22) : mword 64) (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), 8)) sldec_sd_s3_32. Qed.

  (* ---- +0x26: c.li a5,2 ---- *)
  Lemma sli_26 : kernel_text -∗ instr (mword_of_int (SL + 0x26) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SL + 0x26)%Z (mword_of_int 0x4789 : mword 16)
    (mword_of_int (SL + 0x26) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) sldec_li_a5_2 exec_execute_C_LI. Qed.

  (* ---- +0x28: c.sw a5,24(s1) ---- *)
  Lemma sli_28 : kernel_text -∗ instr (mword_of_int (SL + 0x28) : mword 64) true (STORE (mword_of_int 24, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (SL + 0x28)%Z (mword_of_int 0xcc9c : mword 16)
    (mword_of_int (SL + 0x28) : mword 64) (STORE (mword_of_int 24, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_cc9c cexec_cc9c. Qed.

  (* ---- +0x2a: jal sched ---- *)
  Lemma sli_2a : kernel_text -∗ instr (mword_of_int (SL + 0x2a) : mword 64) false (JAL (mword_of_int 2096878 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SL + 0x2a)%Z (mword_of_int 0xeefff0ef : mword 32)
    (mword_of_int (SL + 0x2a) : mword 64) (JAL (mword_of_int 2096878 : mword 21, Regidx (mword_of_int 1))) bdec_eefff0ef. Qed.

  (* ---- +0x2e: sd x0,32(s1) ---- *)
  Lemma sli_2e : kernel_text -∗ instr (mword_of_int (SL + 0x2e) : mword 64) false (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8)).
  Proof. mk_base (SL + 0x2e)%Z (mword_of_int 0x0204b023 : mword 32)
    (mword_of_int (SL + 0x2e) : mword 64) (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8)) sldec_sd_x0_32. Qed.

  (* ---- +0x32: c.mv a0,s1 ---- *)
  Lemma sli_32 : kernel_text -∗ instr (mword_of_int (SL + 0x32) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SL + 0x32)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (SL + 0x32) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* ---- +0x34: jal release ---- *)
  Lemma sli_34 : kernel_text -∗ instr (mword_of_int (SL + 0x34) : mword 64) false (JAL (mword_of_int 2092374 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SL + 0x34)%Z (mword_of_int 0xd57fe0ef : mword 32)
    (mword_of_int (SL + 0x34) : mword 64) (JAL (mword_of_int 2092374 : mword 21, Regidx (mword_of_int 1))) sldec_jal_release2. Qed.

  (* ---- +0x38: c.mv a0,s2 ---- *)
  Lemma sli_38 : kernel_text -∗ instr (mword_of_int (SL + 0x38) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SL + 0x38)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (SL + 0x38) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  (* ---- +0x3a: jal acquire ---- *)
  Lemma sli_3a : kernel_text -∗ instr (mword_of_int (SL + 0x3a) : mword 64) false (JAL (mword_of_int 2092232 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SL + 0x3a)%Z (mword_of_int 0xcc9fe0ef : mword 32)
    (mword_of_int (SL + 0x3a) : mword 64) (JAL (mword_of_int 2092232 : mword 21, Regidx (mword_of_int 1))) sldec_jal_acquire2. Qed.

  (* ---- +0x3e..+0x46: c.ldsp ra/s0/s1/s2/s3 (freerange decodes) ---- *)
  Lemma sli_3e : kernel_text -∗ instr (mword_of_int (SL + 0x3e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (SL + 0x3e)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (SL + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma sli_40 : kernel_text -∗ instr (mword_of_int (SL + 0x40) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (SL + 0x40)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (SL + 0x40) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma sli_42 : kernel_text -∗ instr (mword_of_int (SL + 0x42) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (SL + 0x42)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (SL + 0x42) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma sli_44 : kernel_text -∗ instr (mword_of_int (SL + 0x44) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (SL + 0x44)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (SL + 0x44) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma sli_46 : kernel_text -∗ instr (mword_of_int (SL + 0x46) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (SL + 0x46)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (SL + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  (* ---- +0x48: c.addi16sp sp,48 ---- *)
  Lemma sli_48 : kernel_text -∗ instr (mword_of_int (SL + 0x48) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SL + 0x48)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (SL + 0x48) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  (* ---- +0x4a: c.ret ---- *)
  Lemma sli_4a : kernel_text -∗ instr (mword_of_int (SL + 0x4a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (SL + 0x4a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (SL + 0x4a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeSleep.
