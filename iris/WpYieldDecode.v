(* WpYieldDecode.v -- decode templates + [instr] facts for yield()'s 18
   instructions at KernelSyms.yield = 0x80001eda.

   yield's 32-byte frame prologue/epilogue (c.addi sp,-32 / three c.sdsp /
   c.addi4spn / three c.ldsp / c.addi16sp / c.ret) is byte-identical to
   myproc's/acquire's, so those decodes reuse the shared [podec_*] templates
   from KernelRvcDecode.v.  The four jal's (myproc / acquire / sched /
   release), the two c.mv's (s1,a0 and a0,s1), the c.li a5,3 and the
   c.sw a5,24(s1) are yield's own and get fresh templates here. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode WpLeafCommon KernelText WpAuipc.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Import WpMycpu.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

Notation YD := KernelSyms.yield.

(* ===================================================================== *)
(* Fresh base (32-bit) jal decode templates.                              *)
(* ===================================================================== *)

(* +0x0a  0xa21ff0ef  jal ra,myproc (target 0x80001904) *)
Lemma yddec_jal_myproc s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa21ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095648 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x10  0xd1ffe0ef  jal ra,acquire (target 0x80000c08) *)
Lemma yddec_jal_acquire s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd1ffe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092318 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x18  0xf2dff0ef  jal ra,sched (target 0x80001e1e) *)
Lemma yddec_jal_sched s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf2dff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096940 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x1e  0xd99fe0ef  jal ra,release (target 0x80000c90) *)
Lemma yddec_jal_release s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd99fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092440 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* ===================================================================== *)
(* Fresh compressed decode templates.                                     *)
(* ===================================================================== *)

(* +0x0e  0x84aa  c.mv s1,a0 *)
Lemma yddec_mv_s1_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84aa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x14  0x478d  c.li a5,3 *)
Lemma yddec_li_a5_3 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x478d : mword 16)) s
  = Some (C_LI (mword_of_int 3, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x16  0xcc9c  c.sw a5,24(s1) *)
Lemma yddec_sw_a5_24 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcc9c : mword 16)) s
  = Some (C_SW (mword_of_int 6, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* the specialized C_SW -> STORE bridge (leaf-friendly Regidx / mword_of_int
   form; mirror of WpSconfPlicinit.plexec_sw40). *)
Lemma yd_cr1 : creg2reg_idx (Cregidx (mword_of_int 1)) = Regidx (mword_of_int 9).
Proof. vm_compute. reflexivity. Qed.
Lemma yd_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15).
Proof. vm_compute. reflexivity. Qed.
Lemma yd_imm24 : zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00")) = (mword_of_int 24 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ydexec_sw24 s :
  exec (execute (C_SW (mword_of_int 6, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 24, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_SW. cbn zeta.
  rewrite exec_returnM. rewrite yd_cr1 yd_cr7 yd_imm24. reflexivity.
Qed.

(* +0x1c  0x8526  c.mv a0,s1 *)
Lemma yddec_mv_a0_s1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8526 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Section WpYieldDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ---- prologue: 32-byte frame, saves ra/s0/s1 (shared podec_* decodes) ---- *)
  Lemma ydi_00 : kernel_text -∗ instr (mword_of_int (YD + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (YD + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (YD + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) podec_00 exec_execute_C_ADDI. Qed.

  Lemma ydi_02 : kernel_text -∗ instr (mword_of_int (YD + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (YD + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (YD + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) podec_02 exec_execute_C_SDSP. Qed.

  Lemma ydi_04 : kernel_text -∗ instr (mword_of_int (YD + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (YD + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (YD + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) podec_04 exec_execute_C_SDSP. Qed.

  Lemma ydi_06 : kernel_text -∗ instr (mword_of_int (YD + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (YD + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (YD + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) podec_06 exec_execute_C_SDSP. Qed.

  Lemma ydi_08 : kernel_text -∗ instr (mword_of_int (YD + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (YD + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (YD + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) podec_08 exec_execute_C_ADDI4SPN. Qed.

  (* ---- +0x0a: jal myproc ---- *)
  Lemma ydi_0a : kernel_text -∗ instr (mword_of_int (YD + 0x0a) : mword 64) false (JAL (mword_of_int 2095648 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (YD + 0x0a)%Z (mword_of_int 0xa21ff0ef : mword 32)
    (mword_of_int (YD + 0x0a) : mword 64) (JAL (mword_of_int 2095648 : mword 21, Regidx (mword_of_int 1))) yddec_jal_myproc. Qed.

  (* ---- +0x0e: c.mv s1,a0 ---- *)
  Lemma ydi_0e : kernel_text -∗ instr (mword_of_int (YD + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (YD + 0x0e)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (YD + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) yddec_mv_s1_a0 exec_execute_C_MV. Qed.

  (* ---- +0x10: jal acquire ---- *)
  Lemma ydi_10 : kernel_text -∗ instr (mword_of_int (YD + 0x10) : mword 64) false (JAL (mword_of_int 2092318 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (YD + 0x10)%Z (mword_of_int 0xd1ffe0ef : mword 32)
    (mword_of_int (YD + 0x10) : mword 64) (JAL (mword_of_int 2092318 : mword 21, Regidx (mword_of_int 1))) yddec_jal_acquire. Qed.

  (* ---- +0x14: c.li a5,3 ---- *)
  Lemma ydi_14 : kernel_text -∗ instr (mword_of_int (YD + 0x14) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (YD + 0x14)%Z (mword_of_int 0x478d : mword 16)
    (mword_of_int (YD + 0x14) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) yddec_li_a5_3 exec_execute_C_LI. Qed.

  (* ---- +0x16: c.sw a5,24(s1) ---- *)
  Lemma ydi_16 : kernel_text -∗ instr (mword_of_int (YD + 0x16) : mword 64) true (STORE (mword_of_int 24, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (YD + 0x16)%Z (mword_of_int 0xcc9c : mword 16)
    (mword_of_int (YD + 0x16) : mword 64) (STORE (mword_of_int 24, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) yddec_sw_a5_24 ydexec_sw24. Qed.

  (* ---- +0x18: jal sched ---- *)
  Lemma ydi_18 : kernel_text -∗ instr (mword_of_int (YD + 0x18) : mword 64) false (JAL (mword_of_int 2096940 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (YD + 0x18)%Z (mword_of_int 0xf2dff0ef : mword 32)
    (mword_of_int (YD + 0x18) : mword 64) (JAL (mword_of_int 2096940 : mword 21, Regidx (mword_of_int 1))) yddec_jal_sched. Qed.

  (* ---- +0x1c: c.mv a0,s1 ---- *)
  Lemma ydi_1c : kernel_text -∗ instr (mword_of_int (YD + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (YD + 0x1c)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (YD + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) yddec_mv_a0_s1 exec_execute_C_MV. Qed.

  (* ---- +0x1e: jal release ---- *)
  Lemma ydi_1e : kernel_text -∗ instr (mword_of_int (YD + 0x1e) : mword 64) false (JAL (mword_of_int 2092440 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (YD + 0x1e)%Z (mword_of_int 0xd99fe0ef : mword 32)
    (mword_of_int (YD + 0x1e) : mword 64) (JAL (mword_of_int 2092440 : mword 21, Regidx (mword_of_int 1))) yddec_jal_release. Qed.

  (* ---- +0x22..+0x26: c.ldsp ra/s0/s1 (shared podec_* decodes) ---- *)
  Lemma ydi_22 : kernel_text -∗ instr (mword_of_int (YD + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (YD + 0x22)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (YD + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) podec_22 exec_execute_C_LDSP. Qed.

  Lemma ydi_24 : kernel_text -∗ instr (mword_of_int (YD + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (YD + 0x24)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (YD + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) podec_24 exec_execute_C_LDSP. Qed.

  Lemma ydi_26 : kernel_text -∗ instr (mword_of_int (YD + 0x26) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (YD + 0x26)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (YD + 0x26) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) podec_26 exec_execute_C_LDSP. Qed.

  (* ---- +0x28: c.addi16sp sp,32 ---- *)
  Lemma ydi_28 : kernel_text -∗ instr (mword_of_int (YD + 0x28) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (YD + 0x28)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (YD + 0x28) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) podec_28 exec_execute_C_ADDI16SP. Qed.

  (* ---- +0x2a: c.ret ---- *)
  Lemma ydi_2a : kernel_text -∗ instr (mword_of_int (YD + 0x2a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (YD + 0x2a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (YD + 0x2a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) podec_2a exec_execute_C_JR. Qed.

End WpYieldDecode.
