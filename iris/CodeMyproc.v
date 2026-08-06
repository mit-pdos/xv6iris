(* CodeMyproc.v -- decode templates + [instr] facts for myproc()'s 21
   instructions at KernelSyms.myproc = 0x80001904.

   myproc's 32-byte frame prologue/epilogue (c.addi sp,-32 / three c.sdsp /
   c.addi4spn / three c.ldsp / c.addi16sp / c.ret) is byte-identical to
   acquire's, so its decodes reuse the shared [cdec_*] templates from
   KernelRvcDecode.v; the a5-materialization triple (c.mv a5,tp / c.addiw /
   c.slli a5,7) is byte-identical to mycpu's, reusing [cdec_8792]/[cdec_2781]/
   [cdec_079e] from CodeMycpu.v.  Only the two jal's, the auipc/addi pid_lock
   materialization, the c.add and c.ld, and the two other c.mv's are myproc's
   own and get fresh templates here. *)
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


(* ===================================================================== *)
(* Fresh decode templates (bit patterns unique to myproc).                *)
(* ===================================================================== *)

(* +0x0a  0xac0ff0ef  jal ra,push_off (target 0x80000bce) *)
Lemma mpdec_jal_pushoff s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xac0ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093760 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x22  0xb22ff0ef  jal ra,pop_off (target 0x80000c48) *)
Lemma mpdec_jal_popoff s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb22ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093858 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.


(* +0x18  0xa3070713  addi a4,a4,-1488  (= 0xa30 as a 12-bit residue) *)
Lemma mpdec_addi s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa3070713 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xa30 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x1e  0x7b9c  c.ld a5,48(a5) *)
Lemma mpdec_ld s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7b9c : mword 16)) s
  = Some (C_LD (mword_of_int 6, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Section CodeMyproc.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- prologue: 32-byte frame, saves ra/s0/s1 (shared cdec_* decodes) ---- *)
  Lemma mpi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.myproc + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma mpi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.myproc + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma mpi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.myproc + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma mpi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.myproc + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma mpi_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.myproc + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* ---- +0x0a: jal push_off ---- *)
  Lemma mpi_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x0a) : mword 64) false (JAL (mword_of_int 2093760 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.myproc + 0x0a)%Z (mword_of_int 0xac0ff0ef : mword 32)
    (mword_of_int (KernelSyms.myproc + 0x0a) : mword 64) (JAL (mword_of_int 2093760 : mword 21, Regidx (mword_of_int 1))) mpdec_jal_pushoff. Qed.

  (* ---- +0x0e..+0x12: c.mv a5,tp / c.addiw a5,0 / c.slli a5,7 (mycpu decodes) ---- *)
  Lemma mpi_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (KernelSyms.myproc + 0x0e)%Z (mword_of_int 0x8792 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)) cdec_8792 exec_execute_C_MV. Qed.

  Lemma mpi_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x10) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (KernelSyms.myproc + 0x10)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x10) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2781 exec_execute_C_ADDIW. Qed.

  Lemma mpi_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x12) : mword 64) true (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (KernelSyms.myproc + 0x12)%Z (mword_of_int 0x079e : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x12) : mword 64) (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_079e exec_execute_C_SLLI. Qed.

  (* ---- +0x14: auipc a4,0x11 ---- *)
  Lemma mpi_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x14) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (KernelSyms.myproc + 0x14)%Z (mword_of_int 0x00011717 : mword 32)
    (mword_of_int (KernelSyms.myproc + 0x14) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 14), AUIPC)) bdec_00011717. Qed.

  (* ---- +0x18: addi a4,a4,-1488 ---- *)
  Lemma mpi_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x18) : mword 64) false (ITYPE (mword_of_int 0xa30 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (KernelSyms.myproc + 0x18)%Z (mword_of_int 0xa3070713 : mword 32)
    (mword_of_int (KernelSyms.myproc + 0x18) : mword 64) (ITYPE (mword_of_int 0xa30 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) mpdec_addi. Qed.

  (* ---- +0x1c: c.add a5,a5,a4 ---- *)
  Lemma mpi_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (KernelSyms.myproc + 0x1c)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97ba exec_execute_C_ADD. Qed.

  (* ---- +0x1e: c.ld a5,48(a5) ---- *)
  Lemma mpi_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (KernelSyms.myproc + 0x1e)%Z (mword_of_int 0x7b9c : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) mpdec_ld exec_execute_C_LD. Qed.

  (* ---- +0x20: c.mv s1,a5 (shared cdec_84be) ---- *)
  Lemma mpi_20 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x20) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.myproc + 0x20)%Z (mword_of_int 0x84be : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)) cdec_84be exec_execute_C_MV. Qed.

  (* ---- +0x22: jal pop_off ---- *)
  Lemma mpi_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x22) : mword 64) false (JAL (mword_of_int 2093858 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.myproc + 0x22)%Z (mword_of_int 0xb22ff0ef : mword 32)
    (mword_of_int (KernelSyms.myproc + 0x22) : mword 64) (JAL (mword_of_int 2093858 : mword 21, Regidx (mword_of_int 1))) mpdec_jal_popoff. Qed.

  (* ---- +0x26: c.mv a0,s1 ---- *)
  Lemma mpi_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x26) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.myproc + 0x26)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x26) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* ---- +0x28..+0x2c: c.ldsp ra/s0/s1 (shared cdec_* decodes) ---- *)
  Lemma mpi_28 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x28) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.myproc + 0x28)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma mpi_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.myproc + 0x2a)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma mpi_2c : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.myproc + 0x2c)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  (* ---- +0x2e: c.addi16sp sp,32 ---- *)
  Lemma mpi_2e : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x2e) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.myproc + 0x2e)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x2e) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  (* ---- +0x30: c.ret ---- *)
  Lemma mpi_30 : kernel_text -∗ instr (mword_of_int (KernelSyms.myproc + 0x30) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.myproc + 0x30)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.myproc + 0x30) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeMyproc.
