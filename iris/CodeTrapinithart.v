(* CodeTrapinithart.v -- decode templates + [instr] facts for
   trapinithart() (kernel/trap.c) at KernelSyms.trapinithart = 0x80002426.

   trapinithart's body is w_stvec((uint64)kernelvec) inside the standard
   16-byte frame, so eight of its eleven instructions are the shared
   bit-keyed [cdec_<word>] prologue/epilogue templates from
   KernelRvcDecode.v.  Its own three words -- the auipc/addi pair that
   materializes &kernelvec (0x80005420) and the csrw stvec,a5 that installs
   it -- get fresh [tidec_*] templates here. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpGprCsrwB.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

Notation TIH := KernelSyms.trapinithart.

(* ===================================================================== *)
(* Fresh decode templates (bit patterns unique to trapinithart).          *)
(* ===================================================================== *)

(* +0x08  0x00003797  auipc a5,0x3      (&kernelvec, high half) *)
Lemma tidec_auipc_a5 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00003797 : mword 32)) s
  = Some (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* +0x0c  0xff278793  addi a5,a5,-14    -- a5 := kernelvec (0x80005420) *)
Lemma tidec_addi_a5 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xff278793 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xff2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x10  0x10579073  csrw stvec,a5 *)
Lemma tidec_csrw_stvec s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10579073 : mword 32)) s
  = Some (CSRReg (csr_stvec, Regidx (mword_of_int 15), zreg, CSRRW), s).
Proof. decode_bridge_ms. Qed.

Section CodeTrapinithart.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- prologue: 16-byte frame, saves ra/s0 (shared cdec_* decodes) ---- *)
  Lemma tii_00 : kernel_text -∗ instr (mword_of_int (TIH + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (TIH + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (TIH + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma tii_02 : kernel_text -∗ instr (mword_of_int (TIH + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (TIH + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (TIH + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma tii_04 : kernel_text -∗ instr (mword_of_int (TIH + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (TIH + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (TIH + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma tii_06 : kernel_text -∗ instr (mword_of_int (TIH + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (TIH + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (TIH + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  (* ---- the body: a5 := &kernelvec ; csrw stvec,a5 ---- *)
  Lemma tii_08 : kernel_text -∗ instr (mword_of_int (TIH + 0x08) : mword 64) false (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (TIH + 0x08)%Z (mword_of_int 0x00003797 : mword 32)
    (mword_of_int (TIH + 0x08) : mword 64) (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 15), AUIPC)) tidec_auipc_a5. Qed.

  Lemma tii_0c : kernel_text -∗ instr (mword_of_int (TIH + 0x0c) : mword 64) false (ITYPE (mword_of_int 0xff2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (TIH + 0x0c)%Z (mword_of_int 0xff278793 : mword 32)
    (mword_of_int (TIH + 0x0c) : mword 64) (ITYPE (mword_of_int 0xff2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) tidec_addi_a5. Qed.

  Lemma tii_10 : kernel_text -∗ instr (mword_of_int (TIH + 0x10) : mword 64) false (CSRReg (csr_stvec, Regidx (mword_of_int 15), zreg, CSRRW)).
  Proof. mk_base (TIH + 0x10)%Z (mword_of_int 0x10579073 : mword 32)
    (mword_of_int (TIH + 0x10) : mword 64) (CSRReg (csr_stvec, Regidx (mword_of_int 15), zreg, CSRRW)) tidec_csrw_stvec. Qed.

  (* ---- epilogue: restore ra/s0, frame pop, ret (shared cdec_* words) ---- *)
  Lemma tii_14 : kernel_text -∗ instr (mword_of_int (TIH + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (TIH + 0x14)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (TIH + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma tii_16 : kernel_text -∗ instr (mword_of_int (TIH + 0x16) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (TIH + 0x16)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (TIH + 0x16) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma tii_18 : kernel_text -∗ instr (mword_of_int (TIH + 0x18) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (TIH + 0x18)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (TIH + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma tii_1a : kernel_text -∗ instr (mword_of_int (TIH + 0x1a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (TIH + 0x1a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (TIH + 0x1a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeTrapinithart.
