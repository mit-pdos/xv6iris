(* WpUartPutcSyncFull.v -- the prologue/epilogue frame handling for
   uartputc_sync, on top of the body [wp_uartputc_body] (WpUartPutcSync.v),
   assembled into the whole-function WP [wp_uartputc].

   The prologue's three stack STORES (c.sdsp) and the epilogue's three stack
   LOADS (c.ldsp) have only [_scfg] (smode_config) leaves, so they are run
   through the VCgen (VcGenS.v) as [vop_s] blocks -- exactly as WpMycpu.v runs
   its prologue/epilogue.  The three instructions that are neither ordinary
   value-ALU ops nor stack-slot VCgen ops are handled by dedicated [_scfg]
   leaves (each threads the same [smode_config] bundle):
     - c.mv  s1,a0     (0x96c) : [wp_cmv_gpr_s_config_scfg_pt] (WpSmodeRtype)
     - c.addi16sp sp,32 (0x9ae): [wp_caddi16sp_gpr_s_pt]       (WpSmodeGpr; +32
       is out of c.addi's range so it cannot be folded into the VCgen block)
     - c.ret           (0x9b0) : [wp_cret_s_zca_scfg_pt]       (WpSmodeJalr) *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpUart.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.

Notation UPS := KernelSyms.uartputc_sync.

(* ===================================================================== *)
(*  Decode facts for the three "structural" RVC instructions that are not  *)
(*  in the device-core / panic-check set.  (c.ret reuses [cdec_8082].)      *)
(* ===================================================================== *)

Section WpUartPutcSyncFull.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ}.
  Context `{CID : CpuId}.

  (* [instr]-builder templates, copied verbatim from WpUartPutcSync.v. *)
  (* --- [instr] facts for the three structural RVC instructions --- *)
  Lemma upi_0a : kernel_text -∗ instr (mword_of_int (UPS + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (UPS + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (UPS + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma upi_4c : kernel_text -∗ instr (mword_of_int (UPS + 0x4c) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2), sp, sp, ADDI)).
  Proof. mk_rvc (UPS + 0x4c)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (UPS + 0x4c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma upi_4e : kernel_text -∗ instr (mword_of_int (UPS + 0x4e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (UPS + 0x4e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (UPS + 0x4e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- prologue frame [instr] facts (0x00 c.addi · 0x02/04/06 sd · 0x08 addi4spn) --- *)
  Lemma upi_00 : kernel_text -∗ instr (mword_of_int (UPS + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (UPS + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (UPS + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma upi_02 : kernel_text -∗ instr (mword_of_int (UPS + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (UPS + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (UPS + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma upi_04 : kernel_text -∗ instr (mword_of_int (UPS + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (UPS + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (UPS + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma upi_06 : kernel_text -∗ instr (mword_of_int (UPS + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (UPS + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (UPS + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma upi_08 : kernel_text -∗ instr (mword_of_int (UPS + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (UPS + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (UPS + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* --- epilogue frame [instr] facts (0x46/48/4a ld) --- *)
  Lemma upi_46 : kernel_text -∗ instr (mword_of_int (UPS + 0x46) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (UPS + 0x46)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (UPS + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma upi_48 : kernel_text -∗ instr (mword_of_int (UPS + 0x48) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (UPS + 0x48)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (UPS + 0x48) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma upi_4a : kernel_text -∗ instr (mword_of_int (UPS + 0x4a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (UPS + 0x4a)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (UPS + 0x4a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

End WpUartPutcSyncFull.
