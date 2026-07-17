(* ===================================================================== *)
(*  WpUartPutcSync.v                                                       *)
(*                                                                         *)
(*  Whole-function WP for uartputc_sync (0x80000962), the S-mode UART      *)
(*  synchronous putc.  It composes ordinary S-mode RAM/ALU/branch leaves   *)
(*  with the two native-kernel-PT device leaves (wp_lb_uart_s_kpt,         *)
(*  wp_sb_uart_s_kpt from WpUartKpt.v) under ONE plain [tlb_inv root_ppn]. *)
(*                                                                         *)
(*  This file first assembles the per-instruction [instr] decode facts     *)
(*  (mirroring WpKallocDecode.v) and two missing base leaves (LUI, ANDI),  *)
(*  then proves the device-core straight-line chunk (0x982 -> 0x99e) on    *)
(*  the THRE-ready path.                                                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes DevModel.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpDecodeBridge WpRvcBridge KernelText.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import KptPt SmodeCore.
Require Import WpMmodeLeafBase WpSmodeLeafBase.
Require Import WpAuipc.
Require Import WpSmodeItype WpSmodeBtype WpSmodeUtype WpSmodeLoad.
Require Import WpUart WpSmodeUart WpUartKpt.
Require Import CalleeSaved.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.

Import Defs.

(* ===================================================================== *)
(*  Per-instruction decode facts for the device-core instructions.        *)
(*  Base decodes go through [decode_bridge_ms]; RVC through [rvc_oneshot]. *)
(* ===================================================================== *)

(* 0x982  10000737  lui a4,0x10000 *)
Lemma updc_10000737 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10000737 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.

(* 0x988  00074783  lbu a5,0(a4) *)
Lemma updc_00074783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00074783 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x98c  0207f793  andi a5,a5,32 *)
Lemma updc_0207f793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0207f793 : mword 32)) s
  = Some (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x992  0ff4f513  zext.b a0,s1  (andi a0,s1,255) *)
Lemma updc_0ff4f513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0ff4f513 : mword 32)) s
  = Some (ITYPE (mword_of_int 255 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ANDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x996  100007b7  lui a5,0x10000 *)
Lemma updc_100007b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x100007b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.

(* 0x99a  00a78023  sb a0,0(a5) *)
Lemma updc_00a78023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00a78023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x986  0715  c.addi a4,a4,5 *)
Lemma uprvc_0715 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0715 : mword 16)) s
  = Some (C_ADDI (mword_of_int 5, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x990  dfe5  c.beqz a5,0x988  (offset -8) *)
Lemma uprvc_dfe5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xdfe5 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 252, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x96e / 0x99e  0000a797  auipc a5,0xa *)
Lemma updc_0000a797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0000a797 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x972  8b67a783  lw a5,-1866(a5)  (panicking) *)
Lemma updc_8b67a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8b67a783 : mword 32)) s
  = Some (LOAD (mword_of_int 0x8b6 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x976  cf95  c.beqz a5,0x9b2  (offset +60) *)
Lemma uprvc_cf95 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcf95 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 30, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x97c  8a87a783  lw a5,-1880(a5)  (panicked) *)
Lemma updc_8a87a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8a87a783 : mword 32)) s
  = Some (LOAD (mword_of_int 0x8a8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x980  ef85  c.bnez a5,0x9b8  (offset +56) *)
Lemma uprvc_ef85 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xef85 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 28, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x9a2  8867a783  lw a5,-1914(a5)  (panicking, 2nd read) *)
Lemma updc_8867a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8867a783 : mword 32)) s
  = Some (LOAD (mword_of_int 0x886 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x9a6  cb91  c.beqz a5,0x9ba  (offset +20) *)
Lemma uprvc_cb91 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcb91 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 10, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* compressed BEQZ -> base BTYPE BEQ execute bridge (local copy: the shared
   leaf base only exports the ADDI/LUI/etc. bridges, not C_BEQZ). *)
Lemma exec_execute_C_BEQZ (imm : mword 8) (rs : cregidx) s :
  exec (execute (C_BEQZ (imm, rs))) s
  = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg, creg2reg_idx rs, BEQ)), s).
Proof. unfold execute. cbn match. unfold execute_C_BEQZ. apply exec_returnM. Qed.

Section WpUartPutcSync.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* The three [instr]-builder templates, copied verbatim from WpMycpu.   *)
  (* ------------------------------------------------------------------- *)
  Notation UPS := KernelSyms.uartputc_sync.

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the eight device-core instructions (0x982-0x99a).  *)
  (* ------------------------------------------------------------------- *)
  Lemma upi_20 : kernel_text -∗ instr (mword_of_int (UPS + 0x20) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (UPS + 0x20)%Z (mword_of_int 0x10000737 : mword 32)
    (mword_of_int (UPS + 0x20) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 14), LUI)) updc_10000737. Qed.

  Lemma upi_24 : kernel_text -∗ instr (mword_of_int (UPS + 0x24) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (UPS + 0x24)%Z (mword_of_int 0x0715 : mword 16)
    (mword_of_int (UPS + 0x24) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) uprvc_0715 exec_execute_C_ADDI. Qed.

  Lemma upi_26 : kernel_text -∗ instr (mword_of_int (UPS + 0x26) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), true, 1)).
  Proof. mk_base (UPS + 0x26)%Z (mword_of_int 0x00074783 : mword 32)
    (mword_of_int (UPS + 0x26) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), true, 1)) updc_00074783. Qed.

  Lemma upi_2a : kernel_text -∗ instr (mword_of_int (UPS + 0x2a) : mword 64) false (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_base (UPS + 0x2a)%Z (mword_of_int 0x0207f793 : mword 32)
    (mword_of_int (UPS + 0x2a) : mword 64) (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) updc_0207f793. Qed.

  Lemma upi_2e : kernel_text -∗ instr (mword_of_int (UPS + 0x2e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (UPS + 0x2e)%Z (mword_of_int 0xdfe5 : mword 16)
    (mword_of_int (UPS + 0x2e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) uprvc_dfe5 exec_execute_C_BEQZ. Qed.

  Lemma upi_30 : kernel_text -∗ instr (mword_of_int (UPS + 0x30) : mword 64) false (ITYPE (mword_of_int 255 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ANDI)).
  Proof. mk_base (UPS + 0x30)%Z (mword_of_int 0x0ff4f513 : mword 32)
    (mword_of_int (UPS + 0x30) : mword 64) (ITYPE (mword_of_int 255 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ANDI)) updc_0ff4f513. Qed.

  Lemma upi_34 : kernel_text -∗ instr (mword_of_int (UPS + 0x34) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (UPS + 0x34)%Z (mword_of_int 0x100007b7 : mword 32)
    (mword_of_int (UPS + 0x34) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI)) updc_100007b7. Qed.

  Lemma upi_38 : kernel_text -∗ instr (mword_of_int (UPS + 0x38) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (UPS + 0x38)%Z (mword_of_int 0x00a78023 : mword 32)
    (mword_of_int (UPS + 0x38) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), 1)) updc_00a78023. Qed.

  (* --- panic-check instructions (0x96e auipc / 0x972 lw / 0x976 c.beqz) --- *)
  Lemma upi_0c : kernel_text -∗ instr (mword_of_int (UPS + 0x0c) : mword 64) false (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (UPS + 0x0c)%Z (mword_of_int 0x0000a797 : mword 32)
    (mword_of_int (UPS + 0x0c) : mword 64) (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)) updc_0000a797. Qed.

  Lemma upi_10 : kernel_text -∗ instr (mword_of_int (UPS + 0x10) : mword 64) false (LOAD (mword_of_int 0x8b6 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (UPS + 0x10)%Z (mword_of_int 0x8b67a783 : mword 32)
    (mword_of_int (UPS + 0x10) : mword 64) (LOAD (mword_of_int 0x8b6 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) updc_8b67a783. Qed.

  Lemma upi_14 : kernel_text -∗ instr (mword_of_int (UPS + 0x14) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 30 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (UPS + 0x14)%Z (mword_of_int 0xcf95 : mword 16)
    (mword_of_int (UPS + 0x14) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 30 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) uprvc_cf95 exec_execute_C_BEQZ. Qed.

  (* --- panicked-check (0x978 auipc / 0x97c lw / 0x980 c.bnez) --- *)
  Lemma upi_16 : kernel_text -∗ instr (mword_of_int (UPS + 0x16) : mword 64) false (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (UPS + 0x16)%Z (mword_of_int 0x0000a797 : mword 32)
    (mword_of_int (UPS + 0x16) : mword 64) (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)) updc_0000a797. Qed.

  Lemma upi_1a : kernel_text -∗ instr (mword_of_int (UPS + 0x1a) : mword 64) false (LOAD (mword_of_int 0x8a8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (UPS + 0x1a)%Z (mword_of_int 0x8a87a783 : mword 32)
    (mword_of_int (UPS + 0x1a) : mword 64) (LOAD (mword_of_int 0x8a8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) updc_8a87a783. Qed.

  Lemma upi_1e : kernel_text -∗ instr (mword_of_int (UPS + 0x1e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (UPS + 0x1e)%Z (mword_of_int 0xef85 : mword 16)
    (mword_of_int (UPS + 0x1e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) uprvc_ef85 exec_execute_C_BNEZ. Qed.

  (* --- 2nd panicking-check (0x99e auipc / 0x9a2 lw / 0x9a6 c.beqz) --- *)
  Lemma upi_3c : kernel_text -∗ instr (mword_of_int (UPS + 0x3c) : mword 64) false (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (UPS + 0x3c)%Z (mword_of_int 0x0000a797 : mword 32)
    (mword_of_int (UPS + 0x3c) : mword 64) (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)) updc_0000a797. Qed.

  Lemma upi_40 : kernel_text -∗ instr (mword_of_int (UPS + 0x40) : mword 64) false (LOAD (mword_of_int 0x886 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (UPS + 0x40)%Z (mword_of_int 0x8867a783 : mword 32)
    (mword_of_int (UPS + 0x40) : mword 64) (LOAD (mword_of_int 0x886 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) updc_8867a783. Qed.

  Lemma upi_44 : kernel_text -∗ instr (mword_of_int (UPS + 0x44) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (UPS + 0x44)%Z (mword_of_int 0xcb91 : mword 16)
    (mword_of_int (UPS + 0x44) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) uprvc_cb91 exec_execute_C_BEQZ. Qed.

  (* ------------------------------------------------------------------- *)
  (* Two base leaves missing from the S-mode leaf library: LUI and ANDI.  *)
  (* Both go through the base gpr-write engine + the register-generic      *)
  (* execute facts from WpMmodeLeafBase.                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_lui_s (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (UTYPE (imm, Regidx rd, LUI)) -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg root_ppn γ Φ pc rd rd rd
              (UTYPE (imm, Regidx rd, LUI))
              (luival imm)
              m (dq:=dq)
 Hrd
              _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc _ _.
    rewrite (exec_execute_UTYPE_LUI_gpr rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
  Qed.

  Lemma wp_andi_s (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg root_ppn γ Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ANDI))
              (and_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
              m (dq:=dq)
 Hrd
              _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ANDI_gpr rs1 rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_andi_val. rewrite Hva. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Two call-site-specialized device leaves: LSR read (off=5) and THR      *)
  (* write (off=0), with every constant PTE / geometry premise discharged.  *)
  (* The caller supplies only the config conditions and the fact that the   *)
  (* base register already holds the concrete UART register address.        *)
  (* ------------------------------------------------------------------- *)

  (* the byte the [lbu] leaf writes back when the read returns [uart_lsr u] *)
  Definition uart_lsr_ldval (u : uart_state) : mword 64 :=
    extend_value true (update_subrange_vec_dec (zeros' (1*1*8)) (1*(0+1)*8-1) (1*0*8) (uart_lsr u)).

  Lemma wp_uart_lsr_read_s (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5)
      (m : gmap regidx (mword 64)) (u : uart_state) {dq : dfrac} :
    uint rd <> 0 ->
    m !!! Regidx rs1 = uart_pa 5 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (LOAD (mword_of_int 0 : mword 12, Regidx rs1, Regidx rd, true, 1)) -∗
    uart_frag u -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (uart_lsr_ldval u)]> m) -∗
      uart_frag u -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Haddr)
      "Hsm Htlbinv Hpc Hfile Hinstr Huf Hcont".
    iApply (wp_lb_uart_s_kpt root_ppn γ 5 Φ pc false true rd rs1 (mword_of_int 0 : mword 12)
              (uart_lsr u) m u u (dq:=dq)

              ltac:(unfold uart_size; lia) Hrd
              ltac:(unfold PTE_DEV; lia)
              ltac:(intros; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              (update_PTE_Bits_kpt_dev (kpt_leaf_ppn uart_vpn) (Load Data))
              ltac:(rewrite Haddr; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(reflexivity)
              with "Hsm Htlbinv Hpc Hfile Hinstr Huf [Hcont]").
    unfold uart_lsr_ldval. iApply "Hcont".
  Qed.

  (* THRE-ready path: after [lbu (LSR)] + [andi ...,32], a5 masks to bit5 = 32,
     so the loop's [c.beqz a5] falls through. *)
  Lemma uart_thre_beqz (u : uart_state) :
    uart_thre u = true ->
    eq_vec (and_vec (uart_lsr_ldval u) (sign_extend' 64 (mword_of_int 32 : mword 12))) zero_reg = false.
  Proof.
    intro H. unfold uart_lsr_ldval, uart_lsr. rewrite H.
    destruct (uart_rx_ready u); vm_compute; reflexivity.
  Qed.

  Lemma wp_uart_thr_write_s (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5)
      (m : gmap regidx (mword 64)) (u u' : uart_state) {dq : dfrac} :
    m !!! Regidx rs1 = uart_pa 0 ->
    uart_write u 0 (autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = Some u' ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (STORE (mword_of_int 0 : mword 12, Regidx rs2, Regidx rs1, 1)) -∗
    uart_frag u -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      uart_frag u' -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Haddr Hwrite)
      "Hsm Htlbinv Hpc Hfile Hinstr Huf Hcont".
    iApply (wp_sb_uart_s_kpt root_ppn γ 0 Φ pc false rs2 rs1 (mword_of_int 0 : mword 12)
              m u u' (dq:=dq)

              ltac:(unfold uart_size; lia)
              ltac:(unfold PTE_DEV; lia)
              ltac:(intros; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              (update_PTE_Bits_kpt_dev (kpt_leaf_ppn uart_vpn) (Store Data))
              ltac:(rewrite Haddr; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              Hwrite
              with "Hsm Htlbinv Hpc Hfile Hinstr Huf Hcont").
  Qed.

  (* =================================================================== *)
  (*  DEVICE-CORE CHUNK: uartputc_sync 0x982 -> 0x99e, on the THRE-ready    *)
  (*  path (uart_thre u = true, so the poll loop falls through).            *)
  (*                                                                        *)
  (*    0x982  lui   a4,0x10000                                             *)
  (*    0x986  addi  a4,a4,5           (c.addi)                             *)
  (*    0x988  lbu   a5,0(a4)          -> LSR read (off 5)                  *)
  (*    0x98c  andi  a5,a5,32                                               *)
  (*    0x990  beqz  a5,0x988          (c.beqz, falls through)             *)
  (*    0x992  zext.b a0,s1            (andi a0,s1,255)                     *)
  (*    0x996  lui   a5,0x10000                                            *)
  (*    0x99a  sb    a0,0(a5)          -> THR write (off 0)                 *)
  (* =================================================================== *)

  (* intermediate register files, one per device-core instruction that
     writes a GPR (named to keep the WP threading readable, WpMycpu-style). *)
  Definition ppc_f1 (m : gmap regidx (mword 64)) : gmap regidx (mword 64) :=
    <[Regidx (mword_of_int 14) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> m.
  Definition ppc_f2 (m : gmap regidx (mword 64)) : gmap regidx (mword 64) :=
    <[Regidx (mword_of_int 14) := regval_into_reg (add_vec (ppc_f1 m !!! Regidx (mword_of_int 14))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> (ppc_f1 m).
  Definition ppc_f3 (m : gmap regidx (mword 64)) (u : uart_state) : gmap regidx (mword 64) :=
    <[Regidx (mword_of_int 15) := regval_into_reg (uart_lsr_ldval u)]> (ppc_f2 m).
  Definition ppc_f4 (m : gmap regidx (mword 64)) (u : uart_state) : gmap regidx (mword 64) :=
    <[Regidx (mword_of_int 15) := regval_into_reg (and_vec (ppc_f3 m u !!! Regidx (mword_of_int 15))
        (sign_extend' 64 (mword_of_int 32 : mword 12)))]> (ppc_f3 m u).
  Definition ppc_f5 (m : gmap regidx (mword 64)) (u : uart_state) : gmap regidx (mword 64) :=
    <[Regidx (mword_of_int 10) := regval_into_reg (and_vec (ppc_f4 m u !!! Regidx (mword_of_int 9))
        (sign_extend' 64 (mword_of_int 255 : mword 12)))]> (ppc_f4 m u).
  Definition ppc_f6 (m : gmap regidx (mword 64)) (u : uart_state) : gmap regidx (mword 64) :=
    <[Regidx (mword_of_int 15) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> (ppc_f5 m u).

  (* the three call-site register lookups the leaves need. *)
  Lemma ppc_f2_a4 (m : gmap regidx (mword 64)) :
    ppc_f2 m !!! Regidx (mword_of_int 14) = uart_pa 5.
  Proof.
    unfold ppc_f2, ppc_f1. rewrite !lookup_total_insert.
    apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma ppc_f4_a5 (m : gmap regidx (mword 64)) (u : uart_state) :
    uart_thre u = true ->
    eq_vec (ppc_f4 m u !!! Regidx (mword_of_int 15)) zero_reg = false.
  Proof.
    intro Hthre. unfold ppc_f4, ppc_f3. rewrite !lookup_total_insert.
    unfold regval_into_reg. apply uart_thre_beqz; exact Hthre.
  Qed.

  Lemma ppc_f6_a5 (m : gmap regidx (mword 64)) (u : uart_state) :
    ppc_f6 m u !!! Regidx (mword_of_int 15) = uart_pa 0.
  Proof.
    unfold ppc_f6. rewrite lookup_total_insert.
    apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma ppc_f6_a0 (m : gmap regidx (mword 64)) (u : uart_state) :
    ppc_f6 m u !!! Regidx (mword_of_int 10)
    = and_vec (m !!! Regidx (mword_of_int 9)) (sign_extend' 64 (mword_of_int 255 : mword 12)).
  Proof.
    unfold ppc_f6, ppc_f5, ppc_f4, ppc_f3, ppc_f2, ppc_f1.
    rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
    rewrite lookup_total_insert.
    do 4 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
    unfold regval_into_reg. reflexivity.
  Qed.

  Lemma wp_uartputc_devcore (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (u u' : uart_state) {dq : dfrac} :
    uart_thre u = true ->
    uart_write u 0 (autocast (T := mword)
       (subrange_vec_dec (and_vec (m !!! Regidx (mword_of_int 9))
          (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) : mword 8) = Some u' ->
    smode_config γ dq -∗
    tlb_inv root_ppn -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x20)) -∗ gpr_file m -∗ uart_frag u -∗
    ( smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (UPS + 0x3c)) -∗
      gpr_file (ppc_f6 m u) -∗
      uart_frag u' -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hthre Hwrite)
      "Hsm Htlbinv #Ht Hpc Hfile Huf Hcont".
    assert (P24 : add_vec_int (mword_of_int (UPS + 0x20) : mword 64) 4 = mword_of_int (UPS + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P26 : add_vec_int (mword_of_int (UPS + 0x24) : mword 64) 2 = mword_of_int (UPS + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P2a : add_vec_int (mword_of_int (UPS + 0x26) : mword 64) 4 = mword_of_int (UPS + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P2e : add_vec_int (mword_of_int (UPS + 0x2a) : mword 64) 4 = mword_of_int (UPS + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P30 : add_vec_int (mword_of_int (UPS + 0x2e) : mword 64) 2 = mword_of_int (UPS + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P34 : add_vec_int (mword_of_int (UPS + 0x30) : mword 64) 4 = mword_of_int (UPS + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P38 : add_vec_int (mword_of_int (UPS + 0x34) : mword 64) 4 = mword_of_int (UPS + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P3c : add_vec_int (mword_of_int (UPS + 0x38) : mword 64) 4 = mword_of_int (UPS + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iPoseProof (upi_20 with "Ht") as "Hi20".
    iPoseProof (upi_24 with "Ht") as "Hi24".
    iPoseProof (upi_26 with "Ht") as "Hi26".
    iPoseProof (upi_2a with "Ht") as "Hi2a".
    iPoseProof (upi_2e with "Ht") as "Hi2e".
    iPoseProof (upi_30 with "Ht") as "Hi30".
    iPoseProof (upi_34 with "Ht") as "Hi34".
    iPoseProof (upi_38 with "Ht") as "Hi38".
    (* 0x982  lui a4,0x10000 *)
    iApply (wp_lui_s root_ppn γ Φ (mword_of_int (UPS + 0x20)) (mword_of_int 14) (mword_of_int 0x10000 : mword 20)
              m (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi20").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P24) in "Hpc".
    (* 0x986  c.addi a4,a4,5 *)
    iApply (wp_caddi_gpr_s_config_scfg root_ppn γ Φ (mword_of_int (UPS + 0x24)) (mword_of_int 14) (mword_of_int 5 : mword 6)
              (ppc_f1 m) (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi24").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P26) in "Hpc".
    (* 0x988  lbu a5,0(a4)  -- LSR read *)
    iApply (wp_uart_lsr_read_s root_ppn γ Φ (mword_of_int (UPS + 0x26)) (mword_of_int 15) (mword_of_int 14)
              (ppc_f2 m) u (dq:=dq)
 ltac:(vm_compute; discriminate)
              (ppc_f2_a4 m)
              with "Hsm Htlbinv Hpc Hfile Hi26 Huf").
    iIntros "Hsm Htlbinv Hpc Hfile Huf".
    iEval (rewrite P2a) in "Hpc".
    (* 0x98c  andi a5,a5,32 *)
    iApply (wp_andi_s root_ppn γ Φ (mword_of_int (UPS + 0x2a)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 32 : mword 12)
              (ppc_f3 m u) (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi2a").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P2e) in "Hpc".
    (* 0x990  c.beqz a5,0x988  -- falls through (a5 = 32 != 0) *)
    iApply (wp_cbeqz_fall_s_config_scfg root_ppn γ Φ (mword_of_int (UPS + 0x2e)) (mword_of_int 252 : mword 8)
              (Cregidx (mword_of_int 7)) (mword_of_int 15) (ppc_f4 m u) (dq:=dq)

              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              (ppc_f4_a5 m u Hthre)
              with "Hsm Htlbinv Hpc Hfile Hi2e").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P30) in "Hpc".
    (* 0x992  zext.b a0,s1  (andi a0,s1,255) *)
    iApply (wp_andi_s root_ppn γ Φ (mword_of_int (UPS + 0x30)) (mword_of_int 10) (mword_of_int 9) (mword_of_int 255 : mword 12)
              (ppc_f4 m u) (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi30").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P34) in "Hpc".
    (* 0x996  lui a5,0x10000 *)
    iApply (wp_lui_s root_ppn γ Φ (mword_of_int (UPS + 0x34)) (mword_of_int 15) (mword_of_int 0x10000 : mword 20)
              (ppc_f5 m u) (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi34").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P38) in "Hpc".
    (* 0x99a  sb a0,0(a5)  -- THR write *)
    iApply (wp_uart_thr_write_s root_ppn γ Φ (mword_of_int (UPS + 0x38)) (mword_of_int 10) (mword_of_int 15)
              (ppc_f6 m u) u u' (dq:=dq)

              (ppc_f6_a5 m u)
              ltac:(rewrite ppc_f6_a0; exact Hwrite)
              with "Hsm Htlbinv Hpc Hfile Hi38 Huf").
    iIntros "Hsm Htlbinv Hpc Hfile Huf".
    iEval (rewrite P3c) in "Hpc".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Huf").
  Qed.

  (* =================================================================== *)
  (*  PANIC-CHECK CHUNK: uartputc_sync 0x96e -> 0x978.                     *)
  (*    0x96e  auipc a5,0xa                                                *)
  (*    0x972  lw    a5,-1866(a5)     -> read global `panicking`           *)
  (*    0x976  beqz  a5,0x9b2         (c.beqz; on panicking!=0 falls thru) *)
  (*  The global word is read from a persistent (DfracDiscarded) snapshot   *)
  (*  `panicking_pa ↦₄□ pv`, the read-only-global analogue of kernel_data;  *)
  (*  the caller asserts `pv` sign-extends to a nonzero value (panicking!=0)*)
  (*  so the branch falls through to the panicked check.                    *)
  (* =================================================================== *)
  Lemma wp_uartputc_panicking_check (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (pv : mword 32) {dq dqm : dfrac} :
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    smode_config γ dq -∗
    tlb_inv root_ppn -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x0c)) -∗ gpr_file m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    ( smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (UPS + 0x16)) -∗
      gpr_file (<[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pv)]>
               (<[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x0c)) (auipc_off (mword_of_int 0xa : mword 20)))]> m)) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpv)
      "Hsm Htlbinv #Ht Hpc Hfile Hsnap Hcont".
    assert (P10 : add_vec_int (mword_of_int (UPS + 0x0c) : mword 64) 4 = mword_of_int (UPS + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P14 : add_vec_int (mword_of_int (UPS + 0x10) : mword 64) 4 = mword_of_int (UPS + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P16 : add_vec_int (mword_of_int (UPS + 0x14) : mword 64) 2 = mword_of_int (UPS + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iPoseProof (upi_0c with "Ht") as "Hi0c".
    iPoseProof (upi_10 with "Ht") as "Hi10".
    iPoseProof (upi_14 with "Ht") as "Hi14".
    (* 0x96e auipc a5,0xa *)
    iApply (wp_auipc_s_scfg root_ppn γ Φ (mword_of_int (UPS + 0x0c)) (mword_of_int 15) (mword_of_int 0xa : mword 20)
              m (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi0c").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P10) in "Hpc".
    (* 0x972 lw a5,-1866(a5) : reads panicking; align the snapshot to the ea *)
    set (g1 := <[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x0c)) (auipc_off (mword_of_int 0xa : mword 20)))]> m).
    assert (Hea : add_vec (g1 !!! Regidx (mword_of_int 15)) (sign_extend' 64 (mword_of_int 0x8b6 : mword 12))
                  = (mword_of_int KernelSyms.panicking : mword 64)).
    { unfold g1. rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite <- Hea) in "Hsnap".
    iApply (wp_lw_s_ram_scfg root_ppn γ Φ (mword_of_int (UPS + 0x10)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 0x8b6 : mword 12)
              g1 pv (dq:=dq) (dqm:=dqm)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi10 Hsnap").
    iIntros "Hsm Htlbinv Hpc Hfile Hsnap".
    iEval (rewrite Hea) in "Hsnap".
    iEval (rewrite P14) in "Hpc".
    (* 0x976 c.beqz a5,0x9b2 : panicking != 0 -> falls through *)
    iApply (wp_cbeqz_fall_s_config_scfg root_ppn γ Φ (mword_of_int (UPS + 0x14)) (mword_of_int 30 : mword 8)
              (Cregidx (mword_of_int 7)) (mword_of_int 15)
              (<[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pv)]> g1)
              (dq:=dq)

              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite lookup_total_insert; exact Hpv)
              with "Hsm Htlbinv Hpc Hfile Hi14").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P16) in "Hpc".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hsnap").
  Qed.

  (* =================================================================== *)
  (*  PANICKED-CHECK CHUNK: 0x978 -> 0x982 (auipc · lw panicked · c.bnez).  *)
  (*  On the panic path panicked = 0, so the [c.bnez] falls through to the  *)
  (*  device core.  [pkv] sign-extends to 0.                                *)
  (* =================================================================== *)
  Lemma wp_uartputc_panicked_check (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (pkv : mword 32) {dq dqm : dfrac} :
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    smode_config γ dq -∗
    tlb_inv root_ppn -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x16)) -∗ gpr_file m -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm } pkv -∗
    ( smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (UPS + 0x20)) -∗
      gpr_file (<[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pkv)]>
               (<[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x16)) (auipc_off (mword_of_int 0xa : mword 20)))]> m)) -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm } pkv -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpkv)
      "Hsm Htlbinv #Ht Hpc Hfile Hsnap Hcont".
    assert (P1a : add_vec_int (mword_of_int (UPS + 0x16) : mword 64) 4 = mword_of_int (UPS + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P1e : add_vec_int (mword_of_int (UPS + 0x1a) : mword 64) 4 = mword_of_int (UPS + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P20 : add_vec_int (mword_of_int (UPS + 0x1e) : mword 64) 2 = mword_of_int (UPS + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iPoseProof (upi_16 with "Ht") as "Hi16".
    iPoseProof (upi_1a with "Ht") as "Hi1a".
    iPoseProof (upi_1e with "Ht") as "Hi1e".
    iApply (wp_auipc_s_scfg root_ppn γ Φ (mword_of_int (UPS + 0x16)) (mword_of_int 15) (mword_of_int 0xa : mword 20)
              m (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi16").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P1a) in "Hpc".
    set (g1 := <[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x16)) (auipc_off (mword_of_int 0xa : mword 20)))]> m).
    assert (Hea : add_vec (g1 !!! Regidx (mword_of_int 15)) (sign_extend' 64 (mword_of_int 0x8a8 : mword 12))
                  = (mword_of_int KernelSyms.panicked : mword 64)).
    { unfold g1. rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite <- Hea) in "Hsnap".
    iApply (wp_lw_s_ram_scfg root_ppn γ Φ (mword_of_int (UPS + 0x1a)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 0x8a8 : mword 12)
              g1 pkv (dq:=dq) (dqm:=dqm)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi1a Hsnap").
    iIntros "Hsm Htlbinv Hpc Hfile Hsnap".
    iEval (rewrite Hea) in "Hsnap".
    iEval (rewrite P1e) in "Hpc".
    iApply (wp_cbnez_fall_s_scfg root_ppn γ Φ (mword_of_int (UPS + 0x1e)) (mword_of_int 28 : mword 8)
              (Cregidx (mword_of_int 7)) (mword_of_int 15)
              (<[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pkv)]> g1)
              (dq:=dq)

              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite lookup_total_insert; exact Hpkv)
              with "Hsm Htlbinv Hpc Hfile Hi1e").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P20) in "Hpc".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hsnap").
  Qed.

  (* =================================================================== *)
  (*  2nd PANICKING-CHECK CHUNK: 0x99e -> 0x9a8 (auipc · lw panicking · beqz).*)
  (*  Reads the same [panicking] global; on the panic path it is nonzero so  *)
  (*  the [c.beqz] falls through to the epilogue.                            *)
  (* =================================================================== *)
  Lemma wp_uartputc_panicking_check2 (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (pv : mword 32) {dq dqm : dfrac} :
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    smode_config γ dq -∗
    tlb_inv root_ppn -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x3c)) -∗ gpr_file m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    ( smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (UPS + 0x46)) -∗
      gpr_file (<[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pv)]>
               (<[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x3c)) (auipc_off (mword_of_int 0xa : mword 20)))]> m)) -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpv)
      "Hsm Htlbinv #Ht Hpc Hfile Hsnap Hcont".
    assert (P40 : add_vec_int (mword_of_int (UPS + 0x3c) : mword 64) 4 = mword_of_int (UPS + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P44 : add_vec_int (mword_of_int (UPS + 0x40) : mword 64) 4 = mword_of_int (UPS + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P46 : add_vec_int (mword_of_int (UPS + 0x44) : mword 64) 2 = mword_of_int (UPS + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iPoseProof (upi_3c with "Ht") as "Hi3c".
    iPoseProof (upi_40 with "Ht") as "Hi40".
    iPoseProof (upi_44 with "Ht") as "Hi44".
    iApply (wp_auipc_s_scfg root_ppn γ Φ (mword_of_int (UPS + 0x3c)) (mword_of_int 15) (mword_of_int 0xa : mword 20)
              m (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi3c").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P40) in "Hpc".
    set (g1 := <[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x3c)) (auipc_off (mword_of_int 0xa : mword 20)))]> m).
    assert (Hea : add_vec (g1 !!! Regidx (mword_of_int 15)) (sign_extend' 64 (mword_of_int 0x886 : mword 12))
                  = (mword_of_int KernelSyms.panicking : mword 64)).
    { unfold g1. rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite <- Hea) in "Hsnap".
    iApply (wp_lw_s_ram_scfg root_ppn γ Φ (mword_of_int (UPS + 0x40)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 0x886 : mword 12)
              g1 pv (dq:=dq) (dqm:=dqm)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi40 Hsnap").
    iIntros "Hsm Htlbinv Hpc Hfile Hsnap".
    iEval (rewrite Hea) in "Hsnap".
    iEval (rewrite P44) in "Hpc".
    iApply (wp_cbeqz_fall_s_config_scfg root_ppn γ Φ (mword_of_int (UPS + 0x44)) (mword_of_int 10 : mword 8)
              (Cregidx (mword_of_int 7)) (mword_of_int 15)
              (<[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pv)]> g1)
              (dq:=dq)

              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite lookup_total_insert; exact Hpv)
              with "Hsm Htlbinv Hpc Hfile Hi44").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P46) in "Hpc".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hsnap").
  Qed.

  (* =================================================================== *)
  (*  THE BODY: uartputc_sync 0x96e -> 0x9a8 (post-prologue to pre-epilogue) *)
  (*  on the panic path (panicking != 0, panicked = 0), THRE ready.         *)
  (*  Chains the four body chunks under one plain [tlb_inv].                 *)
  (* =================================================================== *)
  Lemma wp_uartputc_body (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (u u' : uart_state) (pv pkv : mword 32)
      {dq dqm dqm2 : dfrac} :
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    uart_thre u = true ->
    uart_write u 0 (autocast (T := mword)
       (subrange_vec_dec (and_vec (m !!! Regidx (mword_of_int 9))
          (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) : mword 8) = Some u' ->
    smode_config γ dq -∗
    tlb_inv root_ppn -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x0c)) -∗ gpr_file m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    uart_frag u -∗
    ( ∀ mf,
      smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (UPS + 0x46)) -∗
      gpr_file mf -∗
      ⌜ callee_saved m mf ⌝ -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_frag u' -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpv Hpkv Hthre Hwrite)
      "Hsm Htlbinv #Ht Hpc Hfile Hpk Hpkd Huf Hcont".
    (* 0x96e -> 0x978 : panicking check (falls through) *)
    iApply (wp_uartputc_panicking_check root_ppn γ Φ m pv (dq:=dq) (dqm:=dqm)
 Hpv
              with "Hsm Htlbinv Ht Hpc Hfile Hpk").
    iIntros "Hsm Htlbinv Hpc Hfile Hpk".
    set (f1 := <[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pv)]>
               (<[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x0c)) (auipc_off (mword_of_int 0xa : mword 20)))]> m)).
    (* 0x978 -> 0x982 : panicked check (falls through) *)
    iApply (wp_uartputc_panicked_check root_ppn γ Φ f1 pkv (dq:=dq) (dqm:=dqm2)
 Hpkv
              with "Hsm Htlbinv Ht Hpc Hfile Hpkd").
    iIntros "Hsm Htlbinv Hpc Hfile Hpkd".
    set (f2 := <[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pkv)]>
               (<[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x16)) (auipc_off (mword_of_int 0xa : mword 20)))]> f1)).
    assert (HR9 : f2 !!! Regidx (mword_of_int 9) = m !!! Regidx (mword_of_int 9)).
    { unfold f2, f1. do 4 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]). reflexivity. }
    (* 0x982 -> 0x99e : device core (LSR read + THR write) *)
    iApply (wp_uartputc_devcore root_ppn γ Φ f2 u u' (dq:=dq)
 Hthre
              ltac:(rewrite HR9; exact Hwrite)
              with "Hsm Htlbinv Ht Hpc Hfile Huf").
    iIntros "Hsm Htlbinv Hpc Hfile Huf".
    (* 0x99e -> 0x9a8 : 2nd panicking check (falls through) *)
    iApply (wp_uartputc_panicking_check2 root_ppn γ Φ (ppc_f6 f2 u) pv (dq:=dq) (dqm:=dqm)
 Hpv
              with "Hsm Htlbinv Ht Hpc Hfile Hpk").
    iIntros "Hsm Htlbinv Hpc Hfile Hpk".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile [%] Hpk Hpkd Huf").
    (* The body writes only a4/a5/a0, none of them callee-saved, so every
       callee-saved register still holds its entry value. *)
    unfold callee_saved.
    repeat split; unfold ppc_f6, ppc_f5, ppc_f4, ppc_f3, ppc_f2, ppc_f1, f2, f1;
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); reflexivity.
  Qed.

End WpUartPutcSync.
