(* ===================================================================== *)
(*  WpUartPutcSync.v                                                       *)
(*                                                                         *)
(*  Whole-function WP for uartputc_sync (0x80000962), the S-mode UART      *)
(*  synchronous putc.  It composes ordinary S-mode RAM/ALU/branch leaves   *)
(*  with the two native-kernel-PT device leaves (wp_lb_uart_s_pt,         *)
(*  wp_sb_uart_s_pt from WpUartKpt.v) under ONE plain [tlb_inv_pt root_ppn]. *)
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
Require Import DevModel.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecodeBridge WpRvcBridge KernelText.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import WpMmodeLeafBase.
Require Import WpAuipc.
Require Import WpUart.
Require Import CalleeSaved.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.

Require Import KptTree.
Require Import SRegime.
Require Import WpSmodePtLeaves WpSmodePtAlu WpSmodePtBtype.
Require Import WpSmodePtMemWrap WpSmodePtUart.
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

(* 0x972  8a87a783  lw a5,-1880(a5)  (panicking) *)
Lemma updc_8a87a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8a87a783 : mword 32)) s
  = Some (LOAD (mword_of_int 0x8a8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x976  cf95  c.beqz a5,0x9b2  (offset +60) *)
Lemma uprvc_cf95 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcf95 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 30, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x97c  8a87a783  lw a5,-1894(a5)  (panicked) *)
Lemma updc_89a7a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x89a7a783 : mword 32)) s
  = Some (LOAD (mword_of_int 0x89a : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x980  ef85  c.bnez a5,0x9b8  (offset +56) *)
Lemma uprvc_ef85 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xef85 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 28, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x9a2  8787a783  lw a5,-1928(a5)  (panicking, 2nd read) *)
Lemma updc_8787a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8787a783 : mword 32)) s
  = Some (LOAD (mword_of_int 0x878 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
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
  (* the device leaves open [dev_inv], whose ghosts need this *)
  Context `{!uartGhostG Σ}.
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

  Lemma upi_10 : kernel_text -∗ instr (mword_of_int (UPS + 0x10) : mword 64) false (LOAD (mword_of_int 0x8a8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (UPS + 0x10)%Z (mword_of_int 0x8a87a783 : mword 32)
    (mword_of_int (UPS + 0x10) : mword 64) (LOAD (mword_of_int 0x8a8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) updc_8a87a783. Qed.

  Lemma upi_14 : kernel_text -∗ instr (mword_of_int (UPS + 0x14) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 30 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (UPS + 0x14)%Z (mword_of_int 0xcf95 : mword 16)
    (mword_of_int (UPS + 0x14) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 30 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) uprvc_cf95 exec_execute_C_BEQZ. Qed.

  (* --- panicked-check (0x978 auipc / 0x97c lw / 0x980 c.bnez) --- *)
  Lemma upi_16 : kernel_text -∗ instr (mword_of_int (UPS + 0x16) : mword 64) false (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (UPS + 0x16)%Z (mword_of_int 0x0000a797 : mword 32)
    (mword_of_int (UPS + 0x16) : mword 64) (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)) updc_0000a797. Qed.

  Lemma upi_1a : kernel_text -∗ instr (mword_of_int (UPS + 0x1a) : mword 64) false (LOAD (mword_of_int 0x89a : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (UPS + 0x1a)%Z (mword_of_int 0x89a7a783 : mword 32)
    (mword_of_int (UPS + 0x1a) : mword 64) (LOAD (mword_of_int 0x89a : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) updc_89a7a783. Qed.

  Lemma upi_1e : kernel_text -∗ instr (mword_of_int (UPS + 0x1e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (UPS + 0x1e)%Z (mword_of_int 0xef85 : mword 16)
    (mword_of_int (UPS + 0x1e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) uprvc_ef85 exec_execute_C_BNEZ. Qed.

  (* --- 2nd panicking-check (0x99e auipc / 0x9a2 lw / 0x9a6 c.beqz) --- *)
  Lemma upi_3c : kernel_text -∗ instr (mword_of_int (UPS + 0x3c) : mword 64) false (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (UPS + 0x3c)%Z (mword_of_int 0x0000a797 : mword 32)
    (mword_of_int (UPS + 0x3c) : mword 64) (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)) updc_0000a797. Qed.

  Lemma upi_40 : kernel_text -∗ instr (mword_of_int (UPS + 0x40) : mword 64) false (LOAD (mword_of_int 0x878 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (UPS + 0x40)%Z (mword_of_int 0x8787a783 : mword 32)
    (mword_of_int (UPS + 0x40) : mword 64) (LOAD (mword_of_int 0x878 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) updc_8787a783. Qed.

  Lemma upi_44 : kernel_text -∗ instr (mword_of_int (UPS + 0x44) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (UPS + 0x44)%Z (mword_of_int 0xcb91 : mword 16)
    (mword_of_int (UPS + 0x44) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) uprvc_cb91 exec_execute_C_BEQZ. Qed.

  (* ------------------------------------------------------------------- *)
  (* Two base leaves missing from the S-mode leaf library: LUI and ANDI.  *)
  (* Both go through the base gpr-write engine + the register-generic      *)
  (* execute facts from WpMmodeLeafBase.                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_lui_s_r (Rg : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv Rg -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (UTYPE (imm, Regidx rd, LUI)) -∗
    ( smode_config γ dq -∗ sr_inv Rg -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg_regime Rg γ Φ pc rd rd rd
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


  Lemma wp_andi_s_r (Rg : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv Rg -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) -∗
    ( smode_config γ dq -∗ sr_inv Rg -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg_regime Rg γ Φ pc rd rs1 rs1
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

  (* the value the [lbu] leaf writes back for a read byte [b].  The device
     state is shared, so the poll cannot name the byte in advance: everything
     downstream is phrased in terms of [b] and only re-connected to the UART
     inside the leaf's ghost step. *)
  Definition lsr_ldval_of (b : bv 8) : mword 64 :=
    extend_value true (update_subrange_vec_dec (zeros' (1*1*8)) (1*(0+1)*8-1) (1*0*8) b).

  (* the byte the [lbu] leaf writes back when the read returns [uart_lsr u] *)
  Definition uart_lsr_ldval (u : uart_state) : mword 64 := lsr_ldval_of (uart_lsr u).

  (* THE POLL'S BRANCH TEST, as a function of the read byte: [andi a5,a5,32]
     then [c.beqz a5].  True = THRE clear = branch taken = spin again. *)
  Definition lsr_thre_clear (b : bv 8) : bool :=
    eq_vec (and_vec (lsr_ldval_of b) (sign_extend' 64 (mword_of_int 32 : mword 12))) zero_reg.

  (* THRE-ready path: after [lbu (LSR)] + [andi ...,32], a5 masks to bit5 = 32,
     so the loop's [c.beqz a5] falls through. *)
  Lemma uart_thre_beqz (u : uart_state) :
    uart_thre u = true -> lsr_thre_clear (uart_lsr u) = false.
  Proof.
    intro H. unfold lsr_thre_clear, lsr_ldval_of, uart_lsr. rewrite H.
    destruct (uart_rx_ready u); vm_compute; reflexivity.
  Qed.

  (* the converse: THRE clear really does take the branch, so the two cases of
     the poll are exactly [uart_thre u] *)
  Lemma uart_nothre_beqz (u : uart_state) :
    uart_thre u = false -> lsr_thre_clear (uart_lsr u) = true.
  Proof.
    intro H. unfold lsr_thre_clear, lsr_ldval_of, uart_lsr. rewrite H.
    destruct (uart_rx_ready u); vm_compute; reflexivity.
  Qed.

  (* The THR write.  This is where the whole ghost design pays off: the caller
     brings the transmitter token, the out-bound the poll handed back, and the
     frozen DLAB fact; [uart_tx_ready_persists] turns them into
     [uart_write_thr_acc]'s two premises AT THE WRITE'S OWN STATE, so the byte
     provably lands in the FIFO rather than being dropped.  The postcondition
     is the grown token plus a permanent [uart_sent] record. *)
  (* The LSR poll's load.  Takes [dev_inv] + the transmitter token; hands back
     the token and -- IF the read byte says THRE was set -- the [uart_out_lb]
     bound that makes the observation survive to the later THR write
     ([uart_tx_ready_persists], WpUart.v). *)
  Lemma wp_uart_lsr_read_s_r (Rg : s_regime) (γ : gname) (γd : uart_names)
      (Φ : mval -> iProp Σ) (pc : mword 64) (rd rs1 : mword 5)
      (m : gmap regidx (mword 64)) (l : list (bv 8)) {dq : dfrac} :
    uint rd <> 0 ->
    m !!! Regidx rs1 = uart_pa 5 ->
    smode_config γ dq -∗ sr_inv Rg -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (LOAD (mword_of_int 0 : mword 12, Regidx rs1, Regidx rd, true, 1)) -∗
    dev_inv γd -∗ uart_tx_own γd l -∗
    ( ∀ b : bv 8,
      smode_config γ dq -∗ sr_inv Rg -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (lsr_ldval_of b)]> m) -∗
      uart_tx_own γd l -∗
      (⌜ lsr_thre_clear b = false ⌝ -∗ uart_out_lb γd l) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Haddr)
      "Hsm Htlbinv Hpc Hfile Hinstr #Hdinv Hown Hcont".
    iApply (wp_lb_uart_s_r Rg γ γd 5 Φ pc false true rd rs1 (mword_of_int 0 : mword 12)
              m (uart_tx_own γd l)
              (fun b => uart_tx_own γd l ∗ (⌜ lsr_thre_clear b = false ⌝ -∗ uart_out_lb γd l))%I
              (dq:=dq)

              ltac:(unfold uart_size; lia) Hrd
              ltac:(rewrite Haddr; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              with "Hsm Htlbinv Hpc Hfile Hinstr Hdinv Hown [] [Hcont]").
    - (* the ghost step, run with [dev_inv] open: the LSR read is a pure
         observation, so every ghost carries over unchanged; if THRE was set
         we additionally extract the out-bound. *)
      iIntros (u b u') "%Hread Hg Hown".
      rewrite uart_read_lsr in Hread. injection Hread as <- <-.
      iDestruct "Hg" as "(Hs & Hout & Htx & Hdl)".
      destruct (uart_thre u) eqn:Hthre.
      + iDestruct (uart_tx_poll_thre γd u l Hthre with "Hown Htx Hout")
          as "(Hown & Htx & Hout & #Hlb & %Hfacts)".
        iModIntro. iFrame "Hs Hout Htx Hdl Hown". iIntros (_). iExact "Hlb".
      + iModIntro. iFrame "Hs Hout Htx Hdl Hown".
        iIntros (Hc). rewrite (uart_nothre_beqz u Hthre) in Hc. discriminate.
    - iIntros (b) "Hsm Htlbinv Hpc Hfile [Hown Hlb]".
      iApply ("Hcont" $! b with "Hsm Htlbinv Hpc Hfile Hown Hlb").
  Qed.


  Lemma wp_uart_thr_write_s_r (Rg : s_regime) (γ : gname) (γd : uart_names)
      (Φ : mval -> iProp Σ) (pc : mword 64) (rs2 rs1 : mword 5)
      (m : gmap regidx (mword 64)) (l : list (bv 8)) {dq : dfrac} :
    m !!! Regidx rs1 = uart_pa 0 ->
    smode_config γ dq -∗ sr_inv Rg -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (STORE (mword_of_int 0 : mword 12, Regidx rs2, Regidx rs1, 1)) -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_out_lb γd l -∗ uart_dlab_off γd -∗
    ( smode_config γ dq -∗ sr_inv Rg -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      uart_tx_own γd (l ++ [autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8]) -∗
      uart_sent γd (l ++ [autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8]) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Haddr)
      "Hsm Htlbinv Hpc Hfile Hinstr #Hdinv Hown #Hlb #Hoff Hcont".
    set (sb := autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8).
    iApply (wp_sb_uart_s_r Rg γ γd 0 Φ pc false rs2 rs1 (mword_of_int 0 : mword 12)
              m (uart_tx_own γd l)
              (uart_tx_own γd (l ++ [sb]) ∗ uart_sent γd (l ++ [sb]))%I
              (dq:=dq)

              ltac:(unfold uart_size; lia)
              ltac:(rewrite Haddr; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              with "Hsm Htlbinv Hpc Hfile Hinstr Hdinv Hown [] [Hcont]").
    - (* the ghost step, with [dev_inv] open at the write's OWN state [u] *)
      iIntros (u u') "%Hwrite Hg Hown".
      iDestruct "Hg" as "(Hs & Hout & Htx & Hdl)".
      (* the poll's observation still holds HERE -- this is the payoff: the
         token pins uart_acc u = l and the out-bound says l is all transmitted,
         so at THIS state the FIFO is empty and (frozen) DLAB is clear *)
      iDestruct (uart_tx_ready_persists γd u l
                   with "Hown Hlb Hoff Htx Hout Hdl") as %[Hempty Hdlab].
      iDestruct (uart_tx_own_agree with "Htx Hown") as %Haccu.
      (* so the FIFO has room, and the accepted trace grows by exactly [sb] *)
      assert (Hroom : (length (u_tx u) < uart_fifo_depth)%nat).
      { rewrite Hempty. cbn [length]. unfold uart_fifo_depth. lia. }
      assert (Hacc' : uart_acc u' = l ++ [sb]).
      { rewrite (uart_write_thr_acc u sb u' Hdlab Hroom Hwrite) Haccu. reflexivity. }
      iMod (uart_tx_own_update γd u l u' with "Htx Hown") as "[Htx Hown]".
      iMod (uart_sent_update γd u u' with "Hs") as "[Hs Hsent]".
      { rewrite Haccu Hacc'. by apply prefix_app_r. }
      iDestruct (uart_out_auth_stable γd u u' (uart_write_out _ _ _ _ Hwrite)
                   with "Hout") as "Hout".
      iDestruct (uart_dlab_auth_stable γd u u'
                   (uart_write_dlab_0 _ _ _ Hwrite) with "Hdl") as "Hdl".
      iEval (rewrite Hacc') in "Hown".
      iEval (rewrite Hacc') in "Hsent".
      iModIntro. rewrite /uart_ghosts. iFrame "Hs Hout Htx Hdl Hown Hsent".
    - iIntros "Hsm Htlbinv Hpc Hfile [Hown Hsent]".
      iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hown Hsent").
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


  (* The mask [andi a5,a5,32] applied to the LSR-load value for a read byte. *)
  Definition lsr_masked (b : bv 8) : mword 64 :=
    and_vec (lsr_ldval_of b) (sign_extend' 64 (mword_of_int 32 : mword 12)).

  (* The post-loop register maps, now indexed by the EXIT byte [b] the poll
     observed (not by a UART state, which the caller can no longer name):
       f4' : loop exit at 0x992, a5 = [andi]-masked LSR value
       f5' : after [zext.b a0,s1]     (0x992)
       f6' : after [lui a5,0x10000]   (0x996), the pre-THR-store map. *)
  Definition ppc_f4' (m : gmap regidx (mword 64)) (b : bv 8) : gmap regidx (mword 64) :=
    <[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> (ppc_f2 m).
  Definition ppc_f5' (m : gmap regidx (mword 64)) (b : bv 8) : gmap regidx (mword 64) :=
    <[Regidx (mword_of_int 10) := regval_into_reg (and_vec (ppc_f4' m b !!! Regidx (mword_of_int 9))
        (sign_extend' 64 (mword_of_int 255 : mword 12)))]> (ppc_f4' m b).
  Definition ppc_f6' (m : gmap regidx (mword 64)) (b : bv 8) : gmap regidx (mword 64) :=
    <[Regidx (mword_of_int 15) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> (ppc_f5' m b).

  Lemma ppc_f4'_s1 (m : gmap regidx (mword 64)) (b : bv 8) :
    ppc_f4' m b !!! Regidx (mword_of_int 9) = m !!! Regidx (mword_of_int 9).
  Proof.
    unfold ppc_f4', ppc_f2, ppc_f1.
    do 3 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]). reflexivity.
  Qed.

  Lemma ppc_f6'_a5 (m : gmap regidx (mword 64)) (b : bv 8) :
    ppc_f6' m b !!! Regidx (mword_of_int 15) = uart_pa 0.
  Proof.
    unfold ppc_f6'. rewrite lookup_total_insert.
    apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma ppc_f6'_a0 (m : gmap regidx (mword 64)) (b : bv 8) :
    ppc_f6' m b !!! Regidx (mword_of_int 10)
    = and_vec (m !!! Regidx (mword_of_int 9)) (sign_extend' 64 (mword_of_int 255 : mword 12)).
  Proof.
    unfold ppc_f6', ppc_f5'.
    rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
    rewrite lookup_total_insert. rewrite ppc_f4'_s1. reflexivity.
  Qed.

  (* ================================================================= *)
  (*  THE THRE POLL LOOP: 0x988 -> 0x990, run under [dev_inv].          *)
  (*    0x988  lbu   a5,0(a4)   -- read LSR (a4 = uart_pa 5)            *)
  (*    0x98c  andi  a5,a5,32   -- mask THRE bit                        *)
  (*    0x990  c.beqz a5,0x988  -- THRE clear -> spin; set -> fall out  *)
  (*                                                                    *)
  (*  Unlike the old straight-line devcore, THRE is NOT assumed: the    *)
  (*  device state is shared, so any given LSR read may find the FIFO   *)
  (*  non-empty and the branch may loop.  Proved by Löb, mirroring      *)
  (*  WpAcquireLock's spin loop -- the [c.beqz]-taken back edge is      *)
  (*  [wp_cbeqz_taken_s_config_scfg_pt], whose step-later strips the IH.   *)
  (*                                                                    *)
  (*  On exit (THRE set), the loop hands the caller the transmitter     *)
  (*  token back AND [uart_out_lb l]: the observation that at the read  *)
  (*  the accepted trace [l] was fully transmitted.  That bound is what *)
  (*  [uart_tx_ready_persists] later turns into ``the FIFO is still     *)
  (*  empty at the THR write''.  Only a5 is clobbered, so the exit map  *)
  (*  is [<[a5 := lsr_masked b]> mentry] for whatever byte b was seen.  *)
  (* ================================================================= *)
  Lemma wp_uartputc_poll_r (Rg : s_regime) (γ : gname) (γd : uart_names)
      (Φ : mval -> iProp Σ) (mentry : gmap regidx (mword 64)) (l : list (bv 8))
      {dq : dfrac} :
    mentry !!! Regidx (mword_of_int 14) = uart_pa 5 ->
    smode_config γ dq -∗
    sr_inv Rg -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x26)) -∗ gpr_file mentry -∗
    dev_inv γd -∗ uart_tx_own γd l -∗
    ( ∀ b : bv 8,
      smode_config γ dq -∗
      sr_inv Rg -∗
      pc_is (mword_of_int (UPS + 0x30)) -∗
      gpr_file (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> mentry) -∗
      uart_tx_own γd l -∗ uart_out_lb γd l -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Ha4e.
    iIntros "Hsm Htlbinv #Ht Hpc Hfile #Hdinv Hown Hcont".
    iDestruct (upi_26 with "Ht") as "#Hi26".
    iDestruct (upi_2a with "Ht") as "#Hi2a".
    iDestruct (upi_2e with "Ht") as "#Hi2e".
    assert (P2a : add_vec_int (mword_of_int (UPS + 0x26) : mword 64) 4 = mword_of_int (UPS + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P2e : add_vec_int (mword_of_int (UPS + 0x2a) : mword 64) 4 = mword_of_int (UPS + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    assert (P30 : add_vec_int (mword_of_int (UPS + 0x2e) : mword 64) 2 = mword_of_int (UPS + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    (* the c.beqz-taken back edge lands at the loop head 0x988 = UPS+0x26 *)
    assert (Htgt : add_vec (mword_of_int (UPS + 0x2e) : mword 64)
                     (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
                   = mword_of_int (UPS + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    (* The loop invariant, proved by Löb.  The loop-head map [m] agrees with
       [mentry] off a5 and keeps a4 = uart_pa 5; the continuation is a PREMISE
       so each iteration receives a fresh copy (WpAcquireLock's spin idiom).
       Proved from the persistent context only (instruction facts + dev_inv),
       so the caller's own resources are free to feed it at [m := mentry]. *)
    iAssert (∀ m : gmap regidx (mword 64),
      ⌜ m !!! Regidx (mword_of_int 14) = uart_pa 5 ⌝ -∗
      ⌜ forall Y, <[Regidx (mword_of_int 15) := Y]> m
                = <[Regidx (mword_of_int 15) := Y]> mentry ⌝ -∗
      smode_config γ dq -∗ sr_inv Rg -∗
      pc_is (mword_of_int (UPS + 0x26)) -∗ gpr_file m -∗ uart_tx_own γd l -∗
      ( ∀ b : bv 8, smode_config γ dq -∗ sr_inv Rg -∗
          pc_is (mword_of_int (UPS + 0x30)) -∗
          gpr_file (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> mentry) -∗
          uart_tx_own γd l -∗ uart_out_lb γd l -∗ WP (Loop : expr riscv_lang) {{ Φ }}) -∗
      WP (Loop : expr riscv_lang) {{ Φ }})%I with "[]" as "Loop".
    { iLöb as "IH". iIntros (m Ha4m Hagm) "Hsm Htlbinv Hpc Hfile Hown Hk".
      (* 0x988  lbu a5,0(a4)  -- LSR read, under dev_inv *)
      iApply (wp_uart_lsr_read_s_r Rg γ γd Φ (mword_of_int (UPS + 0x26)) (mword_of_int 15) (mword_of_int 14)
                m l (dq:=dq)
 ltac:(vm_compute; discriminate) Ha4m
                with "Hsm Htlbinv Hpc Hfile Hi26 Hdinv Hown").
      iIntros (b) "Hsm Htlbinv Hpc Hfile Hown Hlb".
      iEval (rewrite P2a) in "Hpc".
      (* 0x98c  andi a5,a5,32 *)
      iApply (wp_andi_s_r Rg γ Φ (mword_of_int (UPS + 0x2a)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 32 : mword 12)
                (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_ldval_of b)]> m) (dq:=dq)
 ltac:(vm_compute; discriminate)
                with "Hsm Htlbinv Hpc Hfile Hi2a").
      iIntros "Hsm Htlbinv Hpc Hfile".
      iEval (rewrite lookup_total_insert insert_insert) in "Hfile".
      change (and_vec (lsr_ldval_of b) (sign_extend' 64 (mword_of_int 32 : mword 12)))
        with (lsr_masked b) in *.
      iEval (rewrite P2e) in "Hpc".
      (* 0x990  c.beqz a5,0x988 : the test is exactly [lsr_thre_clear b] *)
      destruct (lsr_thre_clear b) eqn:Hcase.
      - (* THRE clear: branch TAKEN back to 0x988, loop via the IH.  The taken
           leaf hands its step's later out, so [iNext] strips the IH's. *)
        iApply (wp_cbeqz_taken_s_config_scfg_r Rg γ Φ (mword_of_int (UPS + 0x2e)) (mword_of_int 252 : mword 8)
                  (Cregidx (mword_of_int 7)) (mword_of_int 15)
                  (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> m) (dq:=dq)
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite lookup_total_insert; unfold regval_into_reg, lsr_masked;
                        exact Hcase)
                  ltac:(vm_compute; reflexivity)
                  with "Hsm Htlbinv Hpc Hfile Hi2e").
        iNext.
        iIntros "Hsm Htlbinv Hpc Hfile".
        iEval (rewrite Htgt) in "Hpc".
        iApply ("IH" $! (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> m)
                  with "[%] [%] Hsm Htlbinv Hpc Hfile Hown Hk").
        + rewrite lookup_total_insert_ne; [exact Ha4m | vm_compute; discriminate].
        + intro Y. rewrite insert_insert. exact (Hagm Y).
      - (* THRE set: branch FALLS THROUGH to 0x992, exit with the out-bound *)
        iApply (wp_cbeqz_fall_s_config_scfg_r Rg γ Φ (mword_of_int (UPS + 0x2e)) (mword_of_int 252 : mword 8)
                  (Cregidx (mword_of_int 7)) (mword_of_int 15)
                  (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> m) (dq:=dq)
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite lookup_total_insert; unfold regval_into_reg, lsr_masked;
                        exact Hcase)
                  with "Hsm Htlbinv Hpc Hfile Hi2e").
        iIntros "Hsm Htlbinv Hpc Hfile".
        iEval (rewrite P30) in "Hpc".
        iEval (rewrite (Hagm (regval_into_reg (lsr_masked b)))) in "Hfile".
        iApply ("Hk" $! b with "Hsm Htlbinv Hpc Hfile Hown").
        by iApply "Hlb". }
    iApply ("Loop" $! mentry with "[%] [%] Hsm Htlbinv Hpc Hfile Hown Hcont").
    - exact Ha4e.
    - reflexivity.
  Qed.


  Lemma wp_uartputc_devcore_r (Rg : s_regime) (γ : gname) (γd : uart_names)
      (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (l : list (bv 8)) {dq : dfrac} :
    let sb : mword 8 := autocast (T := mword)
       (subrange_vec_dec (and_vec (m !!! Regidx (mword_of_int 9))
          (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) in
    smode_config γ dq -∗
    sr_inv Rg -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x20)) -∗ gpr_file m -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    ( ∀ b : bv 8,
      smode_config γ dq -∗
      sr_inv Rg -∗
      pc_is (mword_of_int (UPS + 0x3c)) -∗
      gpr_file (ppc_f6' m b) -∗
      uart_tx_own γd (l ++ [sb]) -∗ uart_sent γd (l ++ [sb]) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sb.
    iIntros "Hsm Htlbinv #Ht Hpc Hfile #Hdinv Hown #Hoff Hcont".
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
    iApply (wp_lui_s_r Rg γ Φ (mword_of_int (UPS + 0x20)) (mword_of_int 14) (mword_of_int 0x10000 : mword 20)
              m (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi20").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P24) in "Hpc".
    (* 0x986  c.addi a4,a4,5 *)
    iApply (wp_caddi_gpr_s_config_scfg_r Rg γ Φ (mword_of_int (UPS + 0x24)) (mword_of_int 14) (mword_of_int 5 : mword 6)
              (ppc_f1 m) (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi24").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P26) in "Hpc".
    (* 0x988 -> 0x990  the THRE poll loop (Löb; may spin), exits at 0x992 with
       the read byte [b] and the out-bound [uart_out_lb l] *)
    iApply (wp_uartputc_poll_r Rg γ γd Φ (ppc_f2 m) l (dq:=dq)
              (ppc_f2_a4 m)
              with "Hsm Htlbinv Ht Hpc Hfile Hdinv Hown").
    iIntros (b) "Hsm Htlbinv Hpc Hfile Hown #Hlb".
    (* the poll's exit map <[a5:=lsr_masked b]>(ppc_f2 m) IS ppc_f4' m b *)
    iEval (change (<[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> (ppc_f2 m))
             with (ppc_f4' m b)) in "Hfile".
    (* 0x992  zext.b a0,s1  (andi a0,s1,255) *)
    iApply (wp_andi_s_r Rg γ Φ (mword_of_int (UPS + 0x30)) (mword_of_int 10) (mword_of_int 9) (mword_of_int 255 : mword 12)
              (ppc_f4' m b) (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi30").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (change (<[Regidx (mword_of_int 10) := regval_into_reg (and_vec (ppc_f4' m b !!! Regidx (mword_of_int 9))
             (sign_extend' 64 (mword_of_int 255 : mword 12)))]> (ppc_f4' m b))
             with (ppc_f5' m b)) in "Hfile".
    iEval (rewrite P34) in "Hpc".
    (* 0x996  lui a5,0x10000 *)
    iApply (wp_lui_s_r Rg γ Φ (mword_of_int (UPS + 0x34)) (mword_of_int 15) (mword_of_int 0x10000 : mword 20)
              (ppc_f5' m b) (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi34").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (change (<[Regidx (mword_of_int 15) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> (ppc_f5' m b))
             with (ppc_f6' m b)) in "Hfile".
    iEval (rewrite P38) in "Hpc".
    (* 0x99a  sb a0,0(a5)  -- THR write.  a0 = zext.b of s1, and the store byte
       the wrapper enqueues is exactly devcore's [sb] (ppc_f6'_a0).  The payoff:
       the out-bound + token + frozen DLAB establish the FIFO is still empty. *)
    assert (Hsbb : (autocast (T := mword)
                      (subrange_vec_dec (ppc_f6' m b !!! Regidx (mword_of_int 10))
                         (Z.sub (Z.mul 1 8) 1) 0) : mword 8) = sb).
    { unfold sb. rewrite ppc_f6'_a0. reflexivity. }
    iApply (wp_uart_thr_write_s_r Rg γ γd Φ (mword_of_int (UPS + 0x38)) (mword_of_int 10) (mword_of_int 15)
              (ppc_f6' m b) l (dq:=dq)
              (ppc_f6'_a5 m b)
              with "Hsm Htlbinv Hpc Hfile Hi38 Hdinv Hown Hlb Hoff [Hcont]").
    iIntros "Hsm Htlbinv Hpc Hfile Hown Hsent".
    iEval (rewrite Hsbb) in "Hown". iEval (rewrite Hsbb) in "Hsent".
    iEval (rewrite P3c) in "Hpc".
    iApply ("Hcont" $! b with "Hsm Htlbinv Hpc Hfile Hown Hsent").
  Qed.


  (* =================================================================== *)
  (*  PANIC-CHECK CHUNK: uartputc_sync 0x96e -> 0x978.                     *)
  (*    0x96e  auipc a5,0xa                                                *)
  (*    0x980  lw    a5,-1880(a5)     -> read global `panicking`           *)
  (*    0x976  beqz  a5,0x9b2         (c.beqz; on panicking!=0 falls thru) *)
  (*  The global word is read from a persistent (DfracDiscarded) snapshot   *)
  (*  `panicking_pa ↦₄□ pv`, the read-only-global analogue of kernel_data;  *)
  (*  the caller asserts `pv` sign-extends to a nonzero value (panicking!=0)*)
  (*  so the branch falls through to the panicked check.                    *)
  (* =================================================================== *)
  Lemma wp_uartputc_panicking_check_r (Rg : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (pv : mword 32) {dq dqm : dfrac} :
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    smode_config γ dq -∗
    sr_inv Rg -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x0c)) -∗ gpr_file m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    ( smode_config γ dq -∗
      sr_inv Rg -∗
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
    iApply (wp_auipc_s_scfg_r Rg γ Φ (mword_of_int (UPS + 0x0c)) (mword_of_int 15) (mword_of_int 0xa : mword 20)
              m (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi0c").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P10) in "Hpc".
    (* 0x980 lw a5,-1880(a5) : reads panicking; align the snapshot to the ea *)
    set (g1 := <[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x0c)) (auipc_off (mword_of_int 0xa : mword 20)))]> m).
    assert (Hea : add_vec (g1 !!! Regidx (mword_of_int 15)) (sign_extend' 64 (mword_of_int 0x8a8 : mword 12))
                  = (mword_of_int KernelSyms.panicking : mword 64)).
    { unfold g1. rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite <- Hea) in "Hsnap".
    iApply (wp_lw_s_scfg_r Rg γ Φ (mword_of_int (UPS + 0x10)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 0x8a8 : mword 12)
              g1 pv (dq:=dq) (dqm:=dqm)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi10 Hsnap").
    iIntros "Hsm Htlbinv Hpc Hfile Hsnap".
    iEval (rewrite Hea) in "Hsnap".
    iEval (rewrite P14) in "Hpc".
    (* 0x976 c.beqz a5,0x9b2 : panicking != 0 -> falls through *)
    iApply (wp_cbeqz_fall_s_config_scfg_r Rg γ Φ (mword_of_int (UPS + 0x14)) (mword_of_int 30 : mword 8)
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
  Lemma wp_uartputc_panicked_check_r (Rg : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (pkv : mword 32) {dq dqm : dfrac} :
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    smode_config γ dq -∗
    sr_inv Rg -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x16)) -∗ gpr_file m -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm } pkv -∗
    ( smode_config γ dq -∗
      sr_inv Rg -∗
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
    iApply (wp_auipc_s_scfg_r Rg γ Φ (mword_of_int (UPS + 0x16)) (mword_of_int 15) (mword_of_int 0xa : mword 20)
              m (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi16").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P1a) in "Hpc".
    set (g1 := <[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x16)) (auipc_off (mword_of_int 0xa : mword 20)))]> m).
    assert (Hea : add_vec (g1 !!! Regidx (mword_of_int 15)) (sign_extend' 64 (mword_of_int 0x89a : mword 12))
                  = (mword_of_int KernelSyms.panicked : mword 64)).
    { unfold g1. rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite <- Hea) in "Hsnap".
    iApply (wp_lw_s_scfg_r Rg γ Φ (mword_of_int (UPS + 0x1a)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 0x89a : mword 12)
              g1 pkv (dq:=dq) (dqm:=dqm)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi1a Hsnap").
    iIntros "Hsm Htlbinv Hpc Hfile Hsnap".
    iEval (rewrite Hea) in "Hsnap".
    iEval (rewrite P1e) in "Hpc".
    iApply (wp_cbnez_fall_s_scfg_r Rg γ Φ (mword_of_int (UPS + 0x1e)) (mword_of_int 28 : mword 8)
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
  Lemma wp_uartputc_panicking_check2_r (Rg : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (pv : mword 32) {dq dqm : dfrac} :
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    smode_config γ dq -∗
    sr_inv Rg -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x3c)) -∗ gpr_file m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    ( smode_config γ dq -∗
      sr_inv Rg -∗
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
    iApply (wp_auipc_s_scfg_r Rg γ Φ (mword_of_int (UPS + 0x3c)) (mword_of_int 15) (mword_of_int 0xa : mword 20)
              m (dq:=dq)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi3c").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite P40) in "Hpc".
    set (g1 := <[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x3c)) (auipc_off (mword_of_int 0xa : mword 20)))]> m).
    assert (Hea : add_vec (g1 !!! Regidx (mword_of_int 15)) (sign_extend' 64 (mword_of_int 0x878 : mword 12))
                  = (mword_of_int KernelSyms.panicking : mword 64)).
    { unfold g1. rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite <- Hea) in "Hsnap".
    iApply (wp_lw_s_scfg_r Rg γ Φ (mword_of_int (UPS + 0x40)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 0x878 : mword 12)
              g1 pv (dq:=dq) (dqm:=dqm)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi40 Hsnap").
    iIntros "Hsm Htlbinv Hpc Hfile Hsnap".
    iEval (rewrite Hea) in "Hsnap".
    iEval (rewrite P44) in "Hpc".
    iApply (wp_cbeqz_fall_s_config_scfg_r Rg γ Φ (mword_of_int (UPS + 0x44)) (mword_of_int 10 : mword 8)
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
  (*  Chains the four body chunks under one plain [tlb_inv_pt].                 *)
  (* =================================================================== *)
  Lemma wp_uartputc_body_r (Rg : s_regime) (γ : gname) (γd : uart_names)
      (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (l : list (bv 8)) (pv pkv : mword 32)
      {dq dqm dqm2 : dfrac} :
    let sb : mword 8 := autocast (T := mword)
       (subrange_vec_dec (and_vec (m !!! Regidx (mword_of_int 9))
          (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) in
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    smode_config γ dq -∗
    sr_inv Rg -∗ kernel_text -∗
    pc_is (mword_of_int (UPS + 0x0c)) -∗ gpr_file m -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    ( ∀ mf,
      smode_config γ dq -∗
      sr_inv Rg -∗
      pc_is (mword_of_int (UPS + 0x46)) -∗
      gpr_file mf -∗
      ⌜ callee_saved m mf ⌝ -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ [sb]) -∗ uart_sent γd (l ++ [sb]) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sb.
    iIntros (Hpv Hpkv)
      "Hsm Htlbinv #Ht Hpc Hfile Hpk Hpkd #Hdinv Hown #Hoff Hcont".
    (* 0x96e -> 0x978 : panicking check (falls through) *)
    iApply (wp_uartputc_panicking_check_r Rg γ Φ m pv (dq:=dq) (dqm:=dqm)
 Hpv
              with "Hsm Htlbinv Ht Hpc Hfile Hpk").
    iIntros "Hsm Htlbinv Hpc Hfile Hpk".
    set (f1 := <[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pv)]>
               (<[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x0c)) (auipc_off (mword_of_int 0xa : mword 20)))]> m)).
    (* 0x978 -> 0x982 : panicked check (falls through) *)
    iApply (wp_uartputc_panicked_check_r Rg γ Φ f1 pkv (dq:=dq) (dqm:=dqm2)
 Hpkv
              with "Hsm Htlbinv Ht Hpc Hfile Hpkd").
    iIntros "Hsm Htlbinv Hpc Hfile Hpkd".
    set (f2 := <[Regidx (mword_of_int 15) := regval_into_reg (sign_extend' 64 pkv)]>
               (<[Regidx (mword_of_int 15) := regval_into_reg (add_vec (mword_of_int (UPS + 0x16)) (auipc_off (mword_of_int 0xa : mword 20)))]> f1)).
    assert (HR9 : f2 !!! Regidx (mword_of_int 9) = m !!! Regidx (mword_of_int 9)).
    { unfold f2, f1. do 4 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]). reflexivity. }
    (* the device core's store byte is about f2!!!s1, but that equals m!!!s1 *)
    assert (Hsbf2 : (autocast (T := mword)
                      (subrange_vec_dec (and_vec (f2 !!! Regidx (mword_of_int 9))
                         (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) : mword 8) = sb).
    { unfold sb. rewrite HR9. reflexivity. }
    (* 0x982 -> 0x99e : device core (THRE poll loop + THR write) *)
    iApply (wp_uartputc_devcore_r Rg γ γd Φ f2 l (dq:=dq)
              with "Hsm Htlbinv Ht Hpc Hfile Hdinv Hown Hoff").
    iIntros (b) "Hsm Htlbinv Hpc Hfile Hown Hsent".
    iEval (rewrite Hsbf2) in "Hown". iEval (rewrite Hsbf2) in "Hsent".
    (* 0x99e -> 0x9a8 : 2nd panicking check (falls through) *)
    iApply (wp_uartputc_panicking_check2_r Rg γ Φ (ppc_f6' f2 b) pv (dq:=dq) (dqm:=dqm)
 Hpv
              with "Hsm Htlbinv Ht Hpc Hfile Hpk").
    iIntros "Hsm Htlbinv Hpc Hfile Hpk".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile [%] Hpk Hpkd Hown Hsent").
    (* The body writes only a4/a5/a0, none of them callee-saved, so every
       callee-saved register still holds its entry value. *)
    unfold callee_saved.
    repeat split;
      unfold ppc_f6', ppc_f5', ppc_f4', ppc_f2, ppc_f1, f2, f1;
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); reflexivity.
  Qed.


End WpUartPutcSync.
