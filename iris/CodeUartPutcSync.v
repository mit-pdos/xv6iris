(* ===================================================================== *)
(*  CodeUartPutcSync.v                                                       *)
(*                                                                         *)
(*  Whole-function WP for uartputc_sync (0x80000962), the S-mode UART      *)
(*  synchronous putc.  It composes ordinary S-mode RAM/ALU/branch leaves   *)
(*  with the two native-kernel-PT device leaves (wp_lb_uart_s_pt,         *)
(*  wp_sb_uart_s_pt from WpUartKpt.v) under ONE plain [tlb_inv_pt root_ppn]. *)
(*                                                                         *)
(*  This file first assembles the per-instruction [instr] decode facts     *)
(*  (mirroring CodeKalloc.v) and two missing base leaves (LUI, ANDI),  *)
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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecodeBridge WpRvcBridge KernelText.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import WpMmodeLeafBase.
Require Import WpUart.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Require Import KernelBaseDecode.
Require Import RiscvLang RiscvPtsto.
Require Import KernelText.
From Stdlib Require Import ZArith Lia.

Import Defs.

(* ===================================================================== *)
(*  Per-instruction decode facts for the device-core instructions.        *)
(*  Base decodes go through [decode_bridge_ms]; RVC through [rvc_oneshot]. *)
(* ===================================================================== *)


(* 0x988  00074783  lbu a5,0(a4) *)
Lemma updc_00074783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00074783 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), true, 1), s).
Proof. decode_bridge_ms. Qed.


(* 0x992  0ff4f513  zext.b a0,s1  (andi a0,s1,255) *)
Lemma updc_0ff4f513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0ff4f513 : mword 32)) s
  = Some (ITYPE (mword_of_int 255 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ANDI), s).
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

(* [exec_execute_C_BEQZ] (compressed BEQZ -> base BTYPE/BEQ bridge) now lives
   in WpMmodeLeafBase.v alongside [exec_execute_C_BNEZ]. *)

Notation UPS := KernelSyms.uartputc_sync.

Section CodeUartPutcSync.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  (* the device leaves open [dev_inv], whose ghosts need this *)
  Context `{!uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* The three [instr]-builder templates, copied verbatim from CodeMycpu.   *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the eight device-core instructions (0x982-0x99a).  *)
  (* ------------------------------------------------------------------- *)
  Lemma upi_20 : kernel_text -∗ instr (mword_of_int (UPS + 0x20) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (UPS + 0x20)%Z (mword_of_int 0x10000737 : mword 32)
    (mword_of_int (UPS + 0x20) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 14), LUI)) bdec_10000737. Qed.

  Lemma upi_24 : kernel_text -∗ instr (mword_of_int (UPS + 0x24) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (UPS + 0x24)%Z (mword_of_int 0x0715 : mword 16)
    (mword_of_int (UPS + 0x24) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) uprvc_0715 exec_execute_C_ADDI. Qed.

  Lemma upi_26 : kernel_text -∗ instr (mword_of_int (UPS + 0x26) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), true, 1)).
  Proof. mk_base (UPS + 0x26)%Z (mword_of_int 0x00074783 : mword 32)
    (mword_of_int (UPS + 0x26) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), true, 1)) updc_00074783. Qed.

  Lemma upi_2a : kernel_text -∗ instr (mword_of_int (UPS + 0x2a) : mword 64) false (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_base (UPS + 0x2a)%Z (mword_of_int 0x0207f793 : mword 32)
    (mword_of_int (UPS + 0x2a) : mword 64) (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) bdec_0207f793. Qed.

  Lemma upi_2e : kernel_text -∗ instr (mword_of_int (UPS + 0x2e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (UPS + 0x2e)%Z (mword_of_int 0xdfe5 : mword 16)
    (mword_of_int (UPS + 0x2e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) uprvc_dfe5 exec_execute_C_BEQZ. Qed.

  Lemma upi_30 : kernel_text -∗ instr (mword_of_int (UPS + 0x30) : mword 64) false (ITYPE (mword_of_int 255 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ANDI)).
  Proof. mk_base (UPS + 0x30)%Z (mword_of_int 0x0ff4f513 : mword 32)
    (mword_of_int (UPS + 0x30) : mword 64) (ITYPE (mword_of_int 255 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ANDI)) updc_0ff4f513. Qed.

  Lemma upi_34 : kernel_text -∗ instr (mword_of_int (UPS + 0x34) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (UPS + 0x34)%Z (mword_of_int 0x100007b7 : mword 32)
    (mword_of_int (UPS + 0x34) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI)) bdec_100007b7. Qed.

  Lemma upi_38 : kernel_text -∗ instr (mword_of_int (UPS + 0x38) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (UPS + 0x38)%Z (mword_of_int 0x00a78023 : mword 32)
    (mword_of_int (UPS + 0x38) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), 1)) updc_00a78023. Qed.

  (* --- panic-check instructions (0x96e auipc / 0x972 lw / 0x976 c.beqz) --- *)
  Lemma upi_0c : kernel_text -∗ instr (mword_of_int (UPS + 0x0c) : mword 64) false (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (UPS + 0x0c)%Z (mword_of_int 0x0000a797 : mword 32)
    (mword_of_int (UPS + 0x0c) : mword 64) (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0000a797. Qed.

  Lemma upi_10 : kernel_text -∗ instr (mword_of_int (UPS + 0x10) : mword 64) false (LOAD (mword_of_int 0x8a8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (UPS + 0x10)%Z (mword_of_int 0x8a87a783 : mword 32)
    (mword_of_int (UPS + 0x10) : mword 64) (LOAD (mword_of_int 0x8a8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) updc_8a87a783. Qed.

  Lemma upi_14 : kernel_text -∗ instr (mword_of_int (UPS + 0x14) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 30 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (UPS + 0x14)%Z (mword_of_int 0xcf95 : mword 16)
    (mword_of_int (UPS + 0x14) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 30 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) uprvc_cf95 exec_execute_C_BEQZ. Qed.

  (* --- panicked-check (0x978 auipc / 0x97c lw / 0x980 c.bnez) --- *)
  Lemma upi_16 : kernel_text -∗ instr (mword_of_int (UPS + 0x16) : mword 64) false (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (UPS + 0x16)%Z (mword_of_int 0x0000a797 : mword 32)
    (mword_of_int (UPS + 0x16) : mword 64) (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0000a797. Qed.

  Lemma upi_1a : kernel_text -∗ instr (mword_of_int (UPS + 0x1a) : mword 64) false (LOAD (mword_of_int 0x89a : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (UPS + 0x1a)%Z (mword_of_int 0x89a7a783 : mword 32)
    (mword_of_int (UPS + 0x1a) : mword 64) (LOAD (mword_of_int 0x89a : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) updc_89a7a783. Qed.

  Lemma upi_1e : kernel_text -∗ instr (mword_of_int (UPS + 0x1e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (UPS + 0x1e)%Z (mword_of_int 0xef85 : mword 16)
    (mword_of_int (UPS + 0x1e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) uprvc_ef85 exec_execute_C_BNEZ. Qed.

  (* --- 2nd panicking-check (0x99e auipc / 0x9a2 lw / 0x9a6 c.beqz) --- *)
  Lemma upi_3c : kernel_text -∗ instr (mword_of_int (UPS + 0x3c) : mword 64) false (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (UPS + 0x3c)%Z (mword_of_int 0x0000a797 : mword 32)
    (mword_of_int (UPS + 0x3c) : mword 64) (UTYPE (mword_of_int 0xa : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0000a797. Qed.

  Lemma upi_40 : kernel_text -∗ instr (mword_of_int (UPS + 0x40) : mword 64) false (LOAD (mword_of_int 0x878 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (UPS + 0x40)%Z (mword_of_int 0x8787a783 : mword 32)
    (mword_of_int (UPS + 0x40) : mword 64) (LOAD (mword_of_int 0x878 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) updc_8787a783. Qed.

  Lemma upi_44 : kernel_text -∗ instr (mword_of_int (UPS + 0x44) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (UPS + 0x44)%Z (mword_of_int 0xcb91 : mword 16)
    (mword_of_int (UPS + 0x44) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) cdec_cb91 exec_execute_C_BEQZ. Qed.

  (* [wp_lui_s_r] and [wp_andi_s_r] (the base LUI/ANDI S-mode gpr-write
     leaves) now live in WpSmodePtAlu.v with the rest of the ALU leaves. *)

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

  (* THE POLL'S BRANCH TEST, as a function of the read byte: [andi a5,a5,32]
     then [c.beqz a5].  True = THRE clear = branch taken = spin again. *)
  Definition lsr_thre_clear (b : bv 8) : bool :=
    eq_vec (and_vec (lsr_ldval_of b) (sign_extend' 64 (mword_of_int 32 : mword 12))) zero_reg.

  (* THRE-ready path: after [lbu (LSR)] + [andi ...,32], a5 masks to bit5 = 32,
     so the loop's [c.beqz a5] falls through. *)

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
     writes a GPR (named to keep the WP threading readable, CodeMycpu-style). *)
  Definition ppc_f1 (m : regfile) : regfile :=
    <[Regidx (mword_of_int 14) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> m.
  Definition ppc_f2 (m : regfile) : regfile :=
    <[Regidx (mword_of_int 14) := regval_into_reg (add_vec (ppc_f1 m !!! Regidx (mword_of_int 14))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> (ppc_f1 m).

  (* the three call-site register lookups the leaves need. *)
  Lemma ppc_f2_a4 (m : regfile) :
    ppc_f2 m !!! Regidx (mword_of_int 14) = uart_pa 5.
  Proof.
    unfold ppc_f2, ppc_f1. rewrite !upd_eq.
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
  Definition ppc_f4' (m : regfile) (b : bv 8) : regfile :=
    <[Regidx (mword_of_int 15) := regval_into_reg (lsr_masked b)]> (ppc_f2 m).
  Definition ppc_f5' (m : regfile) (b : bv 8) : regfile :=
    <[Regidx (mword_of_int 10) := regval_into_reg (and_vec (ppc_f4' m b !!! Regidx (mword_of_int 9))
        (sign_extend' 64 (mword_of_int 255 : mword 12)))]> (ppc_f4' m b).
  Definition ppc_f6' (m : regfile) (b : bv 8) : regfile :=
    <[Regidx (mword_of_int 15) := regval_into_reg (luival (mword_of_int 0x10000 : mword 20))]> (ppc_f5' m b).

  Lemma ppc_f4'_s1 (m : regfile) (b : bv 8) :
    ppc_f4' m b !!! Regidx (mword_of_int 9) = m !!! Regidx (mword_of_int 9).
  Proof.
    unfold ppc_f4', ppc_f2, ppc_f1.
    do 3 (rewrite upd_ne; [| vm_compute; discriminate]). reflexivity.
  Qed.

  Lemma ppc_f6'_a5 (m : regfile) (b : bv 8) :
    ppc_f6' m b !!! Regidx (mword_of_int 15) = uart_pa 0.
  Proof.
    unfold ppc_f6'. rewrite upd_eq.
    apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma ppc_f6'_a0 (m : regfile) (b : bv 8) :
    ppc_f6' m b !!! Regidx (mword_of_int 10)
    = and_vec (m !!! Regidx (mword_of_int 9)) (sign_extend' 64 (mword_of_int 255 : mword 12)).
  Proof.
    unfold ppc_f6', ppc_f5'.
    rewrite upd_ne; [| vm_compute; discriminate].
    rewrite upd_eq. rewrite ppc_f4'_s1. reflexivity.
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

  (* =================================================================== *)
  (*  PANICKED-CHECK CHUNK: 0x978 -> 0x982 (auipc · lw panicked · c.bnez).  *)
  (*  On the panic path panicked = 0, so the [c.bnez] falls through to the  *)
  (*  device core.  [pkv] sign-extends to 0.                                *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  2nd PANICKING-CHECK CHUNK: 0x99e -> 0x9a8 (auipc · lw panicking · beqz).*)
  (*  Reads the same [panicking] global; on the panic path it is nonzero so  *)
  (*  the [c.beqz] falls through to the epilogue.                            *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  THE BODY: uartputc_sync 0x96e -> 0x9a8 (post-prologue to pre-epilogue) *)
  (*  on the panic path (panicking != 0, panicked = 0), THRE ready.         *)
  (*  Chains the four body chunks under one plain [tlb_inv_pt].                 *)
  (* =================================================================== *)

End CodeUartPutcSync.

(* ---- the prologue/epilogue frame instructions ---- *)
Section CodeUartPutcSyncFrame.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [instr]-builder templates, copied verbatim from CodeUartPutcSync.v. *)
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

End CodeUartPutcSyncFrame.
