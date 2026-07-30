(* WpSleeplockDecode.v -- decode templates + [instr] facts for the four
   kernel/sleeplock.c functions:

     initsleeplock @ 0x80003e96   (offsets 0x00 .. 0x34)
     acquiresleep  @ 0x80003ecc   (offsets 0x00 .. 0x44)
     releasesleep  @ 0x80003f12   (offsets 0x00 .. 0x36)
     holdingsleep  @ 0x80003f4a   (offsets 0x00 .. 0x48)

   Mirror of WpMyprocDecode.v.  initsleeplock/acquiresleep/releasesleep share
   kalloc/kfree's 32-byte 4-register frame (ra/s0/s1/s2) and holdingsleep uses
   freerange's 48-byte frame (ra/s0/s1/s2[/s3]), so every frame word plus
   [cdec_892e] (initsleeplock's [mv s2,a1]) comes from the shared [cdec_*] templates in KernelRvcDecode.v -- this file no longer imports
   kalloc's or freerange's decode file to reach them.  Only the sleeplock-unique
   words
   -- the jal's (each with its own 21-bit offset), the auipc/addi "sleep lock"
   materialization, the sleeplock-offset full-width sw/sd/lw, the addi s2,a0,8,
   the sub/seqz pair, the branches, the c.lw/c.sw/c.mv/c.li/c.j -- get fresh
   [sldec_*] templates here. *)
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
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
From iris.base_logic.lib Require Import invariants.
Require Import KernelRvcDecode.
Require Import KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

Notation ISL := KernelSyms.initsleeplock.
Notation ASL := KernelSyms.acquiresleep.
Notation RSL := KernelSyms.releasesleep.
Notation HSL := KernelSyms.holdingsleep.

(* ===================================================================== *)
(* Generic C_LW / C_SW execute expansions (word-relative, width-4        *)
(* compressed memory ops -- the creg-indexed counterparts of C_LD/C_SD). *)
(* No shared copy exists in WpMmodeLeafBase, so state them here.          *)
(* ===================================================================== *)
(* Fresh compressed decode templates (words unique to sleeplock).        *)
(* ===================================================================== *)

(* 0x0521  c.addi a0,a0,8   (initsleeplock +0x18) *)
Lemma sldec_addi_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0521 : mword 16)) s
  = Some (C_ADDI (mword_of_int 8, Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x409c  c.lw a5,0(s1) -- the bit-keyed decode now lives in the shared base
   (sys_pause steps the same word); kept under its old name for the call sites. *)
Lemma sldec_lw_locked s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x409c : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. exact (cdec_409c s). Qed.

(* 0x591c  c.lw a5,48(a0) *)
Lemma sldec_lw_pid_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x591c : mword 16)) s
  = Some (C_LW (mword_of_int 12, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x5904  c.lw s1,48(a0) *)
Lemma sldec_lw_s1_procpid s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x5904 : mword 16)) s
  = Some (C_LW (mword_of_int 12, Cregidx (mword_of_int 2), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xd49c  c.sw a5,40(s1) *)
Lemma sldec_sw_a5_pid s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd49c : mword 16)) s
  = Some (C_SW (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xc799  c.beqz a5,+14  (acquiresleep +0x1a -> +0x28) *)
Lemma sldec_beqz s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc799 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 7, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xfbfd  c.bnez a5,-10  (acquiresleep +0x26 -> +0x1c) *)
Lemma sldec_bnez_back s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfbfd : mword 16)) s
  = Some (C_BNEZ (mword_of_int 251, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xef81  c.bnez a5,+24  (holdingsleep +0x1a -> +0x32) *)
Lemma sldec_bnez_fwd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xef81 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 12, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4481  c.li s1,0 *)
Lemma sldec_li_s1_0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4481 : mword 16)) s
  = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Fresh base (32-bit) decode templates (words unique to sleeplock).      *)
(* ===================================================================== *)

(* 0x00003597  auipc a1,0x3   (initsleeplock +0x10) *)
Lemma sldec_auipc_a1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00003597 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x3 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0x6a258593  addi a1,a1,1698  (= 0x6a2)  (initsleeplock +0x14) *)
Lemma sldec_addi_a1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6a258593 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x6a2 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0x00850913  addi s2,a0,8  (acquire/release/holdingsleep +0x0e) *)
Lemma sldec_addi_s2 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00850913 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x8 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0x0324b023  sd s2,32(s1)   (initsleeplock +0x1e) *)
Lemma sldec_sd_name s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0324b023 : mword 32)) s
  = Some (STORE (mword_of_int 0x20 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 9), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0x0204a423  sw zero,40(s1)  (init +0x26, release +0x1c) *)
Lemma sldec_sw_zero_pid s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0204a423 : mword 32)) s
  = Some (STORE (mword_of_int 0x28 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0x0284a983  lw s3,40(s1)   (holdingsleep +0x34) *)
Lemma sldec_lw_s3_pid s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0284a983 : mword 32)) s
  = Some (LOAD (mword_of_int 0x28 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 19), false, 4), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0x413484b3  sub s1,s1,s3   (holdingsleep +0x3e) *)
Lemma sldec_sub s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x413484b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 9), Regidx (mword_of_int 9), SUB), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0x0014b493  seqz s1,s1 (sltiu s1,s1,1)  (holdingsleep +0x42) *)
Lemma sldec_seqz s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0014b493 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x1 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), SLTIU), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* ---- jal's (positive 21-bit residues; target in comment) ---- *)

(* 0xcd9fc0ef  jal ra,initlock (target 0x80000b88)  init +0x1a *)
Lemma sldec_jal_initlock s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xcd9fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084056 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0xd29fc0ef  jal ra,acquire (target 0x80000c08)  acquiresleep +0x14 *)
Lemma sldec_jal_acq_asl s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd29fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084136 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0x81afe0ef  jal ra,sleep (target 0x80001f06)  acquiresleep +0x20 *)
Lemma sldec_jal_sleep s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x81afe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2088986 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0xa0dfd0ef  jal ra,myproc (target 0x80001904)  acquiresleep +0x2c *)
Lemma sldec_jal_myproc_asl s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa0dfd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087436 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0xd8ffc0ef  jal ra,release (target 0x80000c90)  acquiresleep +0x36 *)
Lemma sldec_jal_rel_asl s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd8ffc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084238 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0xce3fc0ef  jal ra,acquire (target 0x80000c08)  releasesleep +0x14 *)
Lemma sldec_jal_acq_rsl s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xce3fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084066 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0x81efe0ef  jal ra,wakeup (target 0x80001f52)  releasesleep +0x22 *)
Lemma sldec_jal_wakeup s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x81efe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2088990 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0xd57fc0ef  jal ra,release (target 0x80000c90)  releasesleep +0x28 *)
Lemma sldec_jal_rel_rsl s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd57fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084182 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0xcabfc0ef  jal ra,acquire (target 0x80000c08)  holdingsleep +0x14 *)
Lemma sldec_jal_acq_hsl s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xcabfc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084010 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0xd27fc0ef  jal ra,release (target 0x80000c90)  holdingsleep +0x20 *)
Lemma sldec_jal_rel_hsl s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd27fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084134 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* 0x983fd0ef  jal ra,myproc (target 0x80001904)  holdingsleep +0x38 *)
Lemma sldec_jal_myproc_hsl s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x983fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087298 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Section WpSleeplockDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* =================================================================== *)
  (*  initsleeplock @ 0x80003e96, offsets 0x00 .. 0x34.                   *)
  (* =================================================================== *)
  Lemma isl_00 : kernel_text -∗ instr (mword_of_int (ISL + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (ISL + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (ISL + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma isl_02 : kernel_text -∗ instr (mword_of_int (ISL + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (ISL + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (ISL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma isl_04 : kernel_text -∗ instr (mword_of_int (ISL + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (ISL + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (ISL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma isl_06 : kernel_text -∗ instr (mword_of_int (ISL + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (ISL + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (ISL + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma isl_08 : kernel_text -∗ instr (mword_of_int (ISL + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (ISL + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (ISL + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma isl_0a : kernel_text -∗ instr (mword_of_int (ISL + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (ISL + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (ISL + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma isl_0c : kernel_text -∗ instr (mword_of_int (ISL + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (ISL + 0x0c)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (ISL + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma isl_0e : kernel_text -∗ instr (mword_of_int (ISL + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (ISL + 0x0e)%Z (mword_of_int 0x892e : mword 16)
    (mword_of_int (ISL + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)) cdec_892e exec_execute_C_MV. Qed.

  Lemma isl_10 : kernel_text -∗ instr (mword_of_int (ISL + 0x10) : mword 64) false (UTYPE (mword_of_int 0x3 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (ISL + 0x10)%Z (mword_of_int 0x00003597 : mword 32)
    (mword_of_int (ISL + 0x10) : mword 64) (UTYPE (mword_of_int 0x3 : mword 20, Regidx (mword_of_int 11), AUIPC)) sldec_auipc_a1. Qed.

  Lemma isl_14 : kernel_text -∗ instr (mword_of_int (ISL + 0x14) : mword 64) false (ITYPE (mword_of_int 0x6a2 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (ISL + 0x14)%Z (mword_of_int 0x6a258593 : mword 32)
    (mword_of_int (ISL + 0x14) : mword 64) (ITYPE (mword_of_int 0x6a2 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) sldec_addi_a1. Qed.

  Lemma isl_18 : kernel_text -∗ instr (mword_of_int (ISL + 0x18) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (ISL + 0x18)%Z (mword_of_int 0x0521 : mword 16)
    (mword_of_int (ISL + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) sldec_addi_a0 exec_execute_C_ADDI. Qed.

  Lemma isl_1a : kernel_text -∗ instr (mword_of_int (ISL + 0x1a) : mword 64) false (JAL (mword_of_int 2084056 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (ISL + 0x1a)%Z (mword_of_int 0xcd9fc0ef : mword 32)
    (mword_of_int (ISL + 0x1a) : mword 64) (JAL (mword_of_int 2084056 : mword 21, Regidx (mword_of_int 1))) sldec_jal_initlock. Qed.

  Lemma isl_1e : kernel_text -∗ instr (mword_of_int (ISL + 0x1e) : mword 64) false (STORE (mword_of_int 0x20 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 9), 8)).
  Proof. mk_base (ISL + 0x1e)%Z (mword_of_int 0x0324b023 : mword 32)
    (mword_of_int (ISL + 0x1e) : mword 64) (STORE (mword_of_int 0x20 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 9), 8)) sldec_sd_name. Qed.

  Lemma isl_22 : kernel_text -∗ instr (mword_of_int (ISL + 0x22) : mword 64) false (STORE (mword_of_int 0x0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (ISL + 0x22)%Z (mword_of_int 0x0004a023 : mword 32)
    (mword_of_int (ISL + 0x22) : mword 64) (STORE (mword_of_int 0x0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)) bdec_0004a023. Qed.

  Lemma isl_26 : kernel_text -∗ instr (mword_of_int (ISL + 0x26) : mword 64) false (STORE (mword_of_int 0x28 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (ISL + 0x26)%Z (mword_of_int 0x0204a423 : mword 32)
    (mword_of_int (ISL + 0x26) : mword 64) (STORE (mword_of_int 0x28 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)) sldec_sw_zero_pid. Qed.

  Lemma isl_2a : kernel_text -∗ instr (mword_of_int (ISL + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (ISL + 0x2a)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (ISL + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma isl_2c : kernel_text -∗ instr (mword_of_int (ISL + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (ISL + 0x2c)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (ISL + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma isl_2e : kernel_text -∗ instr (mword_of_int (ISL + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (ISL + 0x2e)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (ISL + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma isl_30 : kernel_text -∗ instr (mword_of_int (ISL + 0x30) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (ISL + 0x30)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (ISL + 0x30) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma isl_32 : kernel_text -∗ instr (mword_of_int (ISL + 0x32) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (ISL + 0x32)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (ISL + 0x32) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma isl_34 : kernel_text -∗ instr (mword_of_int (ISL + 0x34) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (ISL + 0x34)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (ISL + 0x34) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  acquiresleep @ 0x80003ecc, offsets 0x00 .. 0x44.                    *)
  (* =================================================================== *)
  Lemma asl_00 : kernel_text -∗ instr (mword_of_int (ASL + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (ASL + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (ASL + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma asl_02 : kernel_text -∗ instr (mword_of_int (ASL + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (ASL + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (ASL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma asl_04 : kernel_text -∗ instr (mword_of_int (ASL + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (ASL + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (ASL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma asl_06 : kernel_text -∗ instr (mword_of_int (ASL + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (ASL + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (ASL + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma asl_08 : kernel_text -∗ instr (mword_of_int (ASL + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (ASL + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (ASL + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma asl_0a : kernel_text -∗ instr (mword_of_int (ASL + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (ASL + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (ASL + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma asl_0c : kernel_text -∗ instr (mword_of_int (ASL + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (ASL + 0x0c)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (ASL + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma asl_0e : kernel_text -∗ instr (mword_of_int (ASL + 0x0e) : mword 64) false (ITYPE (mword_of_int 0x8 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (ASL + 0x0e)%Z (mword_of_int 0x00850913 : mword 32)
    (mword_of_int (ASL + 0x0e) : mword 64) (ITYPE (mword_of_int 0x8 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), ADDI)) sldec_addi_s2. Qed.

  Lemma asl_12 : kernel_text -∗ instr (mword_of_int (ASL + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (ASL + 0x12)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (ASL + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma asl_14 : kernel_text -∗ instr (mword_of_int (ASL + 0x14) : mword 64) false (JAL (mword_of_int 2084136 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (ASL + 0x14)%Z (mword_of_int 0xd29fc0ef : mword 32)
    (mword_of_int (ASL + 0x14) : mword 64) (JAL (mword_of_int 2084136 : mword 21, Regidx (mword_of_int 1))) sldec_jal_acq_asl. Qed.

  Lemma asl_18 : kernel_text -∗ instr (mword_of_int (ASL + 0x18) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)).
  Proof. mk_rvc (ASL + 0x18)%Z (mword_of_int 0x409c : mword 16)
    (mword_of_int (ASL + 0x18) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) sldec_lw_locked exec_execute_C_LW. Qed.

  Lemma asl_1a : kernel_text -∗ instr (mword_of_int (ASL + 0x1a) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 7 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (ASL + 0x1a)%Z (mword_of_int 0xc799 : mword 16)
    (mword_of_int (ASL + 0x1a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 7 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) sldec_beqz exec_execute_C_BEQZ. Qed.

  Lemma asl_1c : kernel_text -∗ instr (mword_of_int (ASL + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (ASL + 0x1c)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (ASL + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  Lemma asl_1e : kernel_text -∗ instr (mword_of_int (ASL + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (ASL + 0x1e)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (ASL + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma asl_20 : kernel_text -∗ instr (mword_of_int (ASL + 0x20) : mword 64) false (JAL (mword_of_int 2088986 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (ASL + 0x20)%Z (mword_of_int 0x81afe0ef : mword 32)
    (mword_of_int (ASL + 0x20) : mword 64) (JAL (mword_of_int 2088986 : mword 21, Regidx (mword_of_int 1))) sldec_jal_sleep. Qed.

  Lemma asl_24 : kernel_text -∗ instr (mword_of_int (ASL + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)).
  Proof. mk_rvc (ASL + 0x24)%Z (mword_of_int 0x409c : mword 16)
    (mword_of_int (ASL + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) sldec_lw_locked exec_execute_C_LW. Qed.

  Lemma asl_26 : kernel_text -∗ instr (mword_of_int (ASL + 0x26) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (ASL + 0x26)%Z (mword_of_int 0xfbfd : mword 16)
    (mword_of_int (ASL + 0x26) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) sldec_bnez_back exec_execute_C_BNEZ. Qed.

  Lemma asl_28 : kernel_text -∗ instr (mword_of_int (ASL + 0x28) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (ASL + 0x28)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (ASL + 0x28) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma asl_2a : kernel_text -∗ instr (mword_of_int (ASL + 0x2a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 1)), 4)).
  Proof. mk_rvc (ASL + 0x2a)%Z (mword_of_int 0xc09c : mword 16)
    (mword_of_int (ASL + 0x2a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 1)), 4)) cdec_c09c exec_execute_C_SW. Qed.

  Lemma asl_2c : kernel_text -∗ instr (mword_of_int (ASL + 0x2c) : mword 64) false (JAL (mword_of_int 2087436 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (ASL + 0x2c)%Z (mword_of_int 0xa0dfd0ef : mword 32)
    (mword_of_int (ASL + 0x2c) : mword 64) (JAL (mword_of_int 2087436 : mword 21, Regidx (mword_of_int 1))) sldec_jal_myproc_asl. Qed.

  Lemma asl_30 : kernel_text -∗ instr (mword_of_int (ASL + 0x30) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)).
  Proof. mk_rvc (ASL + 0x30)%Z (mword_of_int 0x591c : mword 16)
    (mword_of_int (ASL + 0x30) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) sldec_lw_pid_a0 exec_execute_C_LW. Qed.

  Lemma asl_32 : kernel_text -∗ instr (mword_of_int (ASL + 0x32) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 1)), 4)).
  Proof. mk_rvc (ASL + 0x32)%Z (mword_of_int 0xd49c : mword 16)
    (mword_of_int (ASL + 0x32) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 1)), 4)) sldec_sw_a5_pid exec_execute_C_SW. Qed.

  Lemma asl_34 : kernel_text -∗ instr (mword_of_int (ASL + 0x34) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (ASL + 0x34)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (ASL + 0x34) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma asl_36 : kernel_text -∗ instr (mword_of_int (ASL + 0x36) : mword 64) false (JAL (mword_of_int 2084238 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (ASL + 0x36)%Z (mword_of_int 0xd8ffc0ef : mword 32)
    (mword_of_int (ASL + 0x36) : mword 64) (JAL (mword_of_int 2084238 : mword 21, Regidx (mword_of_int 1))) sldec_jal_rel_asl. Qed.

  Lemma asl_3a : kernel_text -∗ instr (mword_of_int (ASL + 0x3a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (ASL + 0x3a)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (ASL + 0x3a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma asl_3c : kernel_text -∗ instr (mword_of_int (ASL + 0x3c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (ASL + 0x3c)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (ASL + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma asl_3e : kernel_text -∗ instr (mword_of_int (ASL + 0x3e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (ASL + 0x3e)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (ASL + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma asl_40 : kernel_text -∗ instr (mword_of_int (ASL + 0x40) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (ASL + 0x40)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (ASL + 0x40) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma asl_42 : kernel_text -∗ instr (mword_of_int (ASL + 0x42) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (ASL + 0x42)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (ASL + 0x42) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma asl_44 : kernel_text -∗ instr (mword_of_int (ASL + 0x44) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (ASL + 0x44)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (ASL + 0x44) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  releasesleep @ 0x80003f12, offsets 0x00 .. 0x36.                    *)
  (* =================================================================== *)
  Lemma rsl_00 : kernel_text -∗ instr (mword_of_int (RSL + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (RSL + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (RSL + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma rsl_02 : kernel_text -∗ instr (mword_of_int (RSL + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (RSL + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (RSL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma rsl_04 : kernel_text -∗ instr (mword_of_int (RSL + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (RSL + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (RSL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma rsl_06 : kernel_text -∗ instr (mword_of_int (RSL + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (RSL + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (RSL + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma rsl_08 : kernel_text -∗ instr (mword_of_int (RSL + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (RSL + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (RSL + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma rsl_0a : kernel_text -∗ instr (mword_of_int (RSL + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (RSL + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (RSL + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma rsl_0c : kernel_text -∗ instr (mword_of_int (RSL + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (RSL + 0x0c)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (RSL + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma rsl_0e : kernel_text -∗ instr (mword_of_int (RSL + 0x0e) : mword 64) false (ITYPE (mword_of_int 0x8 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (RSL + 0x0e)%Z (mword_of_int 0x00850913 : mword 32)
    (mword_of_int (RSL + 0x0e) : mword 64) (ITYPE (mword_of_int 0x8 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), ADDI)) sldec_addi_s2. Qed.

  Lemma rsl_12 : kernel_text -∗ instr (mword_of_int (RSL + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (RSL + 0x12)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (RSL + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma rsl_14 : kernel_text -∗ instr (mword_of_int (RSL + 0x14) : mword 64) false (JAL (mword_of_int 2084066 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (RSL + 0x14)%Z (mword_of_int 0xce3fc0ef : mword 32)
    (mword_of_int (RSL + 0x14) : mword 64) (JAL (mword_of_int 2084066 : mword 21, Regidx (mword_of_int 1))) sldec_jal_acq_rsl. Qed.

  Lemma rsl_18 : kernel_text -∗ instr (mword_of_int (RSL + 0x18) : mword 64) false (STORE (mword_of_int 0x0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (RSL + 0x18)%Z (mword_of_int 0x0004a023 : mword 32)
    (mword_of_int (RSL + 0x18) : mword 64) (STORE (mword_of_int 0x0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)) bdec_0004a023. Qed.

  Lemma rsl_1c : kernel_text -∗ instr (mword_of_int (RSL + 0x1c) : mword 64) false (STORE (mword_of_int 0x28 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (RSL + 0x1c)%Z (mword_of_int 0x0204a423 : mword 32)
    (mword_of_int (RSL + 0x1c) : mword 64) (STORE (mword_of_int 0x28 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)) sldec_sw_zero_pid. Qed.

  Lemma rsl_20 : kernel_text -∗ instr (mword_of_int (RSL + 0x20) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (RSL + 0x20)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (RSL + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma rsl_22 : kernel_text -∗ instr (mword_of_int (RSL + 0x22) : mword 64) false (JAL (mword_of_int 2088990 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (RSL + 0x22)%Z (mword_of_int 0x81efe0ef : mword 32)
    (mword_of_int (RSL + 0x22) : mword 64) (JAL (mword_of_int 2088990 : mword 21, Regidx (mword_of_int 1))) sldec_jal_wakeup. Qed.

  Lemma rsl_26 : kernel_text -∗ instr (mword_of_int (RSL + 0x26) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (RSL + 0x26)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (RSL + 0x26) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma rsl_28 : kernel_text -∗ instr (mword_of_int (RSL + 0x28) : mword 64) false (JAL (mword_of_int 2084182 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (RSL + 0x28)%Z (mword_of_int 0xd57fc0ef : mword 32)
    (mword_of_int (RSL + 0x28) : mword 64) (JAL (mword_of_int 2084182 : mword 21, Regidx (mword_of_int 1))) sldec_jal_rel_rsl. Qed.

  Lemma rsl_2c : kernel_text -∗ instr (mword_of_int (RSL + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (RSL + 0x2c)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (RSL + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma rsl_2e : kernel_text -∗ instr (mword_of_int (RSL + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (RSL + 0x2e)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (RSL + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma rsl_30 : kernel_text -∗ instr (mword_of_int (RSL + 0x30) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (RSL + 0x30)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (RSL + 0x30) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma rsl_32 : kernel_text -∗ instr (mword_of_int (RSL + 0x32) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (RSL + 0x32)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (RSL + 0x32) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma rsl_34 : kernel_text -∗ instr (mword_of_int (RSL + 0x34) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (RSL + 0x34)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (RSL + 0x34) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma rsl_36 : kernel_text -∗ instr (mword_of_int (RSL + 0x36) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (RSL + 0x36)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (RSL + 0x36) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  holdingsleep @ 0x80003f4a, offsets 0x00 .. 0x48 (48-byte frame).    *)
  (* =================================================================== *)
  Lemma hsl_00 : kernel_text -∗ instr (mword_of_int (HSL + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (HSL + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (HSL + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma hsl_02 : kernel_text -∗ instr (mword_of_int (HSL + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (HSL + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (HSL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma hsl_04 : kernel_text -∗ instr (mword_of_int (HSL + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (HSL + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (HSL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma hsl_06 : kernel_text -∗ instr (mword_of_int (HSL + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (HSL + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (HSL + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma hsl_08 : kernel_text -∗ instr (mword_of_int (HSL + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (HSL + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (HSL + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  Lemma hsl_0a : kernel_text -∗ instr (mword_of_int (HSL + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (HSL + 0x0a)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (HSL + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  Lemma hsl_0c : kernel_text -∗ instr (mword_of_int (HSL + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (HSL + 0x0c)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (HSL + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma hsl_0e : kernel_text -∗ instr (mword_of_int (HSL + 0x0e) : mword 64) false (ITYPE (mword_of_int 0x8 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (HSL + 0x0e)%Z (mword_of_int 0x00850913 : mword 32)
    (mword_of_int (HSL + 0x0e) : mword 64) (ITYPE (mword_of_int 0x8 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), ADDI)) sldec_addi_s2. Qed.

  Lemma hsl_12 : kernel_text -∗ instr (mword_of_int (HSL + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (HSL + 0x12)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (HSL + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma hsl_14 : kernel_text -∗ instr (mword_of_int (HSL + 0x14) : mword 64) false (JAL (mword_of_int 2084010 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (HSL + 0x14)%Z (mword_of_int 0xcabfc0ef : mword 32)
    (mword_of_int (HSL + 0x14) : mword 64) (JAL (mword_of_int 2084010 : mword 21, Regidx (mword_of_int 1))) sldec_jal_acq_hsl. Qed.

  Lemma hsl_18 : kernel_text -∗ instr (mword_of_int (HSL + 0x18) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)).
  Proof. mk_rvc (HSL + 0x18)%Z (mword_of_int 0x409c : mword 16)
    (mword_of_int (HSL + 0x18) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) sldec_lw_locked exec_execute_C_LW. Qed.

  Lemma hsl_1a : kernel_text -∗ instr (mword_of_int (HSL + 0x1a) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 12 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (HSL + 0x1a)%Z (mword_of_int 0xef81 : mword 16)
    (mword_of_int (HSL + 0x1a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 12 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) sldec_bnez_fwd exec_execute_C_BNEZ. Qed.

  Lemma hsl_1c : kernel_text -∗ instr (mword_of_int (HSL + 0x1c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)).
  Proof. mk_rvc (HSL + 0x1c)%Z (mword_of_int 0x4481 : mword 16)
    (mword_of_int (HSL + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)) sldec_li_s1_0 exec_execute_C_LI. Qed.

  Lemma hsl_1e : kernel_text -∗ instr (mword_of_int (HSL + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (HSL + 0x1e)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (HSL + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma hsl_20 : kernel_text -∗ instr (mword_of_int (HSL + 0x20) : mword 64) false (JAL (mword_of_int 2084134 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (HSL + 0x20)%Z (mword_of_int 0xd27fc0ef : mword 32)
    (mword_of_int (HSL + 0x20) : mword 64) (JAL (mword_of_int 2084134 : mword 21, Regidx (mword_of_int 1))) sldec_jal_rel_hsl. Qed.

  Lemma hsl_24 : kernel_text -∗ instr (mword_of_int (HSL + 0x24) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (HSL + 0x24)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (HSL + 0x24) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma hsl_26 : kernel_text -∗ instr (mword_of_int (HSL + 0x26) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (HSL + 0x26)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (HSL + 0x26) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma hsl_28 : kernel_text -∗ instr (mword_of_int (HSL + 0x28) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (HSL + 0x28)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (HSL + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma hsl_2a : kernel_text -∗ instr (mword_of_int (HSL + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (HSL + 0x2a)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (HSL + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma hsl_2c : kernel_text -∗ instr (mword_of_int (HSL + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (HSL + 0x2c)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (HSL + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma hsl_2e : kernel_text -∗ instr (mword_of_int (HSL + 0x2e) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (HSL + 0x2e)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (HSL + 0x2e) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma hsl_30 : kernel_text -∗ instr (mword_of_int (HSL + 0x30) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (HSL + 0x30)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (HSL + 0x30) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma hsl_32 : kernel_text -∗ instr (mword_of_int (HSL + 0x32) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (HSL + 0x32)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (HSL + 0x32) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  Lemma hsl_34 : kernel_text -∗ instr (mword_of_int (HSL + 0x34) : mword 64) false (LOAD (mword_of_int 0x28 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 19), false, 4)).
  Proof. mk_base (HSL + 0x34)%Z (mword_of_int 0x0284a983 : mword 32)
    (mword_of_int (HSL + 0x34) : mword 64) (LOAD (mword_of_int 0x28 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 19), false, 4)) sldec_lw_s3_pid. Qed.

  Lemma hsl_38 : kernel_text -∗ instr (mword_of_int (HSL + 0x38) : mword 64) false (JAL (mword_of_int 2087298 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (HSL + 0x38)%Z (mword_of_int 0x983fd0ef : mword 32)
    (mword_of_int (HSL + 0x38) : mword 64) (JAL (mword_of_int 2087298 : mword 21, Regidx (mword_of_int 1))) sldec_jal_myproc_hsl. Qed.

  Lemma hsl_3c : kernel_text -∗ instr (mword_of_int (HSL + 0x3c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 1)), false, 4)).
  Proof. mk_rvc (HSL + 0x3c)%Z (mword_of_int 0x5904 : mword 16)
    (mword_of_int (HSL + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 1)), false, 4)) sldec_lw_s1_procpid exec_execute_C_LW. Qed.

  Lemma hsl_3e : kernel_text -∗ instr (mword_of_int (HSL + 0x3e) : mword 64) false (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 9), Regidx (mword_of_int 9), SUB)).
  Proof. mk_base (HSL + 0x3e)%Z (mword_of_int 0x413484b3 : mword 32)
    (mword_of_int (HSL + 0x3e) : mword 64) (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 9), Regidx (mword_of_int 9), SUB)) sldec_sub. Qed.

  Lemma hsl_42 : kernel_text -∗ instr (mword_of_int (HSL + 0x42) : mword 64) false (ITYPE (mword_of_int 0x1 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), SLTIU)).
  Proof. mk_base (HSL + 0x42)%Z (mword_of_int 0x0014b493 : mword 32)
    (mword_of_int (HSL + 0x42) : mword 64) (ITYPE (mword_of_int 0x1 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), SLTIU)) sldec_seqz. Qed.

  Lemma hsl_46 : kernel_text -∗ instr (mword_of_int (HSL + 0x46) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (HSL + 0x46)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (HSL + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  Lemma hsl_48 : kernel_text -∗ instr (mword_of_int (HSL + 0x48) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (HSL + 0x48)%Z (mword_of_int 0xbfd9 : mword 16)
    (mword_of_int (HSL + 0x48) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")), zreg)) cdec_bfd9 exec_execute_C_J. Qed.

End WpSleeplockDecode.
