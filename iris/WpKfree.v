(* WpKfree.v -- instruction-level proof of the kernel's [kfree] (0x80000a38)
   against the allocator spec in KallocInv.v.

   kfree is a whole-function S-mode proof in the mould of [wp_release]
   (WpRelease.v) and [wp_acquire_lock] (WpAcquireLock.v): it threads the S-mode
   machine configuration (mstatus/pmp/pte/tlb) through every instruction and
   CALLS the sub-functions memset / acquire / release via [jal], discharging
   each callee's whole-function WP.  The novel content is the free-list PUSH,
   which is discharged by KallocInv's transfer lemma [kmem_res_push] together
   with [page_head8_word_at] / [run_page_page_own].

   Structural sibling: [WpKalloc.v] (same branch).  This file mirrors its
   statement shape (S-mode config + frame windows) and its prologue proof. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
From iris.base_logic.lib Require Import ghost_var.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText WpAuipc.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore WpSmodeGpr.
Require Import WpSmodeBtype.
Require Import WpSmodeItype.
Require Import WpSmodeJal.
Require Import WpSmodeJalr.
Require Import WpSmodeLoad.
Require Import WpSmodeRtype.
Require Import WpSmodeShiftiop.
Require Import WpSmodeStore.
Require Import WpSmodeUtype.
Require Import WpMycpu.
Require Import WpSmodeBtype.
Require Import WpSmodeLoad.
Require Import WpSmodeStore.
Require Import WpLock.
Require Import WpAcquireLock WpRelease WpMemsetPage.
Require Import WpSmodeBtype.
Require Import WpSmodeLoad.
Require Import WpSmodeStore.
Require Import WpHoldingInv.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv WpKallocDecode.
Require Import PtAdBits PtTree PtTreeAdue KptTree SmodeCorePt.
Require Import WpSmodePtLeaves WpSmodePtAlu WpSmodePtBtype WpSmodePtCtl.
Require Import WpSmodePtMem WpSmodePtMemWrap WpSmodePtLock WpSmodePtUart.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Register-generic execute helpers for SLTU (the bounds-check compares), *)
(* mirroring [exec_execute_RTYPE_OR{,_gpr}] in WpGprLogic.  The model's    *)
(* SLTU writes [zero_extend' 64 (bool_to_bit (a <u b))].                   *)
(* ===================================================================== *)
(* gpr_sltu_val / exec_execute_RTYPE_SLTU{,_gpr} relocated to WpMmodeLeafBase.v *)

(* [zopz0zI_u x y = Z.ltb (uint x) (uint y)]; a false compare packs to 0. *)
Lemma sltu_false_zero (a b : mword 64) :
  zopz0zI_u a b = false ->
  (zero_extend' 64 (bool_to_bit (zopz0zI_u a b)) : mword 64) = mword_of_int 0.
Proof. intro H. rewrite H. apply bv_eq; vm_compute; reflexivity. Qed.

(* [slli p 0x34] with [p] 4096-aligned is zero: the low 12 bits (all zero)
   are the only ones that survive a 52-bit left shift in 64 bits. *)
Lemma shift_bits_left52_zero (p : mword 64) :
  (uint p) mod 4096 = 0 ->
  shift_bits_left p (subrange_vec_dec (mword_of_int 52 : mword 6) (Z.sub log2_xlen 1) 0) = mword_of_int 0.
Proof.
  intro Hal.
  assert (Hn : shift_bits_left p (subrange_vec_dec (mword_of_int 52 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftl p 52).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  rewrite Hn. apply bv_eq.
  unfold shiftl, with_word, get_word, MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  assert (Hsh : bv_unsigned (MachineWord.N_to_word (MachineWord.Z_idx 64) (MachineWord.Z_idx 52)) = 52).
  { unfold MachineWord.N_to_word, MachineWord.Z_idx. rewrite Z_to_bv_unsigned.
    apply bv_wrap_small. unfold bv_modulus. simpl. lia. }
  rewrite Hsh.
  assert (Hup : uint p = bv_unsigned p).
  { unfold uint, MachineWord.word_to_N, get_word. rewrite Z2N.id; [reflexivity|].
    pose proof (bv_unsigned_in_range _ p). lia. }
  rewrite Hup in Hal.
  apply Z.mod_divide in Hal; [| lia]. destruct Hal as [q Hq].
  assert (Hz0 : bv_unsigned (mword_of_int 0 : mword 64) = 0) by reflexivity.
  rewrite Hz0.
  rewrite Z.shiftl_mul_pow2; [| lia].
  rewrite Hq.
  unfold bv_wrap, bv_modulus.
  replace (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (4096 * 2 ^ 52) by (vm_compute; reflexivity).
  rewrite <- Z.mul_assoc. apply Z.mod_mul. vm_compute; discriminate.
Qed.

(* kfree's epilogue [c.addi16sp +32] undoes its prologue [c.addi16sp -32],
   restoring sp to its entry value.  (mword_of_int 32 : mword 6) is -32 in
   6-bit two's complement; [caddi16sp_imm (mword_of_int 2)] is +32. *)
Lemma kfree_sp_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64) = 18446744073709551584) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64) = 32) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551584 + 32) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

Section Kfree.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation KF := KernelSyms.kfree.
  Notation PO := KernelSyms.push_off.

  (* ============================================================= *)
  (* kfree: whole-function S-mode WP.  COMPLETE (Qed, no admits).     *)
  (* Covers the prologue (four saves + addi4spn), the auipc/addi      *)
  (* loading a5 := <end>, the bounds/alignment check region +14..+2c  *)
  (* (both panic branches shown dead from page_valid), the memset     *)
  (* argument setup and [jal memset] (wp_memset_page), the [jal       *)
  (* acquire] (wp_acquire_lock), the freelist push (p->next := head;  *)
  (* kmem.freelist := p), the [jal release] (wp_release), and the     *)
  (* epilogue (four c.ldsp restores + c.addi16sp + c.ret).            *)
  (* ============================================================= *)

  (* ===== [smode_config] leaf wrappers kfree's body needs ===== *)

  Lemma wp_auipc_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_auipc_s_pt root_ppn Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_addi4_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_addi4_s_pt root_ppn Φ pc rd rs1 imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_sd_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ea.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_sd_s_pt root_ppn Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_ld_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : bv 64) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    ea ↦₈{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ea Hrd.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_ld_s_pt root_ppn Φ pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
 Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  (* local wp_gpr_write_s_config_base_scfg_pt engine copy removed: sites now use
     specific per-instruction lemmas (wp_sltu_s_pt / wp_slli_s_pt / ...). *)
  Lemma wp_cslli_gpr_s_config_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rsd : regidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    rsd = Regidx rd ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrsd Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cslli_gpr_s_config_pt root_ppn Φ pc rsd rd shamt m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrsd Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_kfree (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γ : gname) (lk fl : mword 64)
      (m : gmap regidx (mword 64))
      (qcpuold : bv 64)
      (qnoff qintena_old : mword 32) (a0f : mword 64)
      (γc : gname) (bsie : mword 1)
      (n : nat)
      :
    let pcE : mword 64 := mword_of_int KF in
    let p := m !!! Regidx (mword_of_int 10 : mword 5) in
    let sp0 := m !!! Regidx csp_rs1 in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let q_noff := add_vec a0f (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let q_intena := add_vec a0f (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let q_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    (* push_off's noff increment value (function of the ghost noff alone) *)
    let q_noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 qnoff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let q_noff_store := (autocast (T := mword) (subrange_vec_dec q_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    (14 <= n)%nat ->
    (* S-mode config facts + the pop_off sstatus fact are folded into
       [smode_config γc] below; acquire's mycpu pins reduce to the single
       tp-only fact [a0f = mycpu_ret ..]. *)
    eq_vec (qcpuold : mword 64) (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = false ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    lk = mword_of_int KernelSyms.kmem ->
    fl = mword_of_int (KernelSyms.kmem + 24) ->
    a0f = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 q_noff_store) = false ->
    eq_vec (sign_extend' 64
       (if eq_vec (sign_extend' 64 qnoff) zero_reg then (zeros' 32) else qintena_old)) zero_reg = true ->
    smode_config γc (DfracOwn 1) -∗
    ghost_var γc (1/2) bsie -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    is_kmem γ lk fl -∗
    kfree_pre p -∗
    stack_own sp0 n -∗
    q_noff ↦₄ qnoff -∗
    q_intena ↦₄ qintena_old -∗
    q_cpu ↦₈ qcpuold -∗
    ( ∀ mr,
      smode_config γc (DfracOwn 1) -∗
      ghost_var γc (1/2) bsie -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗
      ⌜ callee_saved m mr ⌝ -∗
      stack_own sp0 n -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pcE p sp0 ret_tgt q_noff q_intena q_cpu q_noff_a5 q_noff_store Hn Hcpune Hretm Hlk Hfl Ha0fcpu Hnoffpos Hintena0.
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcfg Htoken Htlbinv
             #Htext Hpc Hfile #Hkmem Hpre Hstk Hqnoff Hqint Hqcpu Hcont".
    (* peel kfree's own 4-slot frame [spr, spr+32); the deep tail
       [stack_own spr (n-4)] is lent to memset/acquire/release in turn. *)
    iDestruct (stack_own_split_1 sp0 4 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Htop".
    iDestruct "Htop" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vr0)  "Hr0".
    assert (Hb1 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 4 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hr0".
    iEval (rewrite Hsprstk) in "Hdeep".
    iPoseProof (kfi_00 with "Htext") as "Hi00".
    iPoseProof (kfi_02 with "Htext") as "Hi02".
    iPoseProof (kfi_04 with "Htext") as "Hi04".
    iPoseProof (kfi_06 with "Htext") as "Hi06".
    iPoseProof (kfi_08 with "Htext") as "Hi08".
    iPoseProof (kfi_0a with "Htext") as "Hi0a".
    iPoseProof (kfi_0c with "Htext") as "Hi0c".
    iPoseProof (kfi_10 with "Htext") as "Hi10".
    iPoseProof (kfi_14 with "Htext") as "Hi14".
    iPoseProof (kfi_18 with "Htext") as "Hi18".
    iPoseProof (kfi_1a with "Htext") as "Hi1a".
    iPoseProof (kfi_1c with "Htext") as "Hi1c".
    iPoseProof (kfi_1e with "Htext") as "Hi1e".
    iPoseProof (kfi_22 with "Htext") as "Hi22".
    iPoseProof (kfi_24 with "Htext") as "Hi24".
    iPoseProof (kfi_26 with "Htext") as "Hi26".
    iPoseProof (kfi_28 with "Htext") as "Hi28".
    iPoseProof (kfi_2c with "Htext") as "Hi2c".
    iPoseProof (kfi_2e with "Htext") as "Hi2e".
    iPoseProof (kfi_30 with "Htext") as "Hi30".
    (* the caller-supplied page precondition: validity + full ownership *)
    iDestruct "Hpre" as "[%Hpv Hpown]".
    assert (Hpal : (uint p) mod 4096 = 0) by (destruct Hpv as [Ha _]; exact Ha).
    assert (Hprlo : 0x80023558 <= uint p) by (destruct Hpv as [_ [Hlo _]]; exact Hlo).
    assert (Hprhi : uint p < 0x88000000) by (destruct Hpv as [_ [_ Hhi]]; exact Hhi).
    assert (Hsltu14 : zopz0zI_u p (mword_of_int 0x80023558 : mword 64) = false).
    { unfold zopz0zI_u. apply Z.ltb_ge.
      replace (uint (mword_of_int 0x80023558 : mword 64)) with 0x80023558 by (vm_compute; reflexivity).
      lia. }
    assert (Hsltu1e : zopz0zI_u (mword_of_int 0x87FFFFFF : mword 64) p = false).
    { unfold zopz0zI_u. apply Z.ltb_ge.
      replace (uint (mword_of_int 0x87FFFFFF : mword 64)) with 0x87FFFFFF by (vm_compute; reflexivity).
      lia. }
    (* +0x00 c.addi16sp sp,-32 *)
    iApply (wp_caddi_gpr_s_config_scfg_pt root_ppn γc Φ pcE csp_rs1 (mword_of_int 32 : mword 6) m
              (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1; apply lookup_total_insert).
    assert (Hpp02 : add_vec_int pcE 2 = mword_of_int (KF + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 vr24 (dq:=DfracOwn 1)

              with "Hcfg Htlbinv Hpc Hfile Hi02 [Hr24] [-]").
    { iEval (rewrite HspR1). iExact "Hr24". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KF + 0x02) : mword 64) 2 = mword_of_int (KF + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 vr16 (dq:=DfracOwn 1)

              with "Hcfg Htlbinv Hpc Hfile Hi04 [Hr16] [-]").
    { iEval (rewrite HspR1). iExact "Hr16". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KF + 0x04) : mword 64) 2 = mword_of_int (KF + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 vr8 (dq:=DfracOwn 1)

              with "Hcfg Htlbinv Hpc Hfile Hi06 [Hr8] [-]").
    { iEval (rewrite HspR1). iExact "Hr8". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KF + 0x06) : mword 64) 2 = mword_of_int (KF + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,0(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              R1 vr0 (dq:=DfracOwn 1)

              with "Hcfg Htlbinv Hpc Hfile Hi08 [Hr0] [-]").
    { iEval (rewrite HspR1). iExact "Hr0". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr0".
    assert (Hpp0a : add_vec_int (mword_of_int (KF + 0x08) : mword 64) 2 = mword_of_int (KF + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_gpr_s_config_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 (dq:=DfracOwn 1)

              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0c : add_vec_int (mword_of_int (KF + 0x0a) : mword 64) 2 = mword_of_int (KF + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c auipc a5,0x23 *)
    iApply (wp_auipc_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x0c)) (mword_of_int 15 : mword 5) (mword_of_int 0x23 : mword 20)
              R2 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (mword_of_int (KF + 0x0c) : mword 64) (auipc_off (mword_of_int 0x23 : mword 20)))]> R2).
    assert (Hpp10 : add_vec_int (mword_of_int (KF + 0x0c) : mword 64) 4 = mword_of_int (KF + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 addi a5,a5,-1260  (a5 := <end> = 0x80023558) *)
    iApply (wp_addi4_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x10)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 0xb06 : mword 12)
              R3 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 0xb06 : mword 12)))]> R3).
    assert (Hpp14 : add_vec_int (mword_of_int (KF + 0x10) : mword 64) 4 = mword_of_int (KF + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* a0 (= the page p) and a5 (= <end>) after the prologue+auipc/addi *)
    assert (Hp10 : R4 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hend : R4 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x80023558).
    { rewrite /R4 lookup_total_insert. rewrite /R3 lookup_total_insert.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x14 sltu a4,a0,a5  (a4 := p <u end = 0, since end <= p) *)
    iApply (wp_sltu_s_pt root_ppn γc Φ (mword_of_int (KF + 0x14))
              (mword_of_int 14 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 15 : mword 5)
              (mword_of_int 0 : mword 64)
              R4 (dq:=DfracOwn 1)

              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hp10 Hend; exact (sltu_false_zero p (mword_of_int 0x80023558) Hsltu14))
              with "Hcfg Htlbinv Hpc Hfile Hi14 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R5 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R4).
    assert (Hpp18 : add_vec_int (mword_of_int (KF + 0x14) : mword 64) 4 = mword_of_int (KF + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.li a5,17 *)
    iApply (wp_cli_s_pt root_ppn γc Φ (mword_of_int (KF + 0x18))
              (mword_of_int 15 : mword 5) (mword_of_int 17 : mword 6)
              (mword_of_int 17 : mword 64)
              R5 (dq:=DfracOwn 1)

              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi18 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 17 : mword 64)]> R5).
    assert (Hli : R6 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 17)
      by (rewrite /R6 lookup_total_insert; reflexivity).
    assert (Hpp1a : add_vec_int (mword_of_int (KF + 0x18) : mword 64) 2 = mword_of_int (KF + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.slli a5,0x1b  (a5 := 17 << 27 = PHYSTOP) *)
    iApply (wp_cslli_gpr_s_config_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x1a)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 27 : mword 6)
              R6 (dq:=DfracOwn 1)

              ltac:(reflexivity) ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi1a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (shift_bits_left (R6 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 27 : mword 6) (Z.sub log2_xlen 1) 0))]> R6).
    assert (Hphys : R7 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x88000000).
    { rewrite /R7 lookup_total_insert. rewrite Hli. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp1c : add_vec_int (mword_of_int (KF + 0x1a) : mword 64) 2 = mword_of_int (KF + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.addi a5,-1  (a5 := PHYSTOP - 1) *)
    iApply (wp_caddi_gpr_s_config_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              R7 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi1c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (R7 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> R7).
    assert (Hphysm1 : R8 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x87FFFFFF).
    { rewrite /R8 lookup_total_insert. rewrite Hphys. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp10_8 : R8 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hp10. }
    assert (Hpp1e : add_vec_int (mword_of_int (KF + 0x1c) : mword 64) 2 = mword_of_int (KF + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e sltu a5,a5,a0  (a5 := (PHYSTOP-1) <u p = 0, since p <= PHYSTOP-1) *)
    iApply (wp_sltu_s_pt root_ppn γc Φ (mword_of_int (KF + 0x1e))
              (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 64)
              R8 (dq:=DfracOwn 1)

              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hphysm1 Hp10_8; exact (sltu_false_zero (mword_of_int 0x87FFFFFF) p Hsltu1e))
              with "Hcfg Htlbinv Hpc Hfile Hi1e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R8).
    assert (Hor14 : R9 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0).
    { rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert; reflexivity. }
    assert (Hor15 : R9 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0)
      by (rewrite /R9 lookup_total_insert; reflexivity).
    assert (Hpp22 : add_vec_int (mword_of_int (KF + 0x1e) : mword 64) 4 = mword_of_int (KF + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 c.or a5,a4  (a5 := a5 | a4 = 0) *)
    iApply (wp_cor_s_pt root_ppn γc Φ (mword_of_int (KF + 0x22))
              (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              (mword_of_int 0 : mword 64)
              R9 (dq:=DfracOwn 1)

              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hor15 Hor14; apply bv_eq; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi22 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R9).
    assert (Hbnez24 : R10 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0)
      by (rewrite /R10 lookup_total_insert; reflexivity).
    assert (Hp10_10 : R10 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hp10_8. }
    assert (Hpp24 : add_vec_int (mword_of_int (KF + 0x22) : mword 64) 2 = mword_of_int (KF + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 c.bnez a5,+60  NOT taken (a5 = 0): both bounds hold, panic avoided *)
    iApply (wp_cbnez_fall_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x24)) (mword_of_int 30 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              R10 (dq:=DfracOwn 1)

              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hbnez24; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi24 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp26 : add_vec_int (mword_of_int (KF + 0x24) : mword 64) 2 = mword_of_int (KF + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* +0x26 c.mv s1,a0  (s1 := p) *)
    iApply (wp_cmv_gpr_s_config_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x26)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R10 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi26 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R11 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R10 !!! Regidx (mword_of_int 10 : mword 5)))]> R10).
    assert (Hp10_11 : R11 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hp10_10. }
    assert (Hpp28 : add_vec_int (mword_of_int (KF + 0x26) : mword 64) 2 = mword_of_int (KF + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28 slli a5,a0,0x34  (a5 := p << 52 = 0, since p is 4096-aligned) *)
    iApply (wp_slli_s_pt root_ppn γc Φ (mword_of_int (KF + 0x28))
              (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 52 : mword 6)
              (mword_of_int 0 : mword 64)
              R11 (dq:=DfracOwn 1)

              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hp10_11; exact (shift_bits_left52_zero p Hpal))
              with "Hcfg Htlbinv Hpc Hfile Hi28 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R12 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R11).
    assert (Hbnez2c : R12 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0)
      by (rewrite /R12 lookup_total_insert; reflexivity).
    assert (Hpp2c : add_vec_int (mword_of_int (KF + 0x28) : mword 64) 4 = mword_of_int (KF + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* +0x2c c.bnez a5,+60  NOT taken (a5 = 0): 4096-alignment holds, panic avoided *)
    iApply (wp_cbnez_fall_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x2c)) (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              R12 (dq:=DfracOwn 1)

              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hbnez2c; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi2c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp2e : add_vec_int (mword_of_int (KF + 0x2c) : mword 64) 2 = mword_of_int (KF + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.lui a2,0x1  (a2 := 4096, the memset length) *)
    iApply (wp_clui_s_pt root_ppn γc Φ (mword_of_int (KF + 0x2e))
              (mword_of_int 12 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6))
              (mword_of_int 4096 : mword 64)
              R12 (dq:=DfracOwn 1)

              ltac:(vm_compute; discriminate)
              ltac:(unfold luival; apply bv_eq; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi2e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R13 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 4096 : mword 64)]> R12).
    assert (Hpp30 : add_vec_int (mword_of_int (KF + 0x2e) : mword 64) 2 = mword_of_int (KF + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.li a1,1  (a1 := 1, the memset fill byte) *)
    iApply (wp_cli_s_pt root_ppn γc Φ (mword_of_int (KF + 0x30))
              (mword_of_int 11 : mword 5) (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64)
              R13 (dq:=DfracOwn 1)

              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi30 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R14 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> R13).
    assert (Hpp32 : add_vec_int (mword_of_int (KF + 0x30) : mword 64) 2 = mword_of_int (KF + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* ---- a0 (=p), a1 (=1), a2 (=4096), sp (=spr) at the memset call ---- *)
    assert (Hp10_14 : R14 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R14 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R13 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hp10. }
    assert (Hsp_14 : R14 !!! Regidx csp_rs1 = spr).
    { rewrite /R14 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R13 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspR1. }
    iPoseProof (kfi_32 with "Htext") as "Hi32".
    (* +0x32 jal ra,memset : link ra := +0x36, jump to memset entry *)
    iApply (wp_jal_gpr_s_zca_pt root_ppn γc Φ (mword_of_int (KF + 0x32)) (mword_of_int 1 : mword 5) (mword_of_int 0x250 : mword 21)
              R14 1%Qp
 ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi32 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (Mms := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KF + 0x32) : mword 64) 4)]> R14).
    assert (Htgtms : add_vec (mword_of_int (KF + 0x32) : mword 64) (sign_extend' 64 (mword_of_int 0x250 : mword 21)) = mword_of_int KernelSyms.memset)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtms) in "Hpc".
    (* ---- Mms register lookups ---- *)
    assert (HMmsa0 : Mms !!! Regidx (mword_of_int 10 : mword 5) = p)
      by (rewrite /Mms lookup_total_insert_ne; [ exact Hp10_14 | vm_compute; discriminate ]).
    assert (HMmsa1 : Mms !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 1 : mword 64)).
    { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R14 lookup_total_insert. reflexivity. }
    assert (HMmsa2 : Mms !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int 4096 : mword 64)).
    { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R14 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R13 lookup_total_insert. reflexivity. }
    assert (HMmsra : Mms !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (KF + 0x36)).
    { rewrite /Mms lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    assert (HMmssp : Mms !!! Regidx csp_rs1 = spr)
      by (rewrite /Mms lookup_total_insert_ne; [ exact Hsp_14 | vm_compute; discriminate ]).
    (* +0x32 memset(p, 1, 4096) : fills the page, returns [page_own p] + gpr_file
       (ra/s0/s1/s2/sp/tp preserved).  The return target KF+0x36 is 2-aligned;
       wp_memset_page now supports that (Zca return), so only bit0 = 0 is needed.
       memset's stack frame is the deep tail [stack_own spr (n-4)] (spr = its
       entry sp), returned intact. *)
    iApply (wp_memset_page root_ppn Φ Mms (mword_of_int 1 : mword 64) (n - 4)%nat
              γc (dq:=DfracOwn 1)
              ltac:(lia)
              ltac:(rewrite HMmsa0; exact Hpv)
              HMmsa1 HMmsa2

              ltac:(rewrite HMmsra; vm_compute; reflexivity)
              with "Hcfg Htlbinv Htext Hpc Hfile [Hdeep] [Hpown] [-]").
    { iEval (rewrite HMmssp). iExact "Hdeep". }
    { iEval (rewrite HMmsa0). iExact "Hpown". }
    iIntros (mfp) "Hcfg Htlbinv Hpc Hstk Hpage Hfile %Hpinsf".
    iEval (rewrite HMmsa0) in "Hpage".
    iEval (rewrite HMmssp) in "Hstk". iRename "Hstk" into "Hdeep".
    unfold callee_saved in Hpinsf.
    destruct Hpinsf as (Hfsp & Hftp & Hfs0 & Hfs1 & Hfs2 & Hfs3 & Hfs4 & Hfs5 & Hfs6 & Hfs7 & Hfs8 & Hfs9 & Hfs10 & Hfs11).
    assert (Hpc36 : update_vec_dec (add_vec (Mms !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (KF + 0x36)).
    { rewrite HMmsra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc36) in "Hpc".
    (* ---- memset preserved sp and tp; carry them to the acquire-entry map ---- *)
    assert (Hmfpsp : mfp !!! Regidx csp_rs1 = spr) by (rewrite Hfsp HMmssp; reflexivity).
    assert (HMmstp : Mms !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R14 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R13 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hmfptp : mfp !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5))
      by (rewrite Hftp HMmstp; reflexivity).
    iPoseProof (kfi_36 with "Htext") as "Hi36".
    iPoseProof (kfi_3a with "Htext") as "Hi3a".
    iPoseProof (kfi_3e with "Htext") as "Hi3e".
    (* +0x36 auipc s2,0x12 *)
    iApply (wp_auipc_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x36)) (mword_of_int 18 : mword 5) (mword_of_int 0x12 : mword 20)
              mfp (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi36 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (S1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (mword_of_int (KF + 0x36) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))]> mfp).
    assert (Hpp3a : add_vec_int (mword_of_int (KF + 0x36) : mword 64) 4 = mword_of_int (KF + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    (* +0x3a addi s2,s2,-1862  (s2 := &kmem) *)
    iApply (wp_addi4_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x3a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0x8ac : mword 12)
              S1 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (S2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (S1 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 0x8ac : mword 12)))]> S1).
    assert (Hs2kmem : S2 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /S2 lookup_total_insert. rewrite /S1 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp3e : add_vec_int (mword_of_int (KF + 0x3a) : mword 64) 4 = mword_of_int (KF + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    (* +0x3e c.mv a0,s2 *)
    iApply (wp_cmv_gpr_s_config_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x3e)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              S2 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi3e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (S3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (S2 !!! Regidx (mword_of_int 18 : mword 5)))]> S2).
    assert (Hpp40 : add_vec_int (mword_of_int (KF + 0x3e) : mword 64) 2 = mword_of_int (KF + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    (* +0x40 jal ra,acquire *)
    iPoseProof (kfi_40 with "Htext") as "Hi40".
    iApply (wp_jal_gpr_s_zca_pt root_ppn γc Φ (mword_of_int (KF + 0x40)) (mword_of_int 1 : mword 5) (mword_of_int 0x182 : mword 21)
              S3 1%Qp
 ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (Kacq := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KF + 0x40) : mword 64) 4)]> S3).
    assert (Htgtacq : add_vec (mword_of_int (KF + 0x40) : mword 64) (sign_extend' 64 (mword_of_int 0x182 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    (* ---- the acquire-entry map [Kacq] lookups ---- *)
    assert (HKacqcsp : Kacq !!! Regidx csp_rs1 = spr).
    { rewrite /Kacq lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S1 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hmfpsp. }
    assert (HKacqtp : Kacq !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /Kacq lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S1 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hmfptp. }
    assert (HKacqa0 : Kacq !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /Kacq lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S3 lookup_total_insert. rewrite Hs2kmem. apply add_vec_zero_l. }
    assert (HKacqra : Kacq !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KF + 0x40) : mword 64) 4)
      by (rewrite /Kacq; apply lookup_total_insert).
    assert (HKacqs2 : Kacq !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /Kacq lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S3 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs2kmem. }
    assert (Hmacq_s1 : Kacq !!! Regidx (mword_of_int 9 : mword 5) = p).
    { rewrite /Kacq lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S1 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hfs1.
      rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R14 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R13 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R11 lookup_total_insert.
      rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hp10. apply add_vec_zero_l. }
    (* ---- acquire(&kmem) ---- *)
    iApply (wp_acquire_lock root_ppn Φ γ (kmem_res fl) Kacq
              qcpuold (n - 4)%nat qnoff qintena_old a0f γc bsie
 ltac:(lia)
              ltac:(rewrite HKacqtp; exact (eq_sym Ha0fcpu))
              ltac:(rewrite HKacqtp; exact Hcpune)
              ltac:(rewrite HKacqra; vm_compute; reflexivity)
              with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                    [Hdeep] Hqnoff Hqint [Hkmem] [Hqcpu] [-]").
    { iEval (rewrite HKacqcsp). iExact "Hdeep". }
    { iEval (rewrite HKacqa0 -Hlk). rewrite /is_kmem. iExact "Hkmem". }
    { iEval (rewrite HKacqa0 -Hlk). iExact "Hqcpu". }
    iIntros (macq) "Hcfg Htoken Htlbinv Hpc Htok HRres Hfile %Hacqpins
             Hdeep Hanoff Haint Hacpu".
    iEval (rewrite HKacqcsp) in "Hdeep".
    (* pc = ret_tgt(Kacq) = +0x44 ; hold [locked γ] + [kmem_res fl] *)
    assert (Hpc44 : update_vec_dec (add_vec (Kacq !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (KF + 0x44)).
    { rewrite HKacqra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc44) in "Hpc".
    unfold callee_saved in Hacqpins.
    destruct Hacqpins as (Hqsp & Hqtp & Hqs0 & Hqs1 & Hqs2 & Hqs3 & Hqs4 & Hqs5 & Hqs6 & Hqs7 & Hqs8 & Hqs9 & Hqs10 & Hqs11).
    assert (Hs1p : macq !!! Regidx (mword_of_int 9 : mword 5) = p) by (rewrite Hqs1; exact Hmacq_s1).
    assert (Hs2km : macq !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem) by (rewrite Hqs2; exact HKacqs2).
    iPoseProof (kfi_44 with "Htext") as "Hi44".
    iPoseProof (kfi_48 with "Htext") as "Hi48".
    iPoseProof (kfi_4a with "Htext") as "Hi4a".
    (* the freelist head lives at fl = &kmem + 24 *)
    iDestruct "HRres" as (head pages) "[Hflw Hchain]".
    assert (Hldaddr : add_vec (macq !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 0x18 : mword 12)) = fl).
    { rewrite Hs2km Hfl. apply bv_eq; vm_compute; reflexivity. }
    (* +0x44 ld a5,24(s2) : a5 := *(kmem.freelist) = head *)
    iApply (wp_ld_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x44)) (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0x18 : mword 12)
              macq head (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi44 [Hflw] [-]").
    { iEval (rewrite -Hldaddr) in "Hflw". rewrite /word_at. iExact "Hflw". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hflw".
    iEval (rewrite Hldaddr) in "Hflw".
    set (Rld := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg head]> macq).
    assert (HRlds1 : Rld !!! Regidx (mword_of_int 9 : mword 5) = p)
      by (rewrite /Rld lookup_total_insert_ne; [ exact Hs1p | vm_compute; discriminate ]).
    assert (HRlds2 : Rld !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem)
      by (rewrite /Rld lookup_total_insert_ne; [ exact Hs2km | vm_compute; discriminate ]).
    assert (HRlda5 : Rld !!! Regidx (mword_of_int 15 : mword 5) = head)
      by (rewrite /Rld; apply lookup_total_insert).
    assert (Hpp48 : add_vec_int (mword_of_int (KF + 0x44) : mword 64) 4 = mword_of_int (KF + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp48) in "Hpc".
    (* +0x48 c.sd a5,0(s1) : p->next := head *)
    iEval (rewrite page_own_split) in "Hpage".
    iDestruct "Hpage" as "[Hhead Hrest]".
    iDestruct (page_head8_word_at p Hpv with "Hhead") as (wold) "Hpw".
    assert (Hsdaddr : add_vec (Rld !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))) = p).
    { replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000"))) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      rewrite HRlds1. apply kv_addv_zero. }
    iApply (wp_csd_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x48)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
              Rld wold (dq:=DfracOwn 1)

              with "Hcfg Htlbinv Hpc Hfile Hi48 [Hpw] [-]").
    { iEval (rewrite -Hsdaddr) in "Hpw". rewrite /word_at. iExact "Hpw". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hpw".
    iEval (rewrite Hsdaddr) in "Hpw".
    (* Rld!!!a5 = head, so the stored value is [head] *)
    iEval (rewrite HRlda5) in "Hpw".
    iAssert (run_page p head) with "[Hpw Hrest]" as "Hrun".
    { rewrite /run_page. rewrite /word_at. iFrame "Hpw Hrest". }
    assert (Hpp4a : add_vec_int (mword_of_int (KF + 0x48) : mword 64) 2 = mword_of_int (KF + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a sd s1,24(s2) : kmem.freelist := p *)
    assert (Hsdaddr2 : add_vec (Rld !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 0x18 : mword 12)) = fl).
    { rewrite HRlds2 Hfl. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_sd_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x4a)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0x18 : mword 12)
              Rld head (dq:=DfracOwn 1)

              with "Hcfg Htlbinv Hpc Hfile Hi4a [Hflw] [-]").
    { iEval (rewrite -Hsdaddr2) in "Hflw". rewrite /word_at. iExact "Hflw". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hflw".
    iEval (rewrite Hsdaddr2) in "Hflw".
    iEval (rewrite HRlds1) in "Hflw".
    (* refold the freelist invariant with [p] pushed *)
    iAssert (kmem_res fl) with "[Hflw Hrun Hchain]" as "HRres".
    { iApply (kmem_res_push fl p head pages Hpv). rewrite /word_at. iFrame "Hflw Hrun Hchain". }
    assert (Hpp4e : add_vec_int (mword_of_int (KF + 0x4a) : mword 64) 4 = mword_of_int (KF + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    iPoseProof (kfi_4e with "Htext") as "Hi4e".
    iPoseProof (kfi_50 with "Htext") as "Hi50".
    (* +0x4e c.mv a0,s2 : a0 := &kmem (release's argument) *)
    iApply (wp_cmv_gpr_s_config_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x4e)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              Rld (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi4e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (Rae := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (Rld !!! Regidx (mword_of_int 18 : mword 5)))]> Rld).
    assert (Hpp50 : add_vec_int (mword_of_int (KF + 0x4e) : mword 64) 2 = mword_of_int (KF + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 jal ra,release *)
    iApply (wp_jal_gpr_s_zca_pt root_ppn γc Φ (mword_of_int (KF + 0x50)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fa : mword 21)
              Rae 1%Qp
 ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi50 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (Rrel := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KF + 0x50) : mword 64) 4)]> Rae).
    assert (Htgtrel : add_vec (mword_of_int (KF + 0x50) : mword 64) (sign_extend' 64 (mword_of_int 0x1fa : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrel) in "Hpc".
    (* ---- release-entry map facts ---- *)
    assert (HRrelcsp : Rrel !!! Regidx csp_rs1 = spr).
    { rewrite /Rrel lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Rae lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Rld lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hqsp. exact HKacqcsp. }
    assert (HRreltp : Rrel !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /Rrel lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Rae lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Rld lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hqtp. exact HKacqtp. }
    assert (HRrela0 : Rrel !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /Rrel lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Rae lookup_total_insert. rewrite HRlds2. apply add_vec_zero_l. }
    assert (HRrelra : Rrel !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KF + 0x50) : mword 64) 4)
      by (rewrite /Rrel; apply lookup_total_insert).
    (* ---- release(&kmem): hands its whole scratch frame [stack_own spr (n-4)]
       in and takes it back out ---- *)
    iApply (wp_release root_ppn Φ γ γc bsie lk (kmem_res fl) Rrel
              (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)))
              q_noff_store
              (if eq_vec (sign_extend' 64 qnoff) zero_reg then (zeros' 32) else qintena_old)
              (n - 4)%nat
              (dqi:=DfracOwn 1)
              ltac:(lia)
              ltac:(rewrite HRrela0 Hlk; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HRreltp; apply eq_vec_true_iff; reflexivity)
              Hnoffpos Hintena0
              ltac:(rewrite HRrelra; vm_compute; reflexivity)
              with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                    [Hkmem] Htok HRres [Hacpu] [Hanoff] [Haint] [Hdeep] [-]").
    { iExact "Hkmem". }
    { iEval (rewrite HKacqa0 -Hlk HKacqtp) in "Hacpu". iEval (rewrite HRrela0 -Hlk). iExact "Hacpu". }
    { iEval (rewrite HRreltp -Ha0fcpu). iExact "Hanoff". }
    { iEval (rewrite HRreltp -Ha0fcpu). iExact "Haint". }
    { iEval (rewrite HRrelcsp). iExact "Hdeep". }
    iIntros (mrel) "Hcfg Htoken Htlbinv Hpc Hfile %Hrelpins Hcpu2 Hnoff2 Hint2 Hdeep".
    iEval (rewrite HRrelcsp) in "Hdeep".
    (* pc = ret_tgt(Rrel) = +0x54 ; lock released. epilogue restores the frame. *)
    assert (Hpc54 : update_vec_dec (add_vec (Rrel !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (KF + 0x54)).
    { rewrite HRrelra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc54) in "Hpc".
    unfold callee_saved in Hrelpins.
    destruct Hrelpins as (Hrsp & Hrtp & Hrs0 & Hrs1 & _ & Hrs3 & Hrs4 & Hrs5 & Hrs6 & Hrs7 & Hrs8 & Hrs9 & Hrs10 & Hrs11).
    assert (HspMrel : mrel !!! Regidx csp_rs1 = spr) by (rewrite Hrsp; exact HRrelcsp).
    iPoseProof (kfi_54 with "Htext") as "Hi54".
    iPoseProof (kfi_56 with "Htext") as "Hi56".
    iPoseProof (kfi_58 with "Htext") as "Hi58".
    iPoseProof (kfi_5a with "Htext") as "Hi5a".
    iPoseProof (kfi_5c with "Htext") as "Hi5c".
    iPoseProof (kfi_5e with "Htext") as "Hi5e".
    (* +0x54 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x54)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mrel (R1 !!! Regidx (mword_of_int 1 : mword 5))
              (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi54 [Hr24]").
    { iEval (rewrite HspMrel). iEval (rewrite HspR1) in "Hr24". iExact "Hr24". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr24".
    iEval (rewrite HspMrel) in "Hr24".
    set (Q54 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    assert (HspQ54 : Q54 !!! Regidx csp_rs1 = spr) by (rewrite /Q54 lookup_total_insert_ne; [ exact HspMrel | vm_compute; discriminate ]).
    assert (Hpp56 : add_vec_int (mword_of_int (KF + 0x54) : mword 64) 2 = mword_of_int (KF + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    (* +0x56 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x56)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              Q54 (R1 !!! Regidx (mword_of_int 8 : mword 5))
              (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi56 [Hr16]").
    { iEval (rewrite HspQ54). iEval (rewrite HspR1) in "Hr16". iExact "Hr16". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr16".
    iEval (rewrite HspQ54) in "Hr16".
    set (Q56 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> Q54).
    assert (HspQ56 : Q56 !!! Regidx csp_rs1 = spr) by (rewrite /Q56 lookup_total_insert_ne; [ exact HspQ54 | vm_compute; discriminate ]).
    assert (Hpp58 : add_vec_int (mword_of_int (KF + 0x56) : mword 64) 2 = mword_of_int (KF + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58) in "Hpc".
    (* +0x58 c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x58)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              Q56 (R1 !!! Regidx (mword_of_int 9 : mword 5))
              (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi58 [Hr8]").
    { iEval (rewrite HspQ56). iEval (rewrite HspR1) in "Hr8". iExact "Hr8". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr8".
    iEval (rewrite HspQ56) in "Hr8".
    set (Q58 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> Q56).
    assert (HspQ58 : Q58 !!! Regidx csp_rs1 = spr) by (rewrite /Q58 lookup_total_insert_ne; [ exact HspQ56 | vm_compute; discriminate ]).
    assert (Hpp5a : add_vec_int (mword_of_int (KF + 0x58) : mword 64) 2 = mword_of_int (KF + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    (* +0x5a c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_gpr_s_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x5a)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              Q58 (R1 !!! Regidx (mword_of_int 18 : mword 5))
              (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi5a [Hr0]").
    { iEval (rewrite HspQ58). iEval (rewrite HspR1) in "Hr0". iExact "Hr0". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr0".
    iEval (rewrite HspQ58) in "Hr0".
    set (Q5a := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 18 : mword 5))]> Q58).
    assert (HspQ5a : Q5a !!! Regidx csp_rs1 = spr) by (rewrite /Q5a lookup_total_insert_ne; [ exact HspQ58 | vm_compute; discriminate ]).
    assert (Hpp5c : add_vec_int (mword_of_int (KF + 0x5a) : mword 64) 2 = mword_of_int (KF + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* +0x5c c.addi16sp sp,32 *)
    iApply (wp_caddi16sp_gpr_s_pt root_ppn γc Φ (mword_of_int (KF + 0x5c)) (mword_of_int 2 : mword 6) Q5a
              1%Qp
              with "Hcfg Htlbinv Hpc Hfile Hi5c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (Q5c := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q5a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q5a).
    assert (Hpp5e : add_vec_int (mword_of_int (KF + 0x5c) : mword 64) 2 = mword_of_int (KF + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5e) in "Hpc".
    (* +0x5e c.ret *)
    assert (HQ5cra : Q5c !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Q5c lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Q5a lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Q58 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Q56 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Q54 lookup_total_insert.
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    iApply (wp_cret_s_zca_scfg_pt root_ppn γc Φ (mword_of_int (KF + 0x5e)) (mword_of_int 1) Q5c
              (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              ltac:(rewrite HQ5cra; exact Hretm)
              with "Hcfg Htlbinv Hpc Hfile Hi5e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    iEval (rewrite HQ5cra) in "Hpc".
    (* rebundle kfree's own 4-slot frame with the returned deep tail into the
       FULL [stack_own sp0 n] handed back to the caller. *)
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Htop".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3); iExists _; iExact "Hr8"|].
      iSplitL "Hr0";  [iEval (rewrite -Hb4); iExists _; iExact "Hr0"|].
      done. }
    iEval (rewrite -Hsprstk) in "Hdeep".
    iDestruct (stack_own_split_2 sp0 4 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    iApply ("Hcont" $! Q5c with "Hcfg Htoken Htlbinv Hpc Hfile [%] Hstk").
    { (* callee_saved m Q5c: the epilogue restores ra/s0/s1/s2 to their entry
         (R1 = m) values and sp via the +32/-32 c.addi16sp cancel; tp and s3-s11
         thread untouched through memset/acquire/release (each callee_saved) and
         kfree's own body, which never writes them. *)
      unfold callee_saved.
      (* the register-preservation chain m -> ... -> mrel for a reg K that
         kfree's own code never touches (tp, s3-s11): peel each own-code map
         group, then hop across each callee via its callee_saved conjunct. *)
      split.
      { (* sp *)
        rewrite /Q5c lookup_total_insert.
        assert (HQ5acsp : Q5a !!! Regidx csp_rs1 = spr).
        { rewrite /Q5a /Q58 /Q56 /Q54.
          repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
          exact HspMrel. }
        rewrite HQ5acsp. unfold regval_into_reg, spr. apply kfree_sp_cancel. }
      split.
      { (* tp *)
        rewrite /Q5c /Q5a /Q58 /Q56 /Q54.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        first [rewrite Hrtp | rewrite Hrs3 | rewrite Hrs4 | rewrite Hrs5 | rewrite Hrs6 | rewrite Hrs7 | rewrite Hrs8 | rewrite Hrs9 | rewrite Hrs10 | rewrite Hrs11].
        rewrite /Rrel /Rae /Rld.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        first [rewrite Hqtp | rewrite Hqs3 | rewrite Hqs4 | rewrite Hqs5 | rewrite Hqs6 | rewrite Hqs7 | rewrite Hqs8 | rewrite Hqs9 | rewrite Hqs10 | rewrite Hqs11].
        rewrite /Kacq /S3 /S2 /S1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        first [rewrite Hftp | rewrite Hfs3 | rewrite Hfs4 | rewrite Hfs5 | rewrite Hfs6 | rewrite Hfs7 | rewrite Hfs8 | rewrite Hfs9 | rewrite Hfs10 | rewrite Hfs11].
        rewrite /Mms /R14 /R13 /R12 /R11 /R10 /R9 /R8 /R7 /R6 /R5 /R4 /R3 /R2 /R1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        reflexivity. }
      split.
      { (* s0 *)
        rewrite /Q5c lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q5a lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q58 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q56 lookup_total_insert.
        rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      split.
      { (* s1 *)
        rewrite /Q5c lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q5a lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q58 lookup_total_insert.
        rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      split.
      { (* s2 *)
        rewrite /Q5c lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q5a lookup_total_insert.
        rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      (* s3..s11: identical chain to tp *)
      repeat split;
        rewrite /Q5c /Q5a /Q58 /Q56 /Q54;
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
        first [rewrite Hrtp | rewrite Hrs3 | rewrite Hrs4 | rewrite Hrs5 | rewrite Hrs6 | rewrite Hrs7 | rewrite Hrs8 | rewrite Hrs9 | rewrite Hrs10 | rewrite Hrs11];
        rewrite /Rrel /Rae /Rld;
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
        first [rewrite Hqtp | rewrite Hqs3 | rewrite Hqs4 | rewrite Hqs5 | rewrite Hqs6 | rewrite Hqs7 | rewrite Hqs8 | rewrite Hqs9 | rewrite Hqs10 | rewrite Hqs11];
        rewrite /Kacq /S3 /S2 /S1;
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
        first [rewrite Hftp | rewrite Hfs3 | rewrite Hfs4 | rewrite Hfs5 | rewrite Hfs6 | rewrite Hfs7 | rewrite Hfs8 | rewrite Hfs9 | rewrite Hfs10 | rewrite Hfs11];
        rewrite /Mms /R14 /R13 /R12 /R11 /R10 /R9 /R8 /R7 /R6 /R5 /R4 /R3 /R2 /R1;
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
        reflexivity. }
  Qed.

End Kfree.
