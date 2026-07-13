(* WpHoldingInv.v -- holding() against the CSL lock invariant: the lock-word
   read at +0x0 goes THROUGH [is_lock] (WpLockLeaves.wp_clw_lockinv and twin), so the
   caller owns no lock-word bytes.  Two flavors:

     wp_holding_lockinv         -- caller does NOT hold the lock (its cpu
                                   field differs from mycpu()): holding()
                                   returns 0 on both the fast (word 0) and
                                   slow (word nonzero) paths.
     wp_holding_lockinv_locked  -- caller HOLDS [locked γ] and lk->cpu is
                                   mycpu(): the invariant's free branch is
                                   refuted at the read, so the slow path is
                                   taken and holding() returns 1.

   Both are built from WpHolding.v's decode/leaf lemmas (hi_00..hi_06,
   his_08..his_2a), with instruction +0x0 swapped for the invariant-mediated
   read. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import MinstretInv InstrBytes.
Require Import KernelText.
Require Import WpGpr WpGprRvc.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpKernelvecNew WpPushOff.
Require Import WpMycpu WpPushOffTop WpAcquireMem.
Require Import CalleeSaved.
Require Import WpHolding WpLock WpLockLeaves.
Require Import WpSmodeJalr.
Require Export WpSmodeLeafBase WpSmodeAddiw WpSmodeShiftiop WpSmodeRtype WpSmodeItype WpSmodeLoad WpSmodeStore WpSmodeBtype.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* seqz on a-b for EQUAL operands: result 1 (twin of WpHolding.seqz_sub_neq) *)
Lemma seqz_sub_eq (a b : mword 64) :
  eq_vec a b = true ->
  zero_extend' 64 (bool_to_bit (zopz0zI_u (sub_vec a b)
    (sign_extend' 64 (mword_of_int 1 : mword 12)))) = (mword_of_int 1 : mword 64).
Proof.
  intro He.
  assert (Hab : a = b) by (apply eq_vec_true_iff; exact He).
  subst b.
  replace (sub_vec a a) with (zeros' 64 : mword 64);
    [ apply bv_eq; vm_compute; reflexivity | ].
  apply bv_eq.
  unfold sub_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.sub.
  rewrite bv_sub_unsigned. rewrite Z.sub_diag. reflexivity.
Qed.

Section WpHoldingInv.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* ---- [smode_config] leaf wrappers for holding.  All config-preserving
     (holding never touches mstatus), so each just unbundles → raw leaf →
     rebundles.  The sstatus-reading leaves (cret/cbnez_fall/cbnez_taken_zca…)
     reuse the wrappers exported by WpPopOff. ---- *)

  Lemma wp_csdsp_gpr_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ pc uimm rs2 m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_cldsp_gpr_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : gmap regidx (mword 64)) (v : bv 64) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8)) -∗
    ea ↦₈{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN Hrd.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ pc uimm rd m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.


  Lemma wp_cmv_gpr_s_config_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cmv_gpr_s_config root_ppn E Φ pc rd rs2 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_caddi_gpr_s_config_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_caddi_gpr_s_config root_ppn E Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_caddi4spn_gpr_s_config_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrdc Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ pc rdc nzimm rd m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrdc Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.




  Lemma wp_clw_lockinv_scfg (root_ppn : mword 44) (γc : gname) E (Φ : mval -> iProp Σ)
      (γ : gname) (lk : mword 64) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E -> ↑lockN ⊆ E -> ea = lk -> uint rd <> 0 ->
    smode_config γc dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    is_lock γ lk R -∗
    ( ∀ v : mword 32,
      smode_config γc dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN HNl Hlk Hrd.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hlock Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_clw_lockinv root_ppn E Φ γ lk R pc rd rs1 imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HNl Hlk Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hlock").
    iIntros (v) "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γc dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_clw_lockinv_locked_scfg (root_ppn : mword 44) (γc : gname) E (Φ : mval -> iProp Σ)
      (γ : gname) (lk : mword 64) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E -> ↑lockN ⊆ E -> ea = lk -> uint rd <> 0 ->
    smode_config γc dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    is_lock γ lk R -∗ locked γ -∗
    ( ∀ v : mword 32,
      ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝ -∗
      locked γ -∗
      smode_config γc dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN HNl Hlk Hrd.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hlock Hlocked Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_clw_lockinv_locked root_ppn E Φ γ lk R pc rd rs1 imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HNl Hlk Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hlock Hlocked").
    iIntros (v) "%Hneq Hlocked Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γc dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" $! v with "[%] Hlocked Hsm Htlbinv Hpc Hfile").
    exact Hneq.
  Qed.

  Lemma wp_holding_lockinv (root_ppn : mword 44) (γc : gname) E (Φ : mval -> iProp Σ)
      (γ : gname) (lka : mword 64) (R : iProp Σ)
      (m : gmap regidx (mword 64))
      (cpuold : mword 64)
      (vp24 vp16 vp8 vfra vfs0 : bv 64)
      {dqc : dfrac} :
    let pcE : mword 64 := mword_of_int KernelSyms.holding in
    let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
    let a_lk := add_vec lk (sign_extend' 64 (mword_of_int 0 : mword 12)) in
    let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    let spdh := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let a_h24 := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_h16 := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_h8  := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let mc_sp := add_vec spdh (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let a_fra := add_vec mc_sp (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_fs0 := add_vec mc_sp (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    a_lk = lka ->
    (* data-slot geometry is DERIVED in the leaves from the lock invariant
       (a_lk) and the owned [a_cpu ↦₈ _] -- no po_slot_geom premise. *)
    (* the lock is not held by THIS cpu *)
    eq_vec cpuold (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = false ->
    (* return target alignment *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    is_lock γ lka R -∗
    a_cpu ↦₈{ dqc } cpuold -∗
    a_h24 ↦₈ vp24 -∗
    a_h16 ↦₈ vp16 -∗
    a_h8 ↦₈ vp8 -∗
    a_fra ↦₈ vfra -∗
    a_fs0 ↦₈ vfs0 -∗
    ( ∀ mh,
      smode_config γc (DfracOwn 1) -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mh -∗
      ⌜ callee_saved m mh /\
        mh !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64) ⌝ -∗
      a_cpu ↦₈{ dqc } cpuold -∗
      (∃ (w24 w16 w8 wra ws0 : bv 64),
        a_h24 ↦₈ w24 ∗
        a_h16 ↦₈ w16 ∗
        a_h8 ↦₈ w8 ∗
        a_fra ↦₈ wra ∗
        a_fs0 ↦₈ ws0) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE lk a_lk a_cpu spdh a_h24 a_h16 a_h8 mc_sp a_fra a_fs0 ret_tgt
      HN HNl Hlka Hnotmine Hal0.
    iIntros "Hcfg Htlbinv
             #Htext Hpc Hfile #Hlock Hcpu Hh24 Hh16 Hh8 Hfra Hfs0 Hcont".
    iPoseProof (hi_00 with "Htext") as "Hi00".
    iPoseProof (hi_02 with "Htext") as "Hi02".
    (* +0x0 c.lw a5,0(a0): a5 := sext64 lockv *)
    iApply (wp_clw_lockinv_scfg root_ppn γc E Φ γ lka R pcE (mword_of_int 15) (mword_of_int 10)
              (mword_of_int 0) m
              (dq:=DfracOwn 1)
              HN HNl Hlka ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi00 Hlock [-]").
    iIntros (lockv) "Hcfg Htlbinv Hpc Hfile".
    set (H1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 lockv)]> m).
    assert (Ha5 : H1 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 lockv)
      by (rewrite /H1; apply lookup_total_insert).
    assert (Hpp2 : add_vec_int pcE 2 = mword_of_int (KernelSyms.holding + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2) in "Hpc".
    (* case split: is the lock held? *)
    destruct (neq_vec (sign_extend' 64 lockv) zero_reg) eqn:Hheld.
    - (* ===== SLOW PATH: lock word nonzero, c.bnez TAKEN ===== *)
      iApply (wp_cbnez_taken_s_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x02)) (mword_of_int 3) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                H1 (dq:=DfracOwn 1)
                HN 
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5; exact Hheld)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi02 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpc08 : add_vec (mword_of_int (KernelSyms.holding + 0x02) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.holding + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc08) in "Hpc".
      iPoseProof (his_08 with "Htext") as "Hi08".
      iPoseProof (his_0a with "Htext") as "Hi0a".
      iPoseProof (his_0c with "Htext") as "Hi0c".
      iPoseProof (his_0e with "Htext") as "Hi0e".
      iPoseProof (his_10 with "Htext") as "Hi10".
      iPoseProof (his_12 with "Htext") as "Hi12".
      iPoseProof (his_14 with "Htext") as "Hi14".
      iPoseProof (his_16 with "Htext") as "Hi16".
      iPoseProof (his_1a with "Htext") as "Hi1a".
      iPoseProof (his_1e with "Htext") as "Hi1e".
      iPoseProof (his_22 with "Htext") as "Hi22".
      iPoseProof (his_24 with "Htext") as "Hi24".
      iPoseProof (his_26 with "Htext") as "Hi26".
      iPoseProof (his_28 with "Htext") as "Hi28".
      iPoseProof (his_2a with "Htext") as "Hi2a".
      (* +0x08 c.addi sp,-32 *)
      iApply (wp_caddi_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x08)) csp_rs1 (mword_of_int 32 : mword 6) H1
                (dq:=DfracOwn 1)
                HN  ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi08 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H2 := <[Regidx csp_rs1 := regval_into_reg (add_vec (H1 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> H1).
      assert (HspH1 : H1 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
        by (rewrite /H1; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
      assert (HspH2 : H2 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H2; rewrite lookup_total_insert; rewrite HspH1; reflexivity).
      assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.holding + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp0a) in "Hpc".
      (* +0x0a c.sdsp ra,24(sp) *)
      iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                H2 vp24 (dq:=DfracOwn 1)
                HN
                
                with "Hcfg Htlbinv Hpc Hfile Hi0a [Hh24] [-]").
      { iEval (rewrite HspH2). iExact "Hh24". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh24".
      assert (HraH2 : H2 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HspH2 HraH2) in "Hh24".
      assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.holding + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp0c) in "Hpc".
      (* +0x0c c.sdsp s0,16(sp) *)
      iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                H2 vp16 (dq:=DfracOwn 1)
                HN
                
                with "Hcfg Htlbinv Hpc Hfile Hi0c [Hh16] [-]").
      { iEval (rewrite HspH2). iExact "Hh16". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh16".
      assert (Hs0H2 : H2 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
      { rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HspH2 Hs0H2) in "Hh16".
      assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.holding + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp0e) in "Hpc".
      (* +0x0e c.sdsp s1,8(sp) *)
      iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                H2 vp8 (dq:=DfracOwn 1)
                HN
                
                with "Hcfg Htlbinv Hpc Hfile Hi0e [Hh8] [-]").
      { iEval (rewrite HspH2). iExact "Hh8". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh8".
      assert (Hs1H2 : H2 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
      { rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HspH2 Hs1H2) in "Hh8".
      assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.holding + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp10) in "Hpc".
      (* +0x10 c.addi4spn s0,sp,32 *)
      iApply (wp_caddi4spn_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x10)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
                H2 (dq:=DfracOwn 1)
                HN 
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi10 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H3 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (H2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> H2).
      assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.holding + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp12) in "Hpc".
      (* +0x12 c.ld a5,16(a0): a5 := lk->cpu *)
      assert (Ha0H3 : H3 !!! Regidx (mword_of_int 10 : mword 5) = lk).
      { rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      assert (HAcpu : add_vec (H3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = a_cpu)
        by (rewrite Ha0H3; reflexivity).
        iApply (wp_cld_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x12)) (mword_of_int 15) (mword_of_int 10)
                (mword_of_int 16) H3 cpuold
                (dq:=DfracOwn 1) (dqm:=dqc)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi12 [Hcpu] [-]").
      { iEval (rewrite HAcpu). iExact "Hcpu". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hcpu".
      iEval (rewrite HAcpu) in "Hcpu".
      set (H4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg cpuold]> H3).
      assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.holding + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp14) in "Hpc".
      (* +0x14 c.mv s1,a5 *)
      iApply (wp_cmv_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x14)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
                H4 (dq:=DfracOwn 1)
                HN  ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi14 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (H4 !!! Regidx (mword_of_int 15 : mword 5)))]> H4).
      assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.holding + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp16) in "Hpc".
      (* +0x16 jal ra,mycpu; the whole mycpu() *)
      assert (HspH5 : H5 !!! Regidx csp_rs1 = spdh).
      { rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HspH2. }
      assert (HspH6 : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.holding + 0x16) : mword 64) 4)]> H5) !!! Regidx csp_rs1 = spdh)
        by (rewrite lookup_total_insert_ne; [ exact HspH5 | vm_compute; discriminate ]).
      assert (EQ18 : add_vec_int (mword_of_int (KernelSyms.holding + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      (* mycpu callee, [smode_config] view -- no unbundle island needed *)
      iApply (wp_pushoff_call_mycpu_scfg_cs root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x16)) (mword_of_int 0xd2c : mword 21) H5 vfra vfs0
                HN ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
                with "Hcfg Htlbinv Htext Hpc Hfile Hi16 [Hfra] [Hfs0] [-]").
      { iEval (rewrite HspH6). iExact "Hfra". }
      { iEval (rewrite HspH6). iExact "Hfs0". }
      iIntros (C) "Hcfg Htlbinv Hpc Hfile %Hmc Hfra Hfs0".
      iEval (rewrite HspH6) in "Hfra". iEval (rewrite HspH6) in "Hfs0".
      iEval (rewrite lookup_total_insert) in "Hpc".
      assert (Hpc1a : update_vec_dec (add_vec (add_vec_int (mword_of_int (KernelSyms.holding + 0x16) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                      = (mword_of_int (KernelSyms.holding + 0x1a) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc1a) in "Hpc".
      destruct Hmc as (Hmc_cs & Hmc_a0).
      unfold callee_saved in Hmc_cs.
      destruct Hmc_cs as (Hmc_csp & Hmc_tp & Hmc_s0 & Hmc_s1 & Hmc_s2 & Hmc_s3 & Hmc_s4 & Hmc_s5 & Hmc_s6 & Hmc_s7 & Hmc_s8 & Hmc_s9 & Hmc_s10 & Hmc_s11).
      (* +0x1a sub a0,s1,a0 *)
      assert (Hs1C : C !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg cpuold).
      { rewrite Hmc_s1. rewrite /H5. rewrite lookup_total_insert.
        rewrite /H4. rewrite lookup_total_insert. reflexivity. }
      assert (Ha0C : C !!! Regidx (mword_of_int 10 : mword 5) = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))).
      { rewrite Hmc_a0.
        rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iApply (wp_sub_s root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x1a)) (mword_of_int 10) (mword_of_int 9) (mword_of_int 10)
                (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))
                C (dq:=DfracOwn 1)
                HN
                ltac:(vm_compute; discriminate)
                ltac:(reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi1a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))]> C).
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.holding + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.holding + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* +0x1e seqz a0,a0 *)
      assert (Ha0H6 : H6 !!! Regidx (mword_of_int 10 : mword 5)
                      = sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))
        by (rewrite /H6; apply lookup_total_insert).
      iApply (wp_sltiu_s root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x1e)) (mword_of_int 10) (mword_of_int 10)
                (mword_of_int 1)
                (zero_extend' 64 (bool_to_bit (zopz0zI_u (H6 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))
                H6 (dq:=DfracOwn 1)
                HN
                ltac:(vm_compute; discriminate)
                ltac:(reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H7 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (zero_extend' 64 (bool_to_bit (zopz0zI_u (H6 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))]> H6).
      assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.holding + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.holding + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 c.ldsp ra,24(sp) *)
      assert (HspC : C !!! Regidx csp_rs1 = spdh).
      { rewrite Hmc_csp. exact HspH5. }
      assert (HspH7 : H7 !!! Regidx csp_rs1 = spdh).
      { rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HspC. }
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x22)) (mword_of_int 3) (mword_of_int 1 : mword 5)
                H7 (m !!! Regidx (mword_of_int 1 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                
                with "Hcfg Htlbinv Hpc Hfile Hi22 [Hh24]").
      { iEval (rewrite HspH7). iExact "Hh24". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh24".
      iEval (rewrite HspH7) in "Hh24".
      set (H8 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> H7).
      assert (HspH8 : H8 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H8; rewrite lookup_total_insert_ne; [ exact HspH7 | vm_compute; discriminate ]).
      assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.holding + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      (* +0x24 c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x24)) (mword_of_int 2) (mword_of_int 8 : mword 5)
                H8 (m !!! Regidx (mword_of_int 8 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                
                with "Hcfg Htlbinv Hpc Hfile Hi24 [Hh16]").
      { iEval (rewrite HspH8). iExact "Hh16". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh16".
      iEval (rewrite HspH8) in "Hh16".
      set (H9 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> H8).
      assert (HspH9 : H9 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H9; rewrite lookup_total_insert_ne; [ exact HspH8 | vm_compute; discriminate ]).
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.holding + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* +0x26 c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x26)) (mword_of_int 1) (mword_of_int 9 : mword 5)
                H9 (m !!! Regidx (mword_of_int 9 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                
                with "Hcfg Htlbinv Hpc Hfile Hi26 [Hh8]").
      { iEval (rewrite HspH9). iExact "Hh8". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh8".
      iEval (rewrite HspH9) in "Hh8".
      set (H10 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> H9).
      assert (HspH10 : H10 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H10; rewrite lookup_total_insert_ne; [ exact HspH9 | vm_compute; discriminate ]).
      assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.holding + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      (* +0x28 c.addi16sp sp,32 *)
      iApply (wp_caddi16sp_gpr_s root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x28)) (mword_of_int 2 : mword 6) H10
                1%Qp HN
                with "Hcfg Htlbinv Hpc Hfile Hi28 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H11 := <[Regidx csp_rs1 := regval_into_reg (add_vec (H10 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> H10).
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.holding + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      (* +0x2a c.ret *)
      assert (HraH11 : H11 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H8. apply lookup_total_insert. }
      iApply (wp_cret_s_zca_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x2a)) (mword_of_int 1) H11
                (dq:=DfracOwn 1)
                HN  ltac:(vm_compute; discriminate)
                ltac:(rewrite HraH11; exact Hal0)
                with "Hcfg Htlbinv Hpc Hfile Hi2a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite HraH11) in "Hpc".
      iApply ("Hcont" $! H11 with "Hcfg Htlbinv Hpc Hfile [%] Hcpu [Hh24 Hh16 Hh8 Hfra Hfs0]").
      { split.
        { unfold callee_saved. repeat split.
        - (* sp *)
          rewrite /H11. rewrite lookup_total_insert. rewrite HspH10.
          rewrite /spdh po_addv_assoc.
          replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                           (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))
            with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero.
        - (* tp *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_tp.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s0 (x8) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. apply lookup_total_insert.
        - (* s1 (x9) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. apply lookup_total_insert.
        - (* s2 (x18) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s2.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s3 (x19) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s3.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s4 (x20) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s4.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s5 (x21) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s5.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s6 (x22) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s6.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s7 (x23) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s7.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s8 (x24) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s8.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s9 (x25) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s9.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s10 (x26) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s10.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s11 (x27) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s11.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        }
        (* a0 = 0: slow path -- this cpu does NOT hold the lock *)
        rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H7. rewrite lookup_total_insert.
        rewrite Ha0H6 Hs1C Ha0C.
        rewrite add_vec_zero_l.
        apply seqz_sub_neq. exact Hnotmine.
      }
      iExists _, _, _, _, _. iFrame "Hh24 Hh16 Hh8 Hfra Hfs0".
    - (* ===== FAST PATH: lock word 0, c.bnez NOT taken ===== *)
      iApply (wp_cbnez_fall_s_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x02)) (mword_of_int 3) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                H1 (dq:=DfracOwn 1)
                HN 
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5; exact Hheld)
                with "Hcfg Htlbinv Hpc Hfile Hi02 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.holding + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp04) in "Hpc".
      (* +0x04 c.li a0,0 *)
      iPoseProof (hi_04 with "Htext") as "Hi04".
      iApply (wp_cli_s root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x04)) (mword_of_int 10)
                (mword_of_int 0 : mword 6)
                (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
                H1 (dq:=DfracOwn 1)
                HN  ltac:(vm_compute; discriminate)
                ltac:(reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi04 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H2f := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> H1).
      assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.holding + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp06) in "Hpc".
      (* +0x06 c.ret *)
      iPoseProof (hi_06 with "Htext") as "Hi06".
      assert (HraH2f : H2f !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /H2f. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iApply (wp_cret_s_zca_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x06)) (mword_of_int 1) H2f
                (dq:=DfracOwn 1)
                HN  ltac:(vm_compute; discriminate)
                ltac:(rewrite HraH2f; exact Hal0)
                with "Hcfg Htlbinv Hpc Hfile Hi06 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite HraH2f) in "Hpc".
      iApply ("Hcont" $! H2f with "Hcfg Htlbinv Hpc Hfile [%] Hcpu [Hh24 Hh16 Hh8 Hfra Hfs0]").
      { split.
        { unfold callee_saved. repeat split;
            (rewrite /H2f; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
             rewrite /H1; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]). }
        (* a0 = 0 *)
        rewrite /H2f. rewrite lookup_total_insert. apply bv_eq. vm_compute. reflexivity.
      }
      iExists vp24, vp16, vp8, vfra, vfs0. iFrame "Hh24 Hh16 Hh8 Hfra Hfs0".
  Qed.

  Lemma wp_holding_lockinv_locked (root_ppn : mword 44) (γc : gname) E (Φ : mval -> iProp Σ)
      (γ : gname) (lka : mword 64) (R : iProp Σ)
      (m : gmap regidx (mword 64))
      (cpuold : mword 64)
      (vp24 vp16 vp8 vfra vfs0 : bv 64)
      {dqc : dfrac} :
    let pcE : mword 64 := mword_of_int KernelSyms.holding in
    let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
    let a_lk := add_vec lk (sign_extend' 64 (mword_of_int 0 : mword 12)) in
    let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    let spdh := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let a_h24 := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_h16 := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_h8  := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let mc_sp := add_vec spdh (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let a_fra := add_vec mc_sp (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_fs0 := add_vec mc_sp (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    a_lk = lka ->
    (* data-slot geometry is DERIVED in the leaves from the lock invariant
       (a_lk) and the owned [a_cpu ↦₈ _] -- no po_slot_geom premise. *)
    (* the lock IS held by THIS cpu *)
    eq_vec cpuold (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = true ->
    (* return target alignment *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    is_lock γ lka R -∗
    locked γ -∗
    a_cpu ↦₈{ dqc } cpuold -∗
    a_h24 ↦₈ vp24 -∗
    a_h16 ↦₈ vp16 -∗
    a_h8 ↦₈ vp8 -∗
    a_fra ↦₈ vfra -∗
    a_fs0 ↦₈ vfs0 -∗
    ( ∀ mh,
      smode_config γc (DfracOwn 1) -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      locked γ -∗
      gpr_file mh -∗
      ⌜ callee_saved m mh /\
        mh !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ⌝ -∗
      a_cpu ↦₈{ dqc } cpuold -∗
      (∃ (w24 w16 w8 wra ws0 : bv 64),
        a_h24 ↦₈ w24 ∗
        a_h16 ↦₈ w16 ∗
        a_h8 ↦₈ w8 ∗
        a_fra ↦₈ wra ∗
        a_fs0 ↦₈ ws0) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE lk a_lk a_cpu spdh a_h24 a_h16 a_h8 mc_sp a_fra a_fs0 ret_tgt
      HN HNl Hlka Hmine Hal0.
    iIntros "Hcfg Htlbinv
             #Htext Hpc Hfile #Hlock Htok Hcpu Hh24 Hh16 Hh8 Hfra Hfs0 Hcont".
    iPoseProof (hi_00 with "Htext") as "Hi00".
    iPoseProof (hi_02 with "Htext") as "Hi02".
    (* +0x0 c.lw a5,0(a0): a5 := sext64 lockv *)
    iApply (wp_clw_lockinv_locked_scfg root_ppn γc E Φ γ lka R pcE (mword_of_int 15) (mword_of_int 10)
              (mword_of_int 0) m
              (dq:=DfracOwn 1)
              HN HNl Hlka ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi00 Hlock Htok [-]").
    iIntros (lockv) "%Hheldp Htok Hcfg Htlbinv Hpc Hfile".
    set (H1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 lockv)]> m).
    assert (Ha5 : H1 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 lockv)
      by (rewrite /H1; apply lookup_total_insert).
    assert (Hpp2 : add_vec_int pcE 2 = mword_of_int (KernelSyms.holding + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2) in "Hpc".
    (* the token refuted the free branch: the c.bnez is TAKEN *)
    destruct (neq_vec (sign_extend' 64 lockv) zero_reg) eqn:Hheld;
      [ | exfalso; rewrite Hheldp in Hheld; discriminate ].
    - (* ===== SLOW PATH: lock word nonzero, c.bnez TAKEN ===== *)
      iApply (wp_cbnez_taken_s_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x02)) (mword_of_int 3) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                H1 (dq:=DfracOwn 1)
                HN 
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5; exact Hheld)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi02 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpc08 : add_vec (mword_of_int (KernelSyms.holding + 0x02) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.holding + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc08) in "Hpc".
      iPoseProof (his_08 with "Htext") as "Hi08".
      iPoseProof (his_0a with "Htext") as "Hi0a".
      iPoseProof (his_0c with "Htext") as "Hi0c".
      iPoseProof (his_0e with "Htext") as "Hi0e".
      iPoseProof (his_10 with "Htext") as "Hi10".
      iPoseProof (his_12 with "Htext") as "Hi12".
      iPoseProof (his_14 with "Htext") as "Hi14".
      iPoseProof (his_16 with "Htext") as "Hi16".
      iPoseProof (his_1a with "Htext") as "Hi1a".
      iPoseProof (his_1e with "Htext") as "Hi1e".
      iPoseProof (his_22 with "Htext") as "Hi22".
      iPoseProof (his_24 with "Htext") as "Hi24".
      iPoseProof (his_26 with "Htext") as "Hi26".
      iPoseProof (his_28 with "Htext") as "Hi28".
      iPoseProof (his_2a with "Htext") as "Hi2a".
      (* +0x08 c.addi sp,-32 *)
      iApply (wp_caddi_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x08)) csp_rs1 (mword_of_int 32 : mword 6) H1
                (dq:=DfracOwn 1)
                HN  ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi08 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H2 := <[Regidx csp_rs1 := regval_into_reg (add_vec (H1 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> H1).
      assert (HspH1 : H1 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
        by (rewrite /H1; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
      assert (HspH2 : H2 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H2; rewrite lookup_total_insert; rewrite HspH1; reflexivity).
      assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.holding + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp0a) in "Hpc".
      (* +0x0a c.sdsp ra,24(sp) *)
      iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                H2 vp24 (dq:=DfracOwn 1)
                HN
                
                with "Hcfg Htlbinv Hpc Hfile Hi0a [Hh24] [-]").
      { iEval (rewrite HspH2). iExact "Hh24". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh24".
      assert (HraH2 : H2 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HspH2 HraH2) in "Hh24".
      assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.holding + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp0c) in "Hpc".
      (* +0x0c c.sdsp s0,16(sp) *)
      iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                H2 vp16 (dq:=DfracOwn 1)
                HN
                
                with "Hcfg Htlbinv Hpc Hfile Hi0c [Hh16] [-]").
      { iEval (rewrite HspH2). iExact "Hh16". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh16".
      assert (Hs0H2 : H2 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
      { rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HspH2 Hs0H2) in "Hh16".
      assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.holding + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp0e) in "Hpc".
      (* +0x0e c.sdsp s1,8(sp) *)
      iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                H2 vp8 (dq:=DfracOwn 1)
                HN
                
                with "Hcfg Htlbinv Hpc Hfile Hi0e [Hh8] [-]").
      { iEval (rewrite HspH2). iExact "Hh8". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh8".
      assert (Hs1H2 : H2 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
      { rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HspH2 Hs1H2) in "Hh8".
      assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.holding + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp10) in "Hpc".
      (* +0x10 c.addi4spn s0,sp,32 *)
      iApply (wp_caddi4spn_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x10)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
                H2 (dq:=DfracOwn 1)
                HN 
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi10 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H3 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (H2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> H2).
      assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.holding + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp12) in "Hpc".
      (* +0x12 c.ld a5,16(a0): a5 := lk->cpu *)
      assert (Ha0H3 : H3 !!! Regidx (mword_of_int 10 : mword 5) = lk).
      { rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      assert (HAcpu : add_vec (H3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = a_cpu)
        by (rewrite Ha0H3; reflexivity).
        iApply (wp_cld_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x12)) (mword_of_int 15) (mword_of_int 10)
                (mword_of_int 16) H3 cpuold
                (dq:=DfracOwn 1) (dqm:=dqc)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi12 [Hcpu] [-]").
      { iEval (rewrite HAcpu). iExact "Hcpu". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hcpu".
      iEval (rewrite HAcpu) in "Hcpu".
      set (H4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg cpuold]> H3).
      assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.holding + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp14) in "Hpc".
      (* +0x14 c.mv s1,a5 *)
      iApply (wp_cmv_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x14)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
                H4 (dq:=DfracOwn 1)
                HN  ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi14 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (H4 !!! Regidx (mword_of_int 15 : mword 5)))]> H4).
      assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.holding + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp16) in "Hpc".
      (* +0x16 jal ra,mycpu; the whole mycpu() *)
      assert (HspH5 : H5 !!! Regidx csp_rs1 = spdh).
      { rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HspH2. }
      assert (HspH6 : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.holding + 0x16) : mword 64) 4)]> H5) !!! Regidx csp_rs1 = spdh)
        by (rewrite lookup_total_insert_ne; [ exact HspH5 | vm_compute; discriminate ]).
      assert (EQ18 : add_vec_int (mword_of_int (KernelSyms.holding + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      (* mycpu callee, [smode_config] view -- no unbundle island needed *)
      iApply (wp_pushoff_call_mycpu_scfg_cs root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x16)) (mword_of_int 0xd2c : mword 21) H5 vfra vfs0
                HN ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
                with "Hcfg Htlbinv Htext Hpc Hfile Hi16 [Hfra] [Hfs0] [-]").
      { iEval (rewrite HspH6). iExact "Hfra". }
      { iEval (rewrite HspH6). iExact "Hfs0". }
      iIntros (C) "Hcfg Htlbinv Hpc Hfile %Hmc Hfra Hfs0".
      iEval (rewrite HspH6) in "Hfra". iEval (rewrite HspH6) in "Hfs0".
      iEval (rewrite lookup_total_insert) in "Hpc".
      assert (Hpc1a : update_vec_dec (add_vec (add_vec_int (mword_of_int (KernelSyms.holding + 0x16) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                      = (mword_of_int (KernelSyms.holding + 0x1a) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc1a) in "Hpc".
      destruct Hmc as (Hmc_cs & Hmc_a0).
      unfold callee_saved in Hmc_cs.
      destruct Hmc_cs as (Hmc_csp & Hmc_tp & Hmc_s0 & Hmc_s1 & Hmc_s2 & Hmc_s3 & Hmc_s4 & Hmc_s5 & Hmc_s6 & Hmc_s7 & Hmc_s8 & Hmc_s9 & Hmc_s10 & Hmc_s11).
      (* +0x1a sub a0,s1,a0 *)
      assert (Hs1C : C !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg cpuold).
      { rewrite Hmc_s1. rewrite /H5. rewrite lookup_total_insert.
        rewrite /H4. rewrite lookup_total_insert. reflexivity. }
      assert (Ha0C : C !!! Regidx (mword_of_int 10 : mword 5) = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))).
      { rewrite Hmc_a0.
        rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iApply (wp_sub_s root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x1a)) (mword_of_int 10) (mword_of_int 9) (mword_of_int 10)
                (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))
                C (dq:=DfracOwn 1)
                HN
                ltac:(vm_compute; discriminate)
                ltac:(reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi1a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))]> C).
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.holding + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.holding + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* +0x1e seqz a0,a0 *)
      assert (Ha0H6 : H6 !!! Regidx (mword_of_int 10 : mword 5)
                      = sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))
        by (rewrite /H6; apply lookup_total_insert).
      iApply (wp_sltiu_s root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x1e)) (mword_of_int 10) (mword_of_int 10)
                (mword_of_int 1)
                (zero_extend' 64 (bool_to_bit (zopz0zI_u (H6 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))
                H6 (dq:=DfracOwn 1)
                HN
                ltac:(vm_compute; discriminate)
                ltac:(reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H7 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (zero_extend' 64 (bool_to_bit (zopz0zI_u (H6 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))]> H6).
      assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.holding + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.holding + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 c.ldsp ra,24(sp) *)
      assert (HspC : C !!! Regidx csp_rs1 = spdh).
      { rewrite Hmc_csp. exact HspH5. }
      assert (HspH7 : H7 !!! Regidx csp_rs1 = spdh).
      { rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HspC. }
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x22)) (mword_of_int 3) (mword_of_int 1 : mword 5)
                H7 (m !!! Regidx (mword_of_int 1 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                
                with "Hcfg Htlbinv Hpc Hfile Hi22 [Hh24]").
      { iEval (rewrite HspH7). iExact "Hh24". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh24".
      iEval (rewrite HspH7) in "Hh24".
      set (H8 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> H7).
      assert (HspH8 : H8 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H8; rewrite lookup_total_insert_ne; [ exact HspH7 | vm_compute; discriminate ]).
      assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.holding + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      (* +0x24 c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x24)) (mword_of_int 2) (mword_of_int 8 : mword 5)
                H8 (m !!! Regidx (mword_of_int 8 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                
                with "Hcfg Htlbinv Hpc Hfile Hi24 [Hh16]").
      { iEval (rewrite HspH8). iExact "Hh16". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh16".
      iEval (rewrite HspH8) in "Hh16".
      set (H9 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> H8).
      assert (HspH9 : H9 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H9; rewrite lookup_total_insert_ne; [ exact HspH8 | vm_compute; discriminate ]).
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.holding + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* +0x26 c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x26)) (mword_of_int 1) (mword_of_int 9 : mword 5)
                H9 (m !!! Regidx (mword_of_int 9 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                
                with "Hcfg Htlbinv Hpc Hfile Hi26 [Hh8]").
      { iEval (rewrite HspH9). iExact "Hh8". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hh8".
      iEval (rewrite HspH9) in "Hh8".
      set (H10 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> H9).
      assert (HspH10 : H10 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H10; rewrite lookup_total_insert_ne; [ exact HspH9 | vm_compute; discriminate ]).
      assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.holding + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      (* +0x28 c.addi16sp sp,32 *)
      iApply (wp_caddi16sp_gpr_s root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x28)) (mword_of_int 2 : mword 6) H10
                1%Qp HN
                with "Hcfg Htlbinv Hpc Hfile Hi28 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (H11 := <[Regidx csp_rs1 := regval_into_reg (add_vec (H10 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> H10).
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.holding + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      (* +0x2a c.ret *)
      assert (HraH11 : H11 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H8. apply lookup_total_insert. }
      iApply (wp_cret_s_zca_scfg root_ppn γc E Φ (mword_of_int (KernelSyms.holding + 0x2a)) (mword_of_int 1) H11
                (dq:=DfracOwn 1)
                HN  ltac:(vm_compute; discriminate)
                ltac:(rewrite HraH11; exact Hal0)
                with "Hcfg Htlbinv Hpc Hfile Hi2a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite HraH11) in "Hpc".
      iApply ("Hcont" $! H11 with "Hcfg Htlbinv Hpc Htok Hfile [%] Hcpu [Hh24 Hh16 Hh8 Hfra Hfs0]").
      { split.
        { unfold callee_saved. repeat split.
        - (* sp *)
          rewrite /H11. rewrite lookup_total_insert. rewrite HspH10.
          rewrite /spdh po_addv_assoc.
          replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                           (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))
            with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero.
        - (* tp *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_tp.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s0 (x8) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. apply lookup_total_insert.
        - (* s1 (x9) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. apply lookup_total_insert.
        - (* s2 (x18) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s2.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s3 (x19) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s3.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s4 (x20) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s4.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s5 (x21) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s5.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s6 (x22) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s6.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s7 (x23) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s7.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s8 (x24) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s8.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s9 (x25) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s9.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s10 (x26) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s10.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s11 (x27) *)
          rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hmc_s11.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        }
        (* a0 = 1: holding returns "true" (this cpu holds the lock) *)
        rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H7. rewrite lookup_total_insert.
        rewrite Ha0H6 Hs1C Ha0C.
        rewrite add_vec_zero_l.
        apply seqz_sub_eq. exact Hmine.
      }
      iExists _, _, _, _, _. iFrame "Hh24 Hh16 Hh8 Hfra Hfs0".
  Qed.

End WpHoldingInv.
