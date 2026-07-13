(* S-mode Rtype leaf lemmas (smode_config/Supervisor, decode family Rtype).
   Relocated from function proof files (per-(mode,family) leaf reorg). *)
Require Import WpSmodeLeafBase.
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes WpDecode WpLeafCommon WpGpr WpGprCsrwCommon.
Require Import SmodeCore WpSmodeGpr WpEntryNew StackOwn CalleeSaved.
Require Import WpMmodeLeafBase WpSmodeLeafBase.
Import Defs.
Require Import WpMmodeRtype.

Section WpSmodeRtype.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_cadd_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ pc rd rd rs2
              (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD))
              (add_vec (m !!! Regidx rd) (m !!! Regidx rs2))
              m mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    change (execute (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx rd) (Regidx rd) ADD).
    rewrite (exec_execute_RTYPE_ADD_gpr rs2 rd rd s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_rd_val. rewrite Hva Hvb. reflexivity.
  Qed.

  Lemma wp_cmv_gpr_s_config (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ pc rd rs2 rs2
              (RTYPE (Regidx rs2, zreg, Regidx rd, ADD))
              (add_vec zero_reg (m !!! Regidx rs2))
              m mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      change (execute (RTYPE (Regidx rs2, Regidx (zero_extend' 5 ('b"00") : mword 5), Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx (zero_extend' 5 ('b"00") : mword 5)) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 (zero_extend' 5 ('b"00") : mword 5) rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_rd_val.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
      rewrite Hva. reflexivity.
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

  Lemma wp_cmv_gpr_s (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    smode_config γ dq -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( smode_config γ dq -∗
      tlb_inv root_ppn -∗
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

  (* Specific per-instruction leaf lemmas (instr precondition fixes the RTYPE op;
     a pure map-form value hypothesis replaces the generic [exec (execute i)]). *)

  Lemma wp_sltu_s (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (m !!! Regidx rs2))) = wval ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg root_ppn γ E Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) wval m (dq:=dq)
              HN Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    rewrite (exec_execute_RTYPE_SLTU_gpr rs2 rs1 rd s_pc Hrd).
    unfold gpr_sltu_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_cor_s (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    or_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_scfg root_ppn γ E Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) wval m (dq:=dq)
              HN Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    rewrite (exec_execute_RTYPE_OR_gpr rs2 rs1 rd s_pc Hrd).
    unfold gpr_or_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_sub_s (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    sub_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg root_ppn γ E Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) wval m (dq:=dq)
              HN Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)))
      with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SUB).
    rewrite (exec_execute_RTYPE_SUB_gpr rs2 rs1 rd s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_sub_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_add_s (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    add_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg root_ppn γ E Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) wval m (dq:=dq)
              HN Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
    rewrite (exec_execute_RTYPE_ADD_gpr rs2 rs1 rd s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_rd_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

End WpSmodeRtype.
