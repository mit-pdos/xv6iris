(* S-mode ALU-family leaf lemmas over the generalized page-table invariant
   [tlb_inv_pt] (ptree abstraction, arbitrary A/D bits under Svadu/ADUE).
   Ports of the Itype/Rtype/Utype/Addiw/Shiftiop leaves; see WpSmodePtLeaves.v
   for the engines and the migration recipe. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import MinstretInv InstrBytes WpGpr.
Require Import SRegime.
Require Import SmodeCore WpAuipc.
Require Import WpMmodeLeafBase WpMmodeShiftiop.
Require Import KptTree WpSmodePtLeaves.
Import Defs.

Section WpSmodePtAlu.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* ---- from WpSmodeItype.v ---- *)

  Lemma wp_addi4_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_regime R Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
              (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_addi4_s_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_addi4_s_r (kpt_regime root_ppn) Φ pc rd rs1 imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_addi4_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
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
    iApply (wp_addi4_s_r R Φ pc rd rs1 imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
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
    exact (wp_addi4_s_scfg_r (kpt_regime root_ppn) γ Φ pc rd rs1 imm m (dq:=dq)).
  Qed.

  Lemma wp_caddi4spn_gpr_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrdc Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_regime R Φ pc rd csp_rs1 csp_rs1
              (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      change sp with (Regidx csp_rs1).
      rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 rd (caddi4spn_imm nzimm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_caddi4spn_gpr_s_config_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_caddi4spn_gpr_s_config_r (kpt_regime root_ppn) Φ pc rdc nzimm rd m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_caddi4spn_gpr_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrdc Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_caddi4spn_gpr_s_config_r R Φ pc rdc nzimm rd m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrdc Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_caddi4spn_gpr_s_config_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_caddi4spn_gpr_s_config_scfg_r (kpt_regime root_ppn) γ Φ pc rdc nzimm rd m (dq:=dq)).
  Qed.

  Lemma wp_caddi_gpr_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_regime R Φ pc rd rd rd
              (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI))
              (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr rd rd (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_caddi_gpr_s_config_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_caddi_gpr_s_config_r (kpt_regime root_ppn) Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  (* c.addi16sp sp, imm6: the frame alloc/dealloc.  Raw-config form for the
     VCgen block executor (rd is always sp, so no rd<>0 arg); mirrors
     [wp_caddi_gpr_s_config_pt] with [rd := csp_rs1] and [caddi16sp_imm imm6]. *)
  Lemma wp_caddi16sp_gpr_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm6 : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    assert (Hsp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    unshelve iApply (wp_gpr_write_s_config_regime R Φ pc csp_rs1 csp_rs1 csp_rs1
              (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hsp
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change sp with (Regidx csp_rs1).
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 (caddi16sp_imm imm6) s_pc).
    replace (Z.eqb (uint csp_rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hsp).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_caddi16sp_gpr_s_config_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm6 : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_caddi16sp_gpr_s_config_r (kpt_regime root_ppn) Φ pc imm6 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_caddi_gpr_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_caddi_gpr_s_config_r R Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_caddi_gpr_s_config_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_caddi_gpr_s_config_scfg_r (kpt_regime root_ppn) γ Φ pc rd imm m (dq:=dq)).
  Qed.

  Lemma wp_candi_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_regime R Φ pc rd rd rd
              (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI))
              (and_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ANDI_gpr rd rd (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_andi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_candi_s_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_candi_s_r (kpt_regime root_ppn) Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_candi_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_candi_s_r R Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_candi_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_candi_s_scfg_r (kpt_regime root_ppn) γ Φ pc rd imm m (dq:=dq)).
  Qed.

  Lemma wp_cli_gpr_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_regime R Φ pc rd
              (zero_extend' 5 ('b"00")) (zero_extend' 5 ('b"00"))
              (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI))
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hrd
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) rd
               (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val.
    replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
      by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  Lemma wp_cli_gpr_s_config_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cli_gpr_s_config_r (kpt_regime root_ppn) Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_cli_gpr_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cli_gpr_s_config_r R Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_cli_gpr_s_config_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cli_gpr_s_config_scfg_r (kpt_regime root_ppn) γ Φ pc rd imm m (dq:=dq)).
  Qed.

  Lemma wp_caddi4spn_gpr_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    smode_config γ dq -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrdc Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_caddi4spn_gpr_s_config_r R Φ pc rdc nzimm rd m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrdc Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_caddi4spn_gpr_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    smode_config γ dq -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_caddi4spn_gpr_s_r (kpt_regime root_ppn) γ Φ pc rdc nzimm rd m (dq:=dq)).
  Qed.

  Lemma wp_caddi_gpr_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_caddi_gpr_s_config_r R Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_caddi_gpr_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
    ( smode_config γ dq -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_caddi_gpr_s_r (kpt_regime root_ppn) γ Φ pc rd imm m (dq:=dq)).
  Qed.

  Lemma wp_sltiu_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (sign_extend' 64 imm))) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg_regime R γ Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_SLTIU_gpr rs1 rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_sltiu_val. rewrite Hva Hwval. reflexivity.
  Qed.

  Lemma wp_sltiu_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (sign_extend' 64 imm))) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_sltiu_s_r (kpt_regime root_ppn) γ Φ pc rd rs1 imm wval m (dq:=dq)).
  Qed.

  (* ---- from WpSmodeRtype.v ---- *)

  Lemma wp_cadd_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_regime R Φ pc rd rd rs2
              (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD))
              (add_vec (m !!! Regidx rd) (m !!! Regidx rs2))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    change (execute (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx rd) (Regidx rd) ADD).
    rewrite (exec_execute_RTYPE_ADD_gpr rs2 rd rd s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_rd_val. rewrite Hva Hvb. reflexivity.
  Qed.

  Lemma wp_cadd_s_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cadd_s_r (kpt_regime root_ppn) Φ pc rd rs2 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_cadd_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cadd_s_r R Φ pc rd rs2 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_cmv_gpr_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_regime R Φ pc rd rs2 rs2
              (RTYPE (Regidx rs2, zreg, Regidx rd, ADD))
              (add_vec zero_reg (m !!! Regidx rs2))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd _
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

  Lemma wp_cmv_gpr_s_config_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cmv_gpr_s_config_r (kpt_regime root_ppn) Φ pc rd rs2 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_cmv_gpr_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cmv_gpr_s_config_r R Φ pc rd rs2 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_cmv_gpr_s_config_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cmv_gpr_s_config_scfg_r (kpt_regime root_ppn) γ Φ pc rd rs2 m (dq:=dq)).
  Qed.

  Lemma wp_cmv_gpr_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( smode_config γ dq -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cmv_gpr_s_config_r R Φ pc rd rs2 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_cmv_gpr_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( smode_config γ dq -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cmv_gpr_s_r (kpt_regime root_ppn) γ Φ pc rd rs2 m (dq:=dq)).
  Qed.

  Lemma wp_sltu_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (m !!! Regidx rs2))) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg_regime R γ Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    rewrite (exec_execute_RTYPE_SLTU_gpr rs2 rs1 rd s_pc Hrd).
    unfold gpr_sltu_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_sltu_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (m !!! Regidx rs2))) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_sltu_s_r (kpt_regime root_ppn) γ Φ pc rd rs1 rs2 wval m (dq:=dq)).
  Qed.

  Lemma wp_cor_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    or_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_scfg_regime R γ Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    rewrite (exec_execute_RTYPE_OR_gpr rs2 rs1 rd s_pc Hrd).
    unfold gpr_or_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_cor_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    or_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cor_s_r (kpt_regime root_ppn) γ Φ pc rd rs1 rs2 wval m (dq:=dq)).
  Qed.

  Lemma wp_sub_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    sub_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg_regime R γ Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)))
      with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SUB).
    rewrite (exec_execute_RTYPE_SUB_gpr rs2 rs1 rd s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_sub_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_sub_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    sub_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_sub_s_r (kpt_regime root_ppn) γ Φ pc rd rs1 rs2 wval m (dq:=dq)).
  Qed.

  Lemma wp_add_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    add_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg_regime R γ Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
    rewrite (exec_execute_RTYPE_ADD_gpr rs2 rs1 rd s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_rd_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_add_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    add_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_add_s_r (kpt_regime root_ppn) γ Φ pc rd rs1 rs2 wval m (dq:=dq)).
  Qed.

  Lemma wp_or_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    or_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg_regime R γ Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)))
      with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) OR).
    rewrite (exec_execute_RTYPE_OR_gpr rs2 rs1 rd s_pc Hrd).
    unfold gpr_or_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_or_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    or_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_or_s_r (kpt_regime root_ppn) γ Φ pc rd rs1 rs2 wval m (dq:=dq)).
  Qed.

  (* ---- from WpSmodeUtype.v ---- *)

  Lemma wp_auipc_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_pc_regime R Φ pc rd rd rd
              (UTYPE (imm, Regidx rd, AUIPC))
              (add_vec pc (auipc_off imm))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc HPCpc _ _.
    rewrite (exec_execute_UTYPE_AUIPC_gpr rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite HPCpc. reflexivity.
  Qed.

  Lemma wp_auipc_s_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_auipc_s_r (kpt_regime root_ppn) Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_auipc_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
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
    iApply (wp_auipc_s_r R Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

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
    exact (wp_auipc_s_scfg_r (kpt_regime root_ppn) γ Φ pc rd imm m (dq:=dq)).
  Qed.

  Lemma wp_clui_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    luival imm = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (UTYPE (imm, Regidx rd, LUI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_scfg_regime R γ Φ pc rd rd rd
              (UTYPE (imm, Regidx rd, LUI)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc _ _.
    rewrite (exec_execute_UTYPE_LUI_gpr rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hwval. reflexivity.
  Qed.

  Lemma wp_clui_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    luival imm = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (UTYPE (imm, Regidx rd, LUI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_clui_s_r (kpt_regime root_ppn) γ Φ pc rd imm wval m (dq:=dq)).
  Qed.

  (* ---- from WpSmodeAddiw.v ---- *)

  Lemma wp_caddiw_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm))) 31 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_regime R Φ pc rd rd rd
              (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd))
              (sign_extend' 64 (subrange_vec_dec
                 (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm))) 31 0))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ADDIW_gpr rd rd (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addiw_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_caddiw_s_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm))) 31 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_caddiw_s_r (kpt_regime root_ppn) Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_caddiw_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm))) 31 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_caddiw_s_r R Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_caddiw_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm))) 31 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_caddiw_s_scfg_r (kpt_regime root_ppn) γ Φ pc rd imm m (dq:=dq)).
  Qed.

  (* ---- from WpSmodeShiftiop.v ---- *)

  Lemma wp_cslli_gpr_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rsd : regidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    rsd = Regidx rd ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrsd Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_regime R Φ pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI))
              (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SLLI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_slli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_cslli_gpr_s_config_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rsd : regidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    rsd = Regidx rd ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cslli_gpr_s_config_r (kpt_regime root_ppn) Φ pc rsd rd shamt m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_cslli_gpr_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rsd : regidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    rsd = Regidx rd ->
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
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
    iApply (wp_cslli_gpr_s_config_r R Φ pc rsd rd shamt m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrsd Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

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
    exact (wp_cslli_gpr_s_config_scfg_r (kpt_regime root_ppn) γ Φ pc rsd rd shamt m (dq:=dq)).
  Qed.

  Lemma wp_csrli_gpr_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (crsd : cregidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    creg2reg_idx crsd = Regidx rd ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hcrsd Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_regime R Φ pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI))
              (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SRLI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_srli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_csrli_gpr_s_config_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (crsd : cregidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    creg2reg_idx crsd = Regidx rd ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_csrli_gpr_s_config_r (kpt_regime root_ppn) Φ pc crsd rd shamt m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_csrli_gpr_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (crsd : cregidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    creg2reg_idx crsd = Regidx rd ->
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hcrsd Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csrli_gpr_s_config_r R Φ pc crsd rd shamt m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hcrsd Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_csrli_gpr_s_config_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (crsd : cregidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    creg2reg_idx crsd = Regidx rd ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_csrli_gpr_s_config_scfg_r (kpt_regime root_ppn) γ Φ pc crsd rd shamt m (dq:=dq)).
  Qed.

  Lemma wp_srli4_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_regime R Φ pc rd rs1 rs1
              (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))
              (shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_SHIFTIOP_SRLI_gpr rs1 rd shamt s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_srli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_srli4_s_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_srli4_s_r (kpt_regime root_ppn) Φ pc rd rs1 shamt m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_srli4_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_srli4_s_r R Φ pc rd rs1 shamt m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_srli4_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_srli4_s_scfg_r (kpt_regime root_ppn) γ Φ pc rd rs1 shamt m (dq:=dq)).
  Qed.

  Lemma wp_slli_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 6) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    shift_bits_left (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg_regime R γ Φ pc rd rs1 rs1
              (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_SHIFTIOP_SLLI_gpr rs1 rd shamt s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_slli_val, gpr_src. rewrite Hva Hwval. reflexivity.
  Qed.

  Lemma wp_slli_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 6) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    shift_bits_left (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_slli_s_r (kpt_regime root_ppn) γ Φ pc rd rs1 shamt wval m (dq:=dq)).
  Qed.


  (* ---- walk's extra ALU leaves: register shift (loop-variable shamt),
     base ANDI/ORI, and the RVC shift-immediates ---------------------- *)

  Lemma wp_srl_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    shift_bits_right (m !!! Regidx rs1)
      (subrange_vec_dec (m !!! Regidx rs2) (Z.sub log2_xlen 1) 0) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SRL)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg_regime R γ Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SRL)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    rewrite (exec_execute_RTYPE_SRL_gpr rs2 rs1 rd s_pc Hrd).
    unfold gpr_srl_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_srl_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    shift_bits_right (m !!! Regidx rs1)
      (subrange_vec_dec (m !!! Regidx rs2) (Z.sub log2_xlen 1) 0) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SRL)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_srl_s_r (kpt_regime root_ppn) γ Φ pc rd rs1 rs2 wval m (dq:=dq)).
  Qed.

  Lemma wp_andi_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    and_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg_regime R γ Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ANDI_gpr rs1 rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_andi_val. rewrite Hva Hwval. reflexivity.
  Qed.

  Lemma wp_andi_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    and_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_andi_s_r (kpt_regime root_ppn) γ Φ pc rd rs1 imm wval m (dq:=dq)).
  Qed.

  Lemma wp_ori_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    or_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_base_scfg_regime R γ Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ORI_gpr rs1 rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_ori_val. rewrite Hva Hwval. reflexivity.
  Qed.

  Lemma wp_ori_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    or_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_ori_s_r (kpt_regime root_ppn) γ Φ pc rd rs1 imm wval m (dq:=dq)).
  Qed.

  Lemma wp_cslli_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (shamt : mword 6) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_scfg_regime R γ Φ pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_SHIFTIOP_SLLI_gpr rd rd shamt s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_slli_val, gpr_src. rewrite Hva Hwval. reflexivity.
  Qed.

  Lemma wp_cslli_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (shamt : mword 6) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cslli_s_r (kpt_regime root_ppn) γ Φ pc rd shamt wval m (dq:=dq)).
  Qed.

  Lemma wp_csrli_s_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (shamt : mword 6) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) = wval ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hwval) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config_scfg_regime R γ Φ pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)) wval m (dq:=dq)
 Hrd _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_SHIFTIOP_SRLI_gpr rd rd shamt s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_srli_val, gpr_src. rewrite Hva Hwval. reflexivity.
  Qed.

  Lemma wp_csrli_s_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (shamt : mword 6) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) = wval ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)) -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_csrli_s_r (kpt_regime root_ppn) γ Φ pc rd shamt wval m (dq:=dq)).
  Qed.

End WpSmodePtAlu.
