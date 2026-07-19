(* WpSmodePtMemWrap.v -- smode_config wrappers and sp-relative forms for
   the [tlb_inv_pt] load/store leaves, plus the width-1 store leaf
   [wp_sb_s_pt].  The old _ram indirection disappears: the pt base leaves
   have no geometry premises, so these wrappers only (un)bundle
   [smode_config] and bridge the c.ldsp/c.sdsp immediate form. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SRegime.
Require Import SmodeCore.
Require Import KptTree WpSmodePtLeaves WpSmodePtMem.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Section WpSmodePtMemWrap.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_cldsp_gpr_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : gmap regidx (mword 64)) (v : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let a8 := ea in
    let pa := a8 in
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (imm, sp, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm ea a8 pa Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    unfold pa, a8, ea.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_cld_s_r R Φ pc rd csp_rs1 imm m v
             mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
             Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0).
  Qed.

  Lemma wp_cldsp_gpr_s_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : gmap regidx (mword 64)) (v : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let a8 := ea in
    let pa := a8 in
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (imm, sp, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cldsp_gpr_s_r (kpt_regime root_ppn) Φ pc uimm rd m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)).
  Qed.

  Lemma wp_csdsp_gpr_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let a8 := ea in
    let pa := a8 in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm ea a8 pa HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    unfold pa, a8, ea.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_csd_s_r R Φ pc rs2 csp_rs1 imm m vold
             mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
             HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0).
  Qed.

  Lemma wp_csdsp_gpr_s_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let a8 := ea in
    let pa := a8 in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_csdsp_gpr_s_r (kpt_regime root_ppn) Φ pc uimm rs2 m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

  Lemma wp_cld_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : bv 64) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    ea ↦₈{ dqm } v -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
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
    iApply (wp_cld_s_r R Φ pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
 Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_cld_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : bv 64) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    ea ↦₈{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cld_s_scfg_r (kpt_regime root_ppn) γ Φ pc rd rs1 imm m v (dq:=dq) (dqm:=dqm)).
  Qed.

  Lemma wp_cldsp_gpr_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : gmap regidx (mword 64)) (v : bv 64) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8)) -∗
    ea ↦₈{ dqm } v -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
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
    iApply (wp_cldsp_gpr_s_r R Φ pc uimm rd m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
 Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_cldsp_gpr_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : gmap regidx (mword 64)) (v : bv 64) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8)) -∗
    ea ↦₈{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_cldsp_gpr_s_scfg_r (kpt_regime root_ppn) γ Φ pc uimm rd m v (dq:=dq) (dqm:=dqm)).
  Qed.

  Lemma wp_clw_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 32) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    ea ↦₄{ dqm } v -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      ea ↦₄{ dqm } v -∗
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
    iApply (wp_clw_s_r R Φ pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
 Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_clw_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 32) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    ea ↦₄{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      ea ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_clw_s_scfg_r (kpt_regime root_ppn) γ Φ pc rd rs1 imm m v (dq:=dq) (dqm:=dqm)).
  Qed.

  Lemma wp_lw_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 32) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    ea ↦₄{ dqm } v -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      ea ↦₄{ dqm } v -∗
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
    iApply (wp_lw_s_r R Φ pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
 Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_lw_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 32) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    ea ↦₄{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      ea ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_lw_s_scfg_r (kpt_regime root_ppn) γ Φ pc rd rs1 imm m v (dq:=dq) (dqm:=dqm)).
  Qed.

  Lemma wp_ld_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : bv 64) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    ea ↦₈{ dqm } v -∗
    ( smode_config γ dq -∗ sr_inv R -∗
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
    iApply (wp_ld_s_r R Φ pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
 Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
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
    exact (wp_ld_s_scfg_r (kpt_regime root_ppn) γ Φ pc rd rs1 imm m v (dq:=dq) (dqm:=dqm)).
  Qed.

  Lemma wp_csd_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
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
    iApply (wp_csd_s_r R Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_csd_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_csd_s_scfg_r (kpt_regime root_ppn) γ Φ pc rs2 rs1 imm m vold (dq:=dq)).
  Qed.

  Lemma wp_csdsp_gpr_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      ea ↦₈ (m !!! Regidx rs2) -∗
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
    iApply (wp_csdsp_gpr_s_r R Φ pc uimm rs2 m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_csdsp_gpr_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_csdsp_gpr_s_scfg_r (kpt_regime root_ppn) γ Φ pc uimm rs2 m vold (dq:=dq)).
  Qed.

  Lemma wp_csdsp_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm ea.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csdsp_gpr_s_r R Φ pc uimm rs2 m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_csdsp_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_csdsp_s_scfg_r (kpt_regime root_ppn) γ Φ pc uimm rs2 m vold (dq:=dq)).
  Qed.

  Lemma wp_csw_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₄ (RiscvExtras.trunc32 (m !!! Regidx rs2)) -∗
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
    iApply (wp_csw_s_r R Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_csw_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₄ (RiscvExtras.trunc32 (m !!! Regidx rs2)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_csw_s_scfg_r (kpt_regime root_ppn) γ Φ pc rs2 rs1 imm m vold (dq:=dq)).
  Qed.

  Lemma wp_sw_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      ea ↦₄ (trunc32 (m !!! Regidx rs2)) -∗
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
    iApply (wp_sw_s_r R Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_sw_s_scfg_pt (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( smode_config γ dq -∗ tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      ea ↦₄ (trunc32 (m !!! Regidx rs2)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_sw_s_scfg_r (kpt_regime root_ppn) γ Φ pc rs2 rs1 imm m vold (dq:=dq)).
  Qed.

  Lemma wp_sd_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ sr_inv R -∗
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
    iApply (wp_sd_s_r R Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
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
    exact (wp_sd_s_scfg_r (kpt_regime root_ppn) γ Φ pc rs2 rs1 imm m vold (dq:=dq)).
  Qed.

End WpSmodePtMemWrap.
