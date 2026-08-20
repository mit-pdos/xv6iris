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
Require Import RegFile.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SRegime.
Require Import RiscvExtras.
Require Import WpSmodePtLeaves.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

Section WpSmodePtMemWrap.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_cldsp_gpr_s_r_t (R : s_regime) (kt kt' : ktier) `{!KtierLe kt' kt}
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : regfile) (v : mword 64)
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
    sr_ktier_wit R kt -∗
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (imm, sp, Regidx rd, false, 8)) -∗
    pa ↦₈[kt']{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈[kt']{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm ea a8 pa Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    unfold pa, a8, ea.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    iIntros "#Hwit".
    iApply (wp_cld_s_r_t R kt kt' pc rd csp_rs1 imm m v
             mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
             Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 with "Hwit").
  Qed.

  Lemma wp_cldsp_gpr_s_r (R : s_regime)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : regfile) (v : mword 64)
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
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm ea a8 pa Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    unfold pa, a8, ea.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_cld_s_r R pc rd csp_rs1 imm m v
             mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
             Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0).
  Qed.


  Lemma wp_csdsp_gpr_s_r_t (R : s_regime) (kt kt' : ktier) `{!KtierLe kt' kt}
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : regfile) (vold : mword 64)
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
    sr_ktier_wit R kt -∗
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    pa ↦₈[kt'] vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈[kt'] (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm ea a8 pa HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    unfold pa, a8, ea.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    iIntros "#Hwit".
    iApply (wp_csd_s_r_t R kt kt' pc rs2 csp_rs1 imm m vold
             mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
             HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 with "Hwit").
  Qed.

  Lemma wp_csdsp_gpr_s_r (R : s_regime)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : regfile) (vold : mword 64)
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
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm ea a8 pa HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    unfold pa, a8, ea.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_csd_s_r R pc rs2 csp_rs1 imm m vold
             mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
             HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0).
  Qed.























End WpSmodePtMemWrap.
