(* WpFreelistMem.v -- S-mode load/store WPs for the kalloc/kfree free-list
   accesses, in the "a word_pointsto is all you need" style: given only
   [pa ↦₈ v] (which carries [addr_is_ram pa]) plus the standard S-mode config
   and the RAM/PMP-coverage facts, the whole Sv39 super-page-identity geometry
   is DERIVED internally from the [ram_*] lemma family (SmodeCore.v), so the
   caller supplies NO [po_slot_geom] hypothesis for the accessed address.

   Mirrors [wp_cldsp_gpr_s_ram] (WpSmodeGpr.v), generalised off the [sp]
   base register to an arbitrary [rs1], and provided for both the compressed
   (c.ld / c.sd) and base (ld / sd) instruction encodings. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpPushOffMem WpAcquireMem WpLockLeaves WpGprRvcTor.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section FreelistMem.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* Shared boilerplate for the RAM derivation: from the 8-byte window's bytes,
     recover [addr_is_ram pa], [addr_is_ram (pa_add pa 7)], and the
     [ram_base <= uint pa] / [uint pa + 8 <= ram_base + ram_size] bounds. *)
  Local Lemma ram_bounds_of_bytes (pa : mword 64) (dqm : dfrac) (v : bv 64) :
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ{dqm} nth_byte v j) -∗
    ⌜ addr_is_ram pa /\ addr_is_ram (pa_add pa 7)
      /\ (ram_base <= uint pa)%Z /\ (uint pa + 8 <= ram_base + ram_size)%Z ⌝.
  Proof.
    iIntros "Hbytes".
    iAssert (⌜addr_is_ram pa⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr. iPureIntro. exact Hr. }
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hr7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    iPureIntro.
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hr0 as [H _]; exact H).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hr0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hr7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    split; [exact Hr0 | split; [exact Hr7 | split; [exact Hlo | exact Hfit]]].
  Qed.

  (* ---- compressed c.ld rd, imm(rs1) ---- *)
  Lemma wp_cld_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp HR.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpalign8 & Hbytes)".
    iDestruct (ram_bounds_of_bytes pa dqm v with "Hbytes") as %(Hr0 & _ & Hlo & Hfit).
    iApply (wp_cld_s root_ppn E Φ pc rd rs1 imm (svpn_of a8) m v
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov
              (ram_canonical a8 Hr0) ltac:(reflexivity) (ram_ident root_ppn a8 Hr0)
              (ram_mask a8 Hr0) (ram_svpn2 a8 Hr0) (ram_mvpn a8 Hr0) (ram_mppn a8 Hr0)
              Hpmpp Hpteregion Halignp
              (ram_pmp_match a8 (vec_access_dec pmpaddr00 0) Hlo Hfit Hcov) HR
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr [Hbytes] Hcont").
    rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8.
  Qed.

  (* ---- compressed c.sd rs2, imm(rs1) ---- *)
  Lemma wp_csd_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := m !!! Regidx rs2 in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp HW.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpalign8 & Hbytes)".
    iDestruct (ram_bounds_of_bytes pa (DfracOwn 1) vold with "Hbytes") as %(Hr0 & _ & Hlo & Hfit).
    iApply (wp_csd_s root_ppn E Φ pc rs2 rs1 imm (svpn_of a8) m vold
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov
              (ram_canonical a8 Hr0) ltac:(reflexivity) (ram_ident root_ppn a8 Hr0)
              (ram_mask a8 Hr0) (ram_svpn2 a8 Hr0) (ram_mvpn a8 Hr0) (ram_mppn a8 Hr0)
              Hpmpp Hpteregion Halignp
              (ram_pmp_match a8 (vec_access_dec pmpaddr00 0) Hlo Hfit Hcov) HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr [Hbytes] Hcont").
    rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8.
  Qed.

End FreelistMem.
