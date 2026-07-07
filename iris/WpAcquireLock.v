(* WpAcquireLock.v -- the CSL acquire spec: given [is_lock γ lk R], a run of
   acquire() that RETURNS has taken the lock -- the caller's continuation
   receives the ownership token [locked γ] and the protected resource [R],
   both taken OUT of the lock invariant by the winning amoswap
   (WpLockLeaves.wp_amoswap_lockinv).  If the lock stays held the amoswap
   loop spins forever -- proved by Löb induction in [wp_acquire_lock_loop],
   where EACH iteration opens the invariant: a nonzero read re-enters the
   induction hypothesis (the c.bnez-taken step runs on the raw engine so its
   later strips the IH's), a zero read exits with [locked γ ∗ R].

   Both lemmas are clones of WpAcquireTop.wp_acquire{_spin} with the lock
   word accessed through the invariant instead of an owned byte window. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
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
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpPushOffMem WpPushOffCsr WpMycpu WpPushOffTop WpAmo WpAcquireMem WpHolding WpAcquireTop.
Require Import WpRvcBridge WpLock WpLockLeaves WpHoldingInv.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section WpAcquireLock.
  Context `{!riscvGS Σ, !lockG Σ}.
  Context `{CID : CpuId}.

  Notation PO := KernelSyms.push_off.

  Lemma wp_acquire_lock_loop (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (R : iProp Σ)
      (M0 : gmap regidx (mword 64)) (a5v lk : mword 64) (svpn_lk : mword 27)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) :
    let a4one : mword 64 := add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (* fetch geometry over the loop body: a single X-bit fact + RAM coverage;
       the RAM/PMP fetch geometry is derived internally from instr_bytes *)
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    (* the lock word's data-slot geometry *)
    po_slot_geom root_ppn pmpaddr00 svpn_lk lk 4 ->
    (forall pmar0, pma_allows_all pmar0 ->
       exists region_amo,
         matching_pma_region pmar0 (Physaddr lk) 4 = Some region_amo /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_readable) = true /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_writable) = true /\
         pma_allows_atomic_op
           ((override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_atomic_support))
           AMOSWAP 4 = true) ->
    (* the loop-invariant register facts *)
    M0 !!! Regidx (mword_of_int 14 : mword 5) = a4one ->
    M0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int (AQ + 0x1a)) -∗
    gpr_file (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg a5v]> M0) -∗
    is_lock γ lk R -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (mword_of_int (AQ + 0x24)) -∗
      gpr_file (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> M0) -∗
      locked γ -∗ R -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros a4one HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hpmpp Hpteregion Halignp HR HW
      HX Hcov Hg_lk Hpma_amo HM0a4 HM0s1.
    pose proof Hg_lk as (Lcanon & Lvpn & Lident & Lmask & Lvpn2 & Lmvpn & Lmppn & Lrange & Lalign & Lpalign).
    (* a5v-independent register/address facts, posed once outside the Löb *)
    assert (Ha4any : forall w : mword 64,
        (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w]> M0) !!! Regidx (mword_of_int 14 : mword 5) = a4one).
    { intro w. rewrite lookup_total_insert_ne; [ exact HM0a4 | vm_compute; discriminate ]. }
    assert (Hs1any : forall w : mword 64,
        (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w]> M0) !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { intro w. rewrite lookup_total_insert_ne; [ exact HM0s1 | vm_compute; discriminate ]. }
    assert (HAlk2 : add_vec (add_vec zero_reg lk) (zeros' 64) = lk).
    { rewrite aq_addv_zero_l.
      replace (zeros' 64 : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    set (v1 := add_vec zero_reg a4one).
    assert (Hst1 : amoswap_stored v1 = (mword_of_int 1 : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Htgt : add_vec (mword_of_int (AQ + 0x22) : mword 64)
              (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
            = mword_of_int (AQ + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv #Htext Hpc Hfile #Hlock Hcont".
    iPoseProof (aqi_1a with "Htext") as "#Hj1a".
    iPoseProof (aqi_1c with "Htext") as "#Hj1c".
    iPoseProof (aqi_20 with "Htext") as "#Hj20".
    iPoseProof (aqi_22 with "Htext") as "#Hj22".
    iRevert "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hcont".
    iLöb as "IH" forall (a5v).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hcont".
    (* ---- +0x1a: c.mv a5,a4 ---- *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg a5v]> M0)
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hj1a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite (Ha4any a5v) insert_insert) in "Hfile".
    assert (Hpp1c : add_vec_int (mword_of_int (AQ + 0x1a) : mword 64) 2 = mword_of_int (AQ + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ---- +0x1c: amoswap.w.aq a5,a5,(s1) through the invariant ---- *)
    assert (HPAlk : add_vec ((<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0)
                              !!! Regidx (mword_of_int 9 : mword 5)) (zeros' 64) = lk)
      by (rewrite (Hs1any v1); exact HAlk2).
    assert (HSTZ : neq_vec (sign_extend' 64 (amoswap_stored
                     ((<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0)
                        !!! Regidx (mword_of_int 15 : mword 5)))) zero_reg = true)
      by (rewrite lookup_total_insert Hst1; vm_compute; reflexivity).
    iApply (wp_amoswap_lockinv root_ppn E Φ γ lk R (mword_of_int (AQ + 0x1c)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 9)
              svpn_lk (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0)
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HNl HPAlk
              HSTZ
              ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX
              Hcov
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lcanon)
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lvpn)
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lident)
              Lmask Lvpn2 Lmvpn Lmppn Hpmpp Hpteregion Halignp
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lrange) HR HW
              ltac:(rewrite (Hs1any v1) HAlk2; exact Hpma_amo)
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lalign)
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lpalign)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hj1c Hlock [-]").
    iIntros (w) "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hpay".
    iEval (rewrite insert_insert) in "Hfile".
    assert (Hpp20 : add_vec_int (mword_of_int (AQ + 0x1c) : mword 64) 4 = mword_of_int (AQ + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* ---- +0x20: sext.w a5 ---- *)
    iApply (wp_caddiw_s root_ppn E Φ (mword_of_int (AQ + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (amoswap_loaded w)]> M0)
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hj20 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite lookup_total_insert insert_insert) in "Hfile".
    assert (Hroundw : sign_extend' 64 (subrange_vec_dec
        (add_vec (amoswap_loaded w) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)
        = sign_extend' 64 w) by (apply aq_sextw_round).
    iEval (rewrite Hroundw) in "Hfile".
    assert (Hpp22 : add_vec_int (mword_of_int (AQ + 0x20) : mword 64) 2 = mword_of_int (AQ + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    iDestruct "Hpay" as "[(%Hw0 & Htok & HRes) | %Hwnz]".
    - (* ---- w = 0: ACQUIRED -- c.bnez falls through; hand over token + R ---- *)
      subst w.
      iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (AQ + 0x22)) (mword_of_int 252) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> M0)
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hj22 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      assert (Hpp24 : add_vec_int (mword_of_int (AQ + 0x22) : mword 64) 2 = mword_of_int (AQ + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Htok HRes").
    - (* ---- w <> 0: c.bnez TAKEN back to +0x1a; loop via the Löb IH ---- *)
    (* ---- +0x22: c.bnez a5 TAKEN (a5 = sext32(1) <> 0), back to +0x1a ----
       Run on the raw engine so the step's later strips the Löb IH's. *)
    iDestruct "Hpc" as "[Hpc Hnpc]".
    iDestruct "Hfile" as "[%Hdom Hfmap]".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ (mword_of_int (AQ + 0x22)) true
              (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hj22").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 w)]> M0) !! Regidx (mword_of_int 15 : mword 5)
                  = Some ((<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 w)]> M0) !!! Regidx (mword_of_int 15 : mword 5)))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int (mword_of_int (AQ + 0x22)) 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int (mword_of_int (AQ + 0x22)) 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = mword_of_int (AQ + 0x22)).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value (mword_of_int 15) _ s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iMod (reg_update _ nextPC _ (mword_of_int (AQ + 0x1a)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro. iExists (set_reg s_pc nextPC (mword_of_int (AQ + 0x1a))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc.
      replace (creg2reg_idx (Cregidx (mword_of_int 7))) with (Regidx (mword_of_int 15 : mword 5))
        by (vm_compute; reflexivity).
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : neq_vec (rvv (mword_of_int 15) s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match.
        rewrite lookup_total_insert. exact Hwnz. }
      epose proof (exec_execute_BTYPE_BNE_taken (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")))
                     (zero_extend' 5 ('b"00")) (mword_of_int 15) s_pc Htk) as Hred.
      rewrite Hpcv Htgt in Hred.
      exact (Hred ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC (mword_of_int (AQ + 0x1a))).(sregs) = mword_of_int (AQ + 0x1a))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    (* strip the step's later against the Löb hypothesis and loop *)
    iNext.
    iApply ("IH" $! (sign_extend' 64 w) with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes] [$Hpc' $Hnpc] [Hfmap] Hcont").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  Lemma wp_acquire_lock (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (R : iProp Σ)
      (m : gmap regidx (mword 64))
      (svpn_noff svpn_intena svpn_lk svpn_cpu : mword 27)
      (vr24 vr16 vr8 pr24 pr16 pr8 fraold fs0old cpuold : bv 64)
      (noff intena_old : mword 32) (a0f : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) :
    let AQw : mword 64 := mword_of_int AQ in
    let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    (* acquire's own frame slots (ra/s0/s1 saves at spd+24/+16/+8) *)
    let a_r24 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_r16 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_r8  := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    (* push_off's frame below (its sp is spd): slots at spd-8/-16/-24 *)
    let po_spd := add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let a_p24 := add_vec po_spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_p16 := add_vec po_spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_p8  := add_vec po_spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    (* mycpu's frame under push_off: slots at spd-40/-48 *)
    let po_spm10 := add_vec po_spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let a_fra := add_vec po_spm10 (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_fs0 := add_vec po_spm10 (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    (* the per-cpu noff/intena words *)
    let a_noff := add_vec a0f (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_intena := add_vec a0f (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    (* the spinlock's fields *)
    let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    (* prologue register chain *)
    let A0 := <[Regidx csp_rs1 := regval_into_reg spd]> m in
    let A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0 in
    let A2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1 in
    (* push_off's entry map (after the jal's link write) *)
    let P0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)]> A2 in
    (* push_off's internal register chain (mirrors wp_push_off's lets) *)
    let PN0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (P0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> P0 in
    let PN1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (PN0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> PN0 in
    let PN2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read mstatus0)]> PN1 in
    let PN3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (PN2 !!! Regidx (mword_of_int 15 : mword 5)))]> PN2 in
    let PN4 := po_mycpu_out (mword_of_int (PO + 0x10)) PN3 in
    let PN5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noff)]> PN4 in
    let PN6 := po_mycpu_out (mword_of_int (PO + 0x2c)) PN5 in
    let PN7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (PN6 !!! Regidx (mword_of_int 9 : mword 5))
           (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))]> PN6 in
    let PN8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (PN7 !!! Regidx (mword_of_int 15 : mword 5))
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> PN7 in
    (* push_off's noff/intena update values (mirrors wp_push_off) *)
    let po_storeval32 := (autocast (T := mword)
        (subrange_vec_dec (PN8 !!! Regidx (mword_of_int 15 : mword 5)) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let po_noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let po_noff_store := (autocast (T := mword) (subrange_vec_dec po_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    (* the return target *)
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    (* ---- S-mode configuration ---- *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    legalize_sstatus_val mstatus0 (sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    (* ---- the amoswap data cell additionally supports amoswap.w ---- *)
    (forall pmar0, pma_allows_all pmar0 ->
       exists region_amo,
         matching_pma_region pmar0 (Physaddr lk) 4 = Some region_amo /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_readable) = true /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_writable) = true /\
         pma_allows_atomic_op
           ((override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_atomic_support))
           AMOSWAP 4 = true) ->
    (* ---- push_off's a0f pins (its two mycpu calls return &cpus[cpuid]) ---- *)
    po_mycpu_out (mword_of_int (PO + 0x10)) PN3 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    po_mycpu_out (mword_of_int (PO + 0x2c)) PN5 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    po_mycpu_out (mword_of_int (PO + 0x18)) PN5 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    po_mycpu_out (mword_of_int (PO + 0x18)) PN8 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    (* ---- fetch geometry: a single X-bit fact threaded to every instruction
       (covers acquire, push_off, holding, and both mycpu call sites); the
       RAM/PMP fetch geometry is derived internally from instr_bytes ---- *)
    po_mycpu_geom pmpcfg0 pmpaddr00 ->
    (* ---- the lock is not already held by THIS cpu (no panic) ---- *)
    eq_vec (cpuold : mword 64) (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = false ->
    (* ---- data-slot geometry ---- *)
    po_slot_geom root_ppn pmpaddr00 svpn_noff a_noff 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_intena a_intena 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_lk lk 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_cpu a_cpu 8 ->
    (* ---- the return target is well-aligned ---- *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is AQw -∗ gpr_file m -∗
    a_r24 ↦₈ vr24 -∗
    a_r16 ↦₈ vr16 -∗
    a_r8 ↦₈ vr8 -∗
    a_p24 ↦₈ pr24 -∗
    a_p16 ↦₈ pr16 -∗
    a_p8 ↦₈ pr8 -∗
    a_fra ↦₈ fraold -∗
    a_fs0 ↦₈ fs0old -∗
    ([∗ list] j ∈ seq 0 4, (pa_add a_noff j) ↦ₘ nth_byte noff j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add a_intena j) ↦ₘ nth_byte intena_old j) -∗
    is_lock γ lk R -∗
    a_cpu ↦₈ cpuold -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      locked γ -∗ R -∗
      (∃ mfin, gpr_file mfin ∗
        ⌜ mfin !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5) /\
          mfin !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5) /\
          mfin !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5) /\
          mfin !!! Regidx csp_rs1 = m !!! Regidx csp_rs1 /\
          mfin !!! Regidx (mword_of_int 10 : mword 5)
            = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) /\
          mfin !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5) ⌝) -∗
      a_r24 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      a_r16 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
      a_r8 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
      (∃ (vp24 vp16 vp8 vfra vfs0 : bv 64),
        a_p24 ↦₈ vp24 ∗
        a_p16 ↦₈ vp16 ∗
        a_p8 ↦₈ vp8 ∗
        a_fra ↦₈ vfra ∗
        a_fs0 ↦₈ vfs0) -∗
      ([∗ list] j ∈ seq 0 4, (pa_add a_noff j) ↦ₘ nth_byte po_noff_store j) -∗
      ([∗ list] j ∈ seq 0 4, (pa_add a_intena j) ↦ₘ
          nth_byte (if eq_vec (sign_extend' 64 noff) zero_reg then po_storeval32 else intena_old) j) -∗
      a_cpu ↦₈ (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros AQw lk sp0 spd a_r24 a_r16 a_r8 po_spd a_p24 a_p16 a_p8 po_spm10 a_fra a_fs0
      a_noff a_intena a_cpu A0 A1 A2 P0 PN0 PN1 PN2 PN3 PN4 PN5 PN6 PN7 PN8
      po_storeval32 po_noff_a5 po_noff_store ret_tgt
      HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hpmpp Hpteregion Halignp HW HR Hramcov
      Hlegal Hpma_amo Ha0_10 Ha0_2c Ha0_18f Ha0_18t Hmyg Hnotmine
      Hg_noff Hg_intena Hg_lk Hg_cpu Hal0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv #Htext Hpc Hfile
             Hr24 Hr16 Hr8 Hp24 Hp16 Hp8 Hfra Hfs0 Hnoff Hintena #Hlk Hcpu Hcont".
    iPoseProof (aqi_00 with "Htext") as "Hi00".
    iPoseProof (aqi_02 with "Htext") as "Hi02".
    iPoseProof (aqi_04 with "Htext") as "Hi04".
    iPoseProof (aqi_06 with "Htext") as "Hi06".
    iPoseProof (aqi_08 with "Htext") as "Hi08".
    iPoseProof (aqi_0a with "Htext") as "Hi0a".
    iPoseProof (aqi_0c with "Htext") as "Hi0c".
    iPoseProof (aqi_10 with "Htext") as "Hi10".
    iPoseProof (aqi_12 with "Htext") as "Hi12".
    iPoseProof (aqi_16 with "Htext") as "Hi16".
    iPoseProof (aqi_18 with "Htext") as "Hi18".
    iPoseProof (aqi_1a with "Htext") as "Hi1a".
    iPoseProof (aqi_1c with "Htext") as "Hi1c".
    iPoseProof (aqi_20 with "Htext") as "Hi20".
    iPoseProof (aqi_22 with "Htext") as "Hi22".
    iPoseProof (aqi_24 with "Htext") as "Hi24".
    iPoseProof (aqi_28 with "Htext") as "Hi28".
    iPoseProof (aqi_2a with "Htext") as "Hi2a".
    iPoseProof (aqi_2c with "Htext") as "Hi2c".
    iPoseProof (aqi_2e with "Htext") as "Hi2e".
    iPoseProof (aqi_30 with "Htext") as "Hi30".
    iPoseProof (aqi_32 with "Htext") as "Hi32".
    (* the entry pc in the canonical (AQ + 0x00) spelling *)
    assert (Hpc00 : (mword_of_int AQ : mword 64) = mword_of_int (AQ + 0x00))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite /AQw Hpc00) in "Hpc".
    (* slot-align components *)
    (* ---- 0x00: c.addi sp,-32 ---- *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x00)) csp_rs1 (mword_of_int 32 : mword 6) m
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpp02 : add_vec_int (mword_of_int (AQ + 0x00) : mword 64) 2 = mword_of_int (AQ + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (Hcsp0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0; apply lookup_total_insert).
    (* ---- 0x02: c.sdsp ra,24(sp) ---- *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 vr24 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi02 [Hr24] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr24". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr24".
    assert (HA0ra : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hcsp0 HA0ra) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (AQ + 0x02) : mword 64) 2 = mword_of_int (AQ + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,16(sp) ---- *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 vr16 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi04 [Hr16] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr16".
    assert (HA0s0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hcsp0 HA0s0) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (AQ + 0x04) : mword 64) 2 = mword_of_int (AQ + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.sdsp s1,8(sp) ---- *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 vr8 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi06 [Hr8] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr8". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr8".
    assert (HA0s1 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hcsp0 HA0s1) in "Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (AQ + 0x06) : mword 64) 2 = mword_of_int (AQ + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpp0a : add_vec_int (mword_of_int (AQ + 0x08) : mword 64) 2 = mword_of_int (AQ + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- 0x0a: c.mv s1,a0 ---- *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x0a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              A1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1) with A2.
    assert (Hpp0c : add_vec_int (mword_of_int (AQ + 0x0a) : mword 64) 2 = mword_of_int (AQ + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* ---- 0x0c: jal ra,push_off ---- *)
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    assert (EQ0e : add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 2 = mword_of_int (AQ + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_gpr_s root_ppn E Φ (mword_of_int (AQ + 0x0c)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fffba : mword 21)
              A2 pmpcfg0 pmpaddr00 region_pte (1/2)%Qp
              HN Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)]> A2) with P0.
    assert (Htgtpo : add_vec (mword_of_int (AQ + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 0x1fffba : mword 21)) = mword_of_int (PO + 0x00))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtpo) in "Hpc".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    (* ---- push_off ---- *)
    assert (HP0csp : P0 !!! Regidx csp_rs1 = spd).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hcsp0. }
    assert (HP0ra : P0 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)
      by (rewrite /P0; apply lookup_total_insert).
    assert (E1a : add_vec_int (mword_of_int (PO + 0x18) : mword 64) 2 = mword_of_int (PO + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_push_off root_ppn E Φ P0 svpn_noff svpn_intena pr24 pr16 pr8 fraold fs0old noff intena_old a0f
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hpmpp Hpteregion Halignp HW HR Hramcov
              Hlegal ltac:(vm_compute; reflexivity)
              ltac:(rewrite HP0ra; vm_compute; reflexivity)
              Ha0_10 Ha0_2c Ha0_18f Ha0_18t Hmyg
              Hg_noff Hg_intena
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile [Hp24] [Hp16] [Hp8] [Hfra] [Hfs0] [Hnoff] [Hintena] [-]").
    { iEval (rewrite HP0csp). iExact "Hp24". }
    { iEval (rewrite HP0csp). iExact "Hp16". }
    { iEval (rewrite HP0csp). iExact "Hp8". }
    { iEval (rewrite HP0csp). iExact "Hfra". }
    { iEval (rewrite HP0csp). iExact "Hfs0". }
    { iExact "Hnoff". }
    { iExact "Hintena". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hmfin Hp24 Hp16 Hp8 Hjunk Hnoff Hintena".
    iEval (rewrite HP0csp) in "Hp24". iEval (rewrite HP0csp) in "Hp16". iEval (rewrite HP0csp) in "Hp8".
    iEval (rewrite HP0csp) in "Hjunk".
    assert (Hpc10 : update_vec_dec (add_vec (P0 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AQ + 0x10))
      by (rewrite HP0ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    iDestruct "Hmfin" as (mfin) "[Hfile %Hmf]".
    destruct Hmf as (Hfra_ & Hfs0_ & Hfs1_ & Hfsp_ & Hftp_).
    (* canonical values of the tracked registers after push_off *)
    assert (HP0s1 : P0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert.
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0tp : P0 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s0 : P0 !!! Regidx (mword_of_int 8 : mword 5) = A1 !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    rewrite HP0s1 in Hfs1_. rewrite HP0csp in Hfsp_. rewrite HP0tp in Hftp_. rewrite HP0ra in Hfra_.
    (* ---- 0x10: c.mv a0,s1 ---- *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mfin mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (B1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfin !!! Regidx (mword_of_int 9 : mword 5)))]> mfin).
    assert (Hpp12 : add_vec_int (mword_of_int (AQ + 0x10) : mword 64) 2 = mword_of_int (AQ + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- 0x12: jal ra,holding ---- *)
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    assert (EQ14 : add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 2 = mword_of_int (AQ + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_gpr_s root_ppn E Φ (mword_of_int (AQ + 0x12)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fff88 : mword 21)
              B1 pmpcfg0 pmpaddr00 region_pte (1/2)%Qp
              HN Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    set (B2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 4)]> B1).
    assert (Htgtho : add_vec (mword_of_int (AQ + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 0x1fff88 : mword 21)) = mword_of_int KernelSyms.holding)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtho) in "Hpc".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    (* ---- holding() (fast path) ---- *)
    assert (HB2a0 : B2 !!! Regidx (mword_of_int 10 : mword 5) = add_vec zero_reg (add_vec zero_reg lk)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert. rewrite Hfs1_. reflexivity. }
    assert (HB2ra : B2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 4)
      by (rewrite /B2; apply lookup_total_insert).
    assert (Eh2 : add_vec_int (mword_of_int KernelSyms.holding : mword 64) 2 = mword_of_int (KernelSyms.holding + 2))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eh4 : add_vec_int (mword_of_int KernelSyms.holding : mword 64) 4 = mword_of_int (KernelSyms.holding + 4))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eh6 : add_vec_int (mword_of_int KernelSyms.holding : mword 64) 6 = mword_of_int (KernelSyms.holding + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (HAlk : add_vec (B2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lk).
    { rewrite HB2a0. rewrite !aq_addv_zero_l.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* address bridges into wp_holding_lockinv's own lets *)
    assert (HB2sp : B2 !!! Regidx csp_rs1 = spd).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfsp_. }
    assert (HB2tp : B2 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hftp_. }
    assert (HAcpu2 : add_vec (B2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = a_cpu)
      by (rewrite HB2a0 !aq_addv_zero_l; reflexivity).
    assert (Hspdh_eq : add_vec (B2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = po_spd)
      by (rewrite HB2sp; reflexivity).
    iDestruct "Hjunk" as (vfra0 vfs00) "[Hfra2 Hfs02]".
    iApply (wp_holding_lockinv root_ppn E Φ γ lk R B2 svpn_lk svpn_cpu cpuold
              (P0 !!! Regidx (mword_of_int 1 : mword 5)) (P0 !!! Regidx (mword_of_int 8 : mword 5))
              (P0 !!! Regidx (mword_of_int 9 : mword 5)) vfra0 vfs00
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              (dqc:=DfracOwn 1)
              HN HNl HAlk HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
              Hpmpp Hpteregion Halignp HW HR Hramcov
              Hmyg
              ltac:(rewrite HAlk; exact Hg_lk)
              ltac:(rewrite HAcpu2; exact Hg_cpu)
              ltac:(rewrite HB2tp; exact Hnotmine)
              ltac:(rewrite HB2ra; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile
                    Hlk [Hcpu] [Hp24] [Hp16] [Hp8] [Hfra2] [Hfs02] [-]").
    { iEval (rewrite HAcpu2). iExact "Hcpu". }
    { iEval (rewrite Hspdh_eq). iExact "Hp24". }
    { iEval (rewrite Hspdh_eq). iExact "Hp16". }
    { iEval (rewrite Hspdh_eq). iExact "Hp8". }
    { iEval (rewrite Hspdh_eq). iExact "Hfra2". }
    { iEval (rewrite Hspdh_eq). iExact "Hfs02". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hmh Hcpu Hhj".
    iEval (rewrite HAcpu2) in "Hcpu".
    iDestruct "Hmh" as (mh) "[Hfile %Hmhf]".
    destruct Hmhf as (Hhra & Hhs0 & Hms1 & Hmsp & Hmtp & Hma0).
    iDestruct "Hhj" as (w24 w16 w8 wra ws0) "(Hp24 & Hp16 & Hp8 & Hfra & Hfs0)".
    iEval (rewrite Hspdh_eq) in "Hp24". iEval (rewrite Hspdh_eq) in "Hp16".
    iEval (rewrite Hspdh_eq) in "Hp8". iEval (rewrite Hspdh_eq) in "Hfra".
    iEval (rewrite Hspdh_eq) in "Hfs0".
    assert (Hpc16 : update_vec_dec (add_vec (B2 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AQ + 0x16))
      by (rewrite HB2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- 0x16: c.li a4,1 ---- *)
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ (mword_of_int (AQ + 0x16)) (mword_of_int 14 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 14 : mword 5)
              (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 14), ADDI))
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
              mh mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi16 [-]").
    { intros s_pc Hnpc _ _.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) (mword_of_int 14) (sign_extend' 12 (mword_of_int 1 : mword 6)) s_pc).
      replace (Z.eqb (uint (mword_of_int 14 : mword 5)) 0) with false by (vm_compute; reflexivity).
      unfold gpr_addi_val.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
      reflexivity. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (B5 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mh).
    assert (Hpp18 : add_vec_int (mword_of_int (AQ + 0x16) : mword 64) 2 = mword_of_int (AQ + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* ---- 0x18: c.bnez a0 (NOT taken: a0 = 0) ---- *)
    assert (HB5a0 : B5 !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)).
    { rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hma0. }
    iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (AQ + 0x18)) (mword_of_int 14) (Cregidx (mword_of_int 2)) (mword_of_int 10)
              B5 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite HB5a0; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi18 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp1a : add_vec_int (mword_of_int (AQ + 0x18) : mword 64) 2 = mword_of_int (AQ + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* ---- 0x1a..0x22: the test-and-set loop, THROUGH the lock invariant ---- *)
    assert (HB2s1 : B2 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs1_. }
    assert (HB5a4L : B5 !!! Regidx (mword_of_int 14 : mword 5)
                    = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (rewrite /B5; apply lookup_total_insert).
    assert (HB5s1 : B5 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms1. exact HB2s1. }
    iDestruct "Hfile" as "[%HdomB5 HfmapB5]".
    assert (HB5l : B5 !! Regidx (mword_of_int 15 : mword 5)
                   = Some (B5 !!! Regidx (mword_of_int 15 : mword 5)))
      by (apply lookup_lookup_total_dom; apply HdomB5).
    iApply (wp_acquire_lock_loop root_ppn E Φ γ R B5 (B5 !!! Regidx (mword_of_int 15 : mword 5)) lk svpn_lk
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hpmpp Hpteregion Halignp HR HW
              Hmyg Hramcov Hg_lk Hpma_amo
              HB5a4L HB5s1
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc [HfmapB5] Hlk [-]").
    { rewrite insert_id; [| exact HB5l ].
      iSplitR; [iPureIntro; exact HdomB5 | iExact "HfmapB5"]. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Htok HRes".
    set (B8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> B5).
    (* ---- 0x24: jal ra,mycpu; the whole mycpu() ---- *)
    assert (HB8sp : B8 !!! Regidx csp_rs1 = spd).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hmsp. exact HB2sp. }
    assert (HB9sp : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x24) : mword 64) 4)]> B8) !!! Regidx csp_rs1 = spd)
      by (rewrite lookup_total_insert_ne; [ exact HB8sp | vm_compute; discriminate ]).
    (* the mycpu frame slots coincide with push_off's r24/r16 cells *)
    assert (Hmra : add_vec (add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = a_p24).
    { rewrite /a_p24 /po_spd !po_addv_assoc. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hms0 : add_vec (add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = a_p16).
    { rewrite /a_p16 /po_spd !po_addv_assoc. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_pushoff_call_mycpu root_ppn E Φ (mword_of_int (AQ + 0x24)) (mword_of_int 0xcb8 : mword 21) B8
              w24 w16
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN ltac:(apply bv_eq; vm_compute; reflexivity) Hmyg
              ltac:(vm_compute; reflexivity)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
              Hpmpp Hpteregion Halignp
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              HW HR Hramcov
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile Hi24 [Hp24] [Hp16] [-]").
    { iEval (rewrite HB9sp Hmra). iExact "Hp24". }
    { iEval (rewrite HB9sp Hms0). iExact "Hp16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hp24 Hp16".
    iEval (rewrite HB9sp Hmra) in "Hp24". iEval (rewrite HB9sp Hms0) in "Hp16".
    iEval (rewrite lookup_total_insert) in "Hpc".
    assert (Hpc28 : update_vec_dec (add_vec (add_vec_int (mword_of_int (AQ + 0x24) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (AQ + 0x28) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    set (C1 := po_mycpu_out (mword_of_int (AQ + 0x24)) B8).
    (* ---- 0x28: c.sd a0,16(s1) : lk->cpu := &cpus[cpuid] ---- *)
    assert (HB8s1 : B8 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HB5s1. }
    assert (HC1s1 : C1 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /C1 po_mycpu_out_s1. exact HB8s1. }
    assert (HAcpu : add_vec (C1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = a_cpu).
    { rewrite HC1s1 aq_addv_zero_l. reflexivity. }
    pose proof Hg_cpu as (Ccanon & Cvpn & Cident & Cmask & Cvpn2 & Cmvpn & Cmppn & Crange & Calign & Cpalign).
    iApply (wp_csd_s root_ppn E Φ (mword_of_int (AQ + 0x28)) (mword_of_int 10) (mword_of_int 9)
              (mword_of_int 16) svpn_cpu C1 cpuold mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              ltac:(rewrite HAcpu; exact Ccanon) ltac:(rewrite HAcpu; exact Cvpn) ltac:(rewrite HAcpu; exact Cident)
              Cmask Cvpn2 Cmvpn Cmppn Hpmpp Hpteregion Halignp ltac:(rewrite HAcpu; exact Crange) HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi28 [Hcpu] [-]").
    { iEval (rewrite HAcpu). iExact "Hcpu". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hcpu".
    iEval (rewrite HAcpu) in "Hcpu".
    (* the stored value is mycpu's return &cpus[cpuid] *)
    assert (HB8tp : B8 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hmtp. exact HB2tp. }
    assert (HC1a0 : C1 !!! Regidx (mword_of_int 10 : mword 5) = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))).
    { rewrite /C1 po_mycpu_out_a0 HB8tp. reflexivity. }
    iEval (rewrite HC1a0) in "Hcpu".
    assert (Hpp2a : add_vec_int (mword_of_int (AQ + 0x28) : mword 64) 2 = mword_of_int (AQ + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* ---- 0x2a: c.ldsp ra,24(sp) ---- *)
    assert (HC1sp : C1 !!! Regidx csp_rs1 = spd).
    { rewrite /C1 po_mycpu_out_csp. exact HB8sp. }
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x2a)) (mword_of_int 3) (mword_of_int 1 : mword 5)
              C1 (m !!! Regidx (mword_of_int 1 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HR
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2a [Hr24]").
    { iEval (rewrite HC1sp). iExact "Hr24". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr24".
    iEval (rewrite HC1sp) in "Hr24".
    set (D1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> C1).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = spd)
      by (rewrite /D1; rewrite lookup_total_insert_ne; [ exact HC1sp | vm_compute; discriminate ]).
    assert (Hpp2c : add_vec_int (mword_of_int (AQ + 0x2a) : mword 64) 2 = mword_of_int (AQ + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* ---- 0x2c: c.ldsp s0,16(sp) ---- *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x2c)) (mword_of_int 2) (mword_of_int 8 : mword 5)
              D1 (m !!! Regidx (mword_of_int 8 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HR
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2c [Hr16]").
    { iEval (rewrite HD1sp). iExact "Hr16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr16".
    iEval (rewrite HD1sp) in "Hr16".
    set (D2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> D1).
    assert (HD2sp : D2 !!! Regidx csp_rs1 = spd)
      by (rewrite /D2; rewrite lookup_total_insert_ne; [ exact HD1sp | vm_compute; discriminate ]).
    assert (Hpp2e : add_vec_int (mword_of_int (AQ + 0x2c) : mword 64) 2 = mword_of_int (AQ + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* ---- 0x2e: c.ldsp s1,8(sp) ---- *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x2e)) (mword_of_int 1) (mword_of_int 9 : mword 5)
              D2 (m !!! Regidx (mword_of_int 9 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HR
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2e [Hr8]").
    { iEval (rewrite HD2sp). iExact "Hr8". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr8".
    iEval (rewrite HD2sp) in "Hr8".
    set (D3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> D2).
    assert (HD3sp : D3 !!! Regidx csp_rs1 = spd)
      by (rewrite /D3; rewrite lookup_total_insert_ne; [ exact HD2sp | vm_compute; discriminate ]).
    assert (Hpp30 : add_vec_int (mword_of_int (AQ + 0x2e) : mword 64) 2 = mword_of_int (AQ + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* ---- 0x30: c.addi16sp sp,32 ---- *)
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    iApply (wp_caddi16sp_gpr_s root_ppn E Φ (mword_of_int (AQ + 0x30)) (mword_of_int 2 : mword 6) D3
              pmpcfg0 pmpaddr00 region_pte (1/2)%Qp HN Hmyg Hramcov Hpmpp Hpteregion Halignp
              with "Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi30 [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    set (D4 := <[Regidx csp_rs1 := regval_into_reg (add_vec (D3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> D3).
    assert (Hpp32 : add_vec_int (mword_of_int (AQ + 0x30) : mword 64) 2 = mword_of_int (AQ + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* ---- 0x32: c.ret ---- *)
    assert (HD4ra : D4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /D1. apply lookup_total_insert. }
    iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (AQ + 0x32)) (mword_of_int 1 : mword 5) D4
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
              ltac:(vm_compute; discriminate) Hlpe
              ltac:(rewrite HD4ra; exact Hal0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi32 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite HD4ra) in "Hpc".
    (* ---- hand everything to the caller's continuation ---- *)
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Htok HRes [Hfile] Hr24 Hr16 Hr8 [Hfra Hfs0 Hp24 Hp16 Hp8] Hnoff Hintena Hcpu").
    { iExists D4. iFrame "Hfile". iPureIntro.
      split; [exact HD4ra|]. split; [|split; [|split; [|split]]].
      - rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. apply lookup_total_insert.
      - rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. apply lookup_total_insert.
      - rewrite /D4. rewrite lookup_total_insert. rewrite HD3sp.
        rewrite /spd po_addv_assoc.
        replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))
          with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        apply kv_addv_zero.
      - rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HC1a0.
      - rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /C1 po_mycpu_out_tp. exact HB8tp.
    }
    iExists _, _, _, _, _.
    iFrame "Hp24 Hp16 Hp8 Hfra Hfs0".
  Qed.

End WpAcquireLock.
