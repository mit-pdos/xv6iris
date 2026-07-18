(* WpSmodePtLock.v -- lock-invariant instruction leaves over [tlb_inv_pt]
   (ports of WpLockLeaves.v).  Same absorption recipe as the data leaves;
   the lock invariant is opened inside the engine callback and re-closed
   before the step commits.  The byte facts are re-derived from the
   gen_heap AFTER the absorption [iMod] (the ADUE write-back only touches
   page-table pages, never the lock word). *)
Require Import WpSmodeLeafBase.
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpLoad WpLeafCommon.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree PtTreeAdue KptPt.
Require Import SmodeCore WpSmodeGpr WpPushOffMem WpAmo WpLock.
Require Import KptTree SmodeCorePt WpSmodePtLeaves WpSmodePtMem.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* Local width-4 helpers (Local in WpSmodeLoad.v, so re-proved here). *)
Local Lemma avi0_mul4 (a : mword 64) : add_vec_int a (0 * 4) = a.
Proof. change (0 * 4) with 0. apply avi0. Qed.

Local Lemma data2_id_4 (v : mword 32) :
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v = v.
Proof.
    apply bv_eq. unfold update_subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
    erewrite bv_concat_unsigned by (cbn; lia).
    erewrite bv_concat_unsigned by (cbn; lia).
    rewrite !bv_unsigned_N_0.
    rewrite Z.shiftl_0_l. rewrite Z.shiftl_0_r. rewrite Z.lor_0_r. rewrite Z.lor_0_l.
    reflexivity.
Qed.

Section ExecAmoGS4walkPt.
  Variable rs2 rs1 rd : mword 5.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable w : mword 32.
  Variable s s' : mstate.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s'.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := a8.
  Let storeval : mword 32 :=
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Atomic (AMOSWAP, Data, Data))) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hamo : pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hhr : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hhw : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte w j).

  Lemma exec_execute_AMOSWAP_4_gpr_S_walk_pt :
    exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg (MState s'.(sregs) (write_bytes s'.(mem) pa 4 storeval) s'.(mdev))
                    (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))).
  Proof.
    change (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)))
      with (execute_AMO AMOSWAP true false (Regidx rs2) (Regidx rs1) 4 (Regidx rd)).
    unfold execute_AMO. cbn zeta.
    rewrite exec_catch_early_return.
    assert (Hae : exec (Defs.assert_exp' (Z.leb 4 (Z.mul xlen_bytes 2)) "extensions/A/zaamo_insts.sail:73.32-73.33") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae).
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (AMOSWAP, Data, Data)) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 (zeros' 64) (Atomic (AMOSWAP, Data, Data)) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_amo_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite Halign. cbn [Riscv.rv64d.not negb]. cbv iota.
    rewrite (execR_liftR_seq _ _ _ _ _ Htr).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s')).
    cbn beta match.
    replace (Z.leb 4 xlen_bytes) with true by (vm_compute; reflexivity).
    cbv iota.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_rX_bits_gpr rs2 s')).
    cbn beta. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_amo_4 pa s' Hpalign)).
    cbn match.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_mem_read_amo_4_S PBMT_PMA pa region w (register_lookup mstatus s'.(sregs)) s'
                 HA Hord Hrange HR HW Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhr Hdev
                 (fun j Hj => Hbytes j Hj) eq_refl Hmprv' Hcp')).
    cbn match. rewrite execR_returnR. cbn match.
    cbn zeta. cbn match.
    replace (generic_eq AMOSWAP AMOCAS) with false by (vm_compute; reflexivity).
    unfold and_boolM.
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match. cbv iota.
    rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_mem_write_value_amo_4_S PBMT_PMA pa region _ (register_lookup mstatus s'.(sregs)) s'
                 HA Hord Hrange HR HW Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhw Hdev eq_refl Hmprv' Hcp')).
    cbn match.
    match goal with |- context[execR _ ?st] =>
      set (s_m := st)
    end.
    assert (HwX : execR (Defs.liftR (wX_bits (Regidx rd)
                     (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))
                   : Defs.monadR ExecutionResult exception unit) s_m
                  = Some (inr tt,
                          set_reg s_m (R_bitvector_64 (gpr_of_Z (uint rd)))
                            (regval_into_reg (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8)))))).
    { rewrite execR_liftR.
      rewrite (exec_wX_bits_gpr rd _ s_m).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      reflexivity. }
    rewrite (execR_bind0_Some _ _ _ _ HwX).
    rewrite execR_returnR.
    cbn.
    reflexivity.
  Qed.
End ExecAmoGS4walkPt.

(* AMO variants of KptPt's check lemmas (A/D-variant leaf passes the
   check for amoswap.w at Supervisor). *)
Local Lemma kpt_check_amo_ad (adf : kpt_adf) (vpn : mword 27) :
  forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (Atomic (AMOSWAP, Data, Data)) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn)))
          (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof.
  intros mxr do_sum s'.
  unfold kpt_lflags_ad, PTE_RAM_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    destruct (adf vpn) as [a d]; destruct a, d, mxr, do_sum; vm_compute; reflexivity.
Qed.

Local Lemma kpt_variant_check_amo (vpn : mword 27) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (Atomic (AMOSWAP, Data, Data)) Supervisor mxr do_sum
    (pte_set_ad (kpt_leaf_pte vpn) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite kpt_variant_flags. rewrite kpt_variant_ext.
  apply kpt_check_amo_ad.
Qed.

Section WpSmodePtLock.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_clw_lockinv_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γ : gname) (lk : mword 64) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    pa = lk ->
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    is_lock γ lk R -∗
    ( ∀ v : mword 32,
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ea a8 pa Hpalk Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr #Hlock Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    iApply (wp_instr_s_config_tlbinv_pt root_ppn Φ pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlock") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (v) "[>Hbytes Hbr]".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampa3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampa3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iMod (tlb_inv_pt_translateAddr_load root_ppn a8 s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
              s_tr.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf_tr.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    pose proof (within_clint_false pa 4 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 4 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 4 s_tr Lhtif_tr) as Hwh.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v) = sign_extend' 64 v).
    { unfold extend_value. rewrite data2_id_4. reflexivity. }
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
        by (cbn [bits_of_virtaddr]; reflexivity).
      replace pa with a8 by (unfold pa; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sign_extend' 64 v)))).
    { rewrite <- Hev.
      apply (exec_execute_LOAD_4_gpr_S_walk_pt rs1 rd imm v region_ld satp1 s_pc s_tr Hrd
               Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
               ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
               ltac:(rewrite Lmenv_pc; exact Hpmm)
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_tr; exact HR)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_ld0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
               Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hbytesf_tr)). }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64 v)) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iMod ("Hclose" with "[Hbytes Hbr]") as "_".
    { iNext. iExists v. iSplitL "Hbytes".
      { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
      iExact "Hbr". }
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
             = add_vec_int pc 2).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" $! v with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  Lemma wp_clw_lockinv_locked_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γ : gname) (lk : mword 64) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    pa = lk ->
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    is_lock γ lk R -∗
    locked γ -∗
    ( ∀ v : mword 32,
      ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝ -∗
      locked γ -∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ea a8 pa Hpalk Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr #Hlock Htok Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    iApply (wp_instr_s_config_tlbinv_pt root_ppn Φ pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlock") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (v) "[>Hbytes Hbr]".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    iDestruct "Hbr" as "[(_ & >Htok2 & _) | >%Hvnz]".
    { iExFalso. iApply (locked_exclusive with "Htok Htok2"). }
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampa3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampa3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iMod (tlb_inv_pt_translateAddr_load root_ppn a8 s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
              s_tr.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf_tr.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    pose proof (within_clint_false pa 4 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 4 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 4 s_tr Lhtif_tr) as Hwh.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v) = sign_extend' 64 v).
    { unfold extend_value. rewrite data2_id_4. reflexivity. }
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
        by (cbn [bits_of_virtaddr]; reflexivity).
      replace pa with a8 by (unfold pa; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sign_extend' 64 v)))).
    { rewrite <- Hev.
      apply (exec_execute_LOAD_4_gpr_S_walk_pt rs1 rd imm v region_ld satp1 s_pc s_tr Hrd
               Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
               ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
               ltac:(rewrite Lmenv_pc; exact Hpmm)
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_tr; exact HR)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_ld0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
               Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hbytesf_tr)). }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64 v)) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iMod ("Hclose" with "[Hbytes]") as "_".
    { iNext. iExists v. iSplitL "Hbytes".
      { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
      iRight. iPureIntro. exact Hvnz. }
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
             = add_vec_int pc 2).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" $! v with "[//] Htok Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  Lemma wp_sd_zero_s_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := (zero_reg : mword 64) in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct (word_pointsto_aligned_p with "Hbytes") as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iApply (wp_instr_s_config_tlbinv_pt root_ppn Φ pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (word_pointsto_bytes with "Hbytes") as "Hb".
      iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampa7.
    { iDestruct (word_pointsto_bytes with "Hbytes") as "Hb".
      iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hb") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iMod (tlb_inv_pt_translateAddr_store root_ppn a8 s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    pose proof (within_clint_false pa 8 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 8 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
        by (cbn [bits_of_virtaddr]; reflexivity).
      replace pa with a8 by (unfold pa; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) pa 8 storeval)
                              s_tr.(mdev))).
    { pose proof (exec_execute_STORE_8_gpr_S_walk_pt (mword_of_int 0 : mword 5) rs1 imm region_st satp1 s_pc s_tr
               Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
               ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
               ltac:(rewrite Lmenv_pc; exact Hpmm)
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_tr; exact HW)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
               Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id in H0.
      rewrite H0. do 3 f_equal;
      first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
    iMod (word_pointsto_write s_tr.(mem) pa vold storeval with "Hmem Hbytes")
      as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 8 storeval) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 8 storeval) s_tr.(mdev)).(sregs)
             = add_vec_int pc 4).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbytes").
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.

  Lemma wp_sw_zero_lockinv_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γ : gname) (lk : mword 64) (R : iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    pa = lk ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    is_lock γ lk R -∗
    locked γ -∗
    R -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ea a8 pa Hpalk HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    set (storeval := (mword_of_int 0 : mword 32)).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr #Hlock Htok HRes Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iApply (wp_instr_s_config_tlbinv_pt root_ppn Φ pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlock") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (w) "[>Hbytes _]".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampa3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampa3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iMod (tlb_inv_pt_translateAddr_store root_ppn a8 s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    pose proof (within_clint_false pa 4 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 4 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 4 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
        by (cbn [bits_of_virtaddr]; reflexivity).
      replace pa with a8 by (unfold pa; reflexivity).
      exact Htr0. }
    pose (s_x := MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 4 storeval) s_tr.(mdev)).
    assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))) s_pc
                     = Some (RETIRE_SUCCESS, s_x)).
    { pose proof (exec_execute_STORE_4_gpr_S_walk_pt (mword_of_int 0 : mword 5) rs1 imm region_st satp1 s_pc s_tr
               Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
               ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
               ltac:(rewrite Lmenv_pc; exact Hpmm)
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_tr; exact HW)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
               Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id in H0.
      rewrite H0. subst s_x. do 3 f_equal;
      first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
    iMod (upd_window_4 s_tr.(mem) pa storeval w with "Hmem Hbytes") as "[Hmem Hbytes]".
    iMod ("Hclose" with "[Hbytes Htok HRes]") as "_".
    { iNext. iExists storeval. iSplitL "Hbytes".
      { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
      iLeft. iFrame "Htok HRes". iPureIntro. reflexivity. }
    iModIntro.
    iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { unfold s_x; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
    { unfold s_x; cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_amoswap_lockinv_pt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γ : gname) (lk : mword 64) (R : iProp Σ)
      (pc : mword 64) (rd rs2 rs1 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (zeros' 64) in
    let a8 := ea in
    let pa := a8 in
    pa = lk ->
    neq_vec (sign_extend' 64 (amoswap_stored (m !!! Regidx rs2))) zero_reg = true ->
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)) -∗
    is_lock γ lk R -∗
    ( ∀ w : mword 32,
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (amoswap_loaded w)]> m) -∗
      (⌜w = (mword_of_int 0 : mword 32)⌝ ∗ locked γ ∗ R
       ∨ ⌜neq_vec (sign_extend' 64 w) zero_reg = true⌝) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ea a8 pa Hpalk Hstz Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr #Hlock Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_amo & Hmatch_amo & _ & Hread_amo & Hwrite_amo & Hatomic_supp_amo).
    assert (Hatomic_amo : pma_allows_atomic_op
              ((override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_atomic_support))
              AMOSWAP 4 = true)
      by (rewrite Hatomic_supp_amo; vm_compute; reflexivity).
    iApply (wp_instr_s_config_tlbinv_pt root_ppn Φ pc false (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlock") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (w) "[>Hbytes Hbr]".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampa3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampa3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    assert (Hea_pc : add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                             (zeros' 64) = pa)
      by (rewrite Lva; reflexivity).
    assert (Ha8_pc : sign_extend' 64 (subrange_vec_dec
                       (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                 else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                                (zeros' 64)) (xlen - 0 - 1) 0) = pa)
      by (rewrite Hea_pc subrange_id sign_extend'_id; reflexivity).
    iMod (tlb_inv_pt_translateAddr (Atomic (AMOSWAP, Data, Data))
            root_ppn a8 s_pc
            (fun a d mxr do_sum => kpt_variant_check_amo (svpn_of a8) a d mxr do_sum)
            (or_introl (ram_svpn_range a8 Hrampa))
            (RiscvExtras.ram_canonical a8 Hrampa)
            (ram_ident_4k a8 Hrampa)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_amo_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_amo s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_tr with "Hreg Hr2c") as %Lv2_tr.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
              s_tr.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbytesf_tr.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    pose proof (within_clint_false pa 4 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 4 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 4 s_tr Lhtif_tr) as Hwhr.
    pose proof (within_htif_writable_false pa 4 s_tr Lhtif_tr) as Hwhw.
    assert (Htr_pc : exec (translateAddr (Virtaddr pa) (Atomic (AMOSWAP, Data, Data))) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { exact Htr0. }
    pose (s_x := set_reg (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 4 (amoswap_stored (m !!! Regidx rs2))) s_tr.(mdev))
                   (R_bitvector_64 (gpr_of_Z (uint rd)))
                   (regval_into_reg (amoswap_loaded w))).
    assert (Hexec : exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s_pc
                    = Some (RETIRE_SUCCESS, s_x)).
    { rewrite (exec_execute_AMOSWAP_4_gpr_S_walk_pt rs2 rs1 rd region_amo satp1 w s_pc s_tr Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Ha8_pc; exact Halign4)
                 ltac:(rewrite Ha8_pc; exact Htr_pc)
                 Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
                 ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
                 ltac:(rewrite Lpmpaddr_tr Ha8_pc; exact Hrange_ld) ltac:(rewrite Lpmpc_tr; exact HR)
                 ltac:(rewrite Lpmpc_tr; exact HW)
                 ltac:(rewrite Lpma_tr Ha8_pc; exact Hmatch_amo)
                 ltac:(rewrite Ha8_pc; exact Hpalign4)
                 Hread_amo Hwrite_amo Hatomic_amo
                 ltac:(rewrite Ha8_pc; apply Hwc) ltac:(rewrite Ha8_pc; apply Hws)
                 ltac:(rewrite Ha8_pc; apply Hwhr) ltac:(rewrite Ha8_pc; apply Hwhw)
                 ltac:(rewrite Ha8_pc; exact (addr_is_ram_not_dev _ Hrampa))
                 ltac:(rewrite Ha8_pc; exact Hbytesf_tr)).
      subst s_x. unfold amoswap_stored, amoswap_loaded.
      rewrite Ha8_pc. rewrite Lv2_tr. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (amoswap_loaded w))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (amoswap_loaded w)) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iMod (upd_window_4 s_tr.(mem) pa (amoswap_stored (m !!! Regidx rs2)) w with "Hmem Hbytes") as "[Hmem Hbytes]".
    iMod ("Hclose" with "[Hbytes]") as "_".
    { iNext. iExists (amoswap_stored (m !!! Regidx rs2)). iSplitL "Hbytes".
      { rewrite /lock_word -Hpalk. iApply (word4_pointsto_intro _ _ _ Hpalign4). iExact "Hbytes". }
      iRight. iPureIntro. exact Hstz. }
    iModIntro.
    iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hexec. }
    iSplitL "Hreg Hmem Hdev".
    { unfold s_x, set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
    { unfold s_x, set_reg; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply ("Hcont" $! w with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbr").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpSmodePtLock.
