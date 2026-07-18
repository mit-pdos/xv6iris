(* UserretEntryPt.v -- the userret PAGE-TABLE SWITCH over the pt2 window
   (TransPt.v): sfence.vma ; csrw satp,a0 ; sfence.vma, as three uniform
   steps of the shared trampoline engine.

     step 1 (kernel invariant): the sfence flushes the TLB; the kernel
       invariant re-seals with [tlb_ok_pt_empty].
     step 2 (kernel invariant): the csrw installs the user root; the
       kernel invariant DISSOLVES into the two-table window invariant
       [tlb_inv_pt2] ([tlb_inv_pt2_enter]) -- the freshly parked user
       table arrives as [pt_frame], every resident TLB entry is
       kernel-provenance.
     step 3 (window invariant): the fetch itself is absorbed by
       [tlb_inv_pt2] (a hit on a stale kernel-provenance trampoline
       entry -- same physical page -- may Svadu-write-back into the
       KERNEL tree through the cached pteAddr; a miss walks the USER
       tree); then the sfence flushes the TLB, the window EXITS
       ([tlb_inv_pt2_exit]): the kernel table parks as [pt_frame] for
       the return trip and the user invariant [utlb_inv_pt] seals.     *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import WpLoad WpLeafCommon WpGpr WpGprCsrwB WpMmodeLeafBase.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree PtTreeAdue KptPt TrampPt TrampTlb.
Require Import SmodeCore SmodeCorePt WpSmodeGpr KptTree UptTree.
Require Import WpSmodePtLeaves PtFetchGen TrampStepPt TransPt.
Require Import WpUserret.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section UserretEntryPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_userret_entry_pt (kroot uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (usatp : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    (* S-mode config *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_TVM mstatus0) ('b"1") = false ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    upt_map_wf um ->
    (* a0 holds the USER satp value *)
    m !! Regidx (mword_of_int 10) = Some usatp ->
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt kroot -∗
    pt_frame (upt_tree_spec uroot tfp um) -∗
    pc_is (uva 0x9c) -∗
    gpr_file m -∗
    instr (upa 0x9c) false ai_sfence -∗
    instr (upa 0xa0) false ai_csrw -∗
    instr (upa 0xa4) false ai_sfence -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      utlb_inv_pt uroot tfp um -∗
      pt_frame (kpt_tree_spec kroot) -∗
      pc_is (uva 0xa8) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HSIE HMPRV HSXL HTVM Hmm HPBMTE Hmenvval0 Hwf Ha0 HuMode Huasid Huppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hktlb Hufr [Hpc Hnpc]
             [%Hdom Hfmap] Hi1 Hi2 Hi3 Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    assert (Hva01 : add_vec_int (uva 0x9c) 4 = uva 0xa0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva02 : add_vec_int (uva 0xa0) 4 = uva 0xa4)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva03 : add_vec_int (uva 0xa4) 4 = uva 0xa8)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ============ STEP 1: sfence.vma under the kernel invariant ======== *)
    iApply (wp_instr_ktramp_pt kroot Φ (uva 0x9c) (upa 0x9c) false ai_sfence
              mstatus0 mie_v mdv0 menvcfg0 dq
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hktlb Hpc Hi1").
    iIntros (σ1 Hpceq1) "Hpriv Hms Hmie Hmdl Hmenv Hktlb Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv1.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms1.
    iMod (reg_update _ nextPC _ (uva 0xa0) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc1 := set_reg σ1 nextPC (uva 0xa0)).
    assert (Lpriv1p : register_lookup cur_privilege s_pc1.(sregs) = Supervisor)
      by (unfold s_pc1; tmig; exact Lpriv1).
    assert (Lms1p : register_lookup mstatus s_pc1.(sregs) = mstatus0)
      by (unfold s_pc1; tmig; exact Lms1).
    destruct (exec_execute_SFENCE_VMA_S s_pc1 Lpriv1p
                ltac:(rewrite Lms1p; exact HTVM)) as (tlbz1 & Hex1 & Hnone1).
    (* flush the invariant's TLB cell and re-seal with the empty vector *)
    iDestruct (tlb_inv_pt_open with "Hktlb") as (ksatp1 tlbvec1 kt1)
      "(Hsatp & %HkMode1 & %Hkasid1 & %Hkppn1 & Htlb & %Hokk1 & %Hspeck1 & %Hpmaw1 & Hkt & Hpmp)".
    iMod (reg_update _ tlb _ tlbz1 with "Hreg Htlb") as "[Hreg Htlb]".
    iDestruct (tlb_inv_pt_intro kroot ksatp1 tlbz1 kt1 HkMode1 Hkasid1 Hkppn1
                 (tlb_ok_pt_empty (mword_of_int 0) kt1 tlbz1
                    (fun vpn' => Hnone1 _ (tlb_hash_range vpn')))
                 Hspeck1 Hpmaw1 with "Hsatp Htlb Hkt Hpmp") as "Hktlb".
    iModIntro.
    iExists (set_reg s_pc1 tlb tlbz1).
    iSplitR.
    { iPureIntro. rewrite Hpceq1. rewrite Hva01. fold s_pc1.
      change ai_sfence with (SFENCE_VMA (zreg, zreg)). exact Hex1. }
    iSplitL "Hreg Hmem".
    { unfold s_pc1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc".
    assert (Lnpc1 : register_lookup nextPC (set_reg s_pc1 tlb tlbz1).(sregs) = uva 0xa0).
    { unfold s_pc1; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc1) in "Hpc".
    iNext.
    (* ============ STEP 2: csrw satp,a0 -- ENTER the window ============= *)
    iApply (wp_instr_ktramp_pt kroot Φ (uva 0xa0) (upa 0xa0) false ai_csrw
              mstatus0 mie_v mdv0 menvcfg0 dq
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hktlb Hpc Hi2").
    iIntros (σ2 Hpceq2) "Hpriv Hms Hmie Hmdl Hmenv Hktlb Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv2.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms2.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa2.
    iMod (reg_update _ nextPC _ (uva 0xa4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc2 := set_reg σ2 nextPC (uva 0xa4)).
    assert (Lpriv2p : register_lookup cur_privilege s_pc2.(sregs) = Supervisor)
      by (unfold s_pc2; tmig; exact Lpriv2).
    assert (Lms2p : register_lookup mstatus s_pc2.(sregs) = mstatus0)
      by (unfold s_pc2; tmig; exact Lms2).
    assert (Lmisa2p : register_lookup misa s_pc2.(sregs) = misa0)
      by (unfold s_pc2; tmig; exact Lmisa2).
    (* a0's value at the executing state *)
    assert (Hmsp : m !! Regidx (mword_of_int 10 : mword 5)
                   = Some (m !!! Regidx (mword_of_int 10 : mword 5)))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value (mword_of_int 10) (m !!! Regidx (mword_of_int 10 : mword 5)) s_pc2
                 with "Hreg Hspc") as %Lva2.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Hma0v : m !!! Regidx (mword_of_int 10 : mword 5) = usatp)
      by (apply lookup_total_correct; exact Ha0).
    replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false in Lva2
      by (vm_compute; reflexivity).
    rewrite Hma0v in Lva2.
    pose proof (exec_execute_csrw_satp_S (mword_of_int 10) s_pc2
                  ltac:(vm_compute; lia) Lpriv2p
                  ltac:(rewrite Lms2p; exact HTVM)
                  ltac:(rewrite Lmisa2p; exact HmisaS)
                  ltac:(rewrite Lms2p; exact HSXL)) as Hex2.
    rewrite Lva2 in Hex2.
    rewrite (satp_legalized_sv39 (register_lookup satp s_pc2.(sregs)) usatp HuMode) in Hex2.
    (* dissolve the kernel invariant into the two-table window *)
    iDestruct (tlb_inv_pt_open with "Hktlb") as (ksatp2 tlbvec2 kt2)
      "(Hsatp & %HkMode2 & %Hkasid2 & %Hkppn2 & Htlb & %Hokk2 & %Hspeck2 & %Hpmaw2 & Hkt & Hpmp)".
    iMod (reg_update _ satp _ usatp with "Hreg Hsatp") as "[Hreg Hsatp]".
    iDestruct (tlb_inv_pt2_enter uroot (kpt_tree_spec kroot) (upt_tree_spec uroot tfp um)
                 usatp tlbvec2 kt2 HuMode Huasid Huppn Hokk2 Hspeck2 Hpmaw2
                 with "Hsatp Htlb Hkt Hufr [Hpmp]") as "Hpt2".
    { iApply (pmp_config_reindex kroot uroot with "Hpmp"). }
    iModIntro.
    iExists (set_reg s_pc2 satp usatp).
    iSplitR.
    { iPureIntro. rewrite Hpceq2. rewrite Hva02. fold s_pc2.
      change ai_csrw with (CSRReg (csr_satp, Regidx (mword_of_int 10 : mword 5), zreg, CSRRW)).
      exact Hex2. }
    iSplitL "Hreg Hmem".
    { unfold s_pc2, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc".
    assert (Lnpc2 : register_lookup nextPC (set_reg s_pc2 satp usatp).(sregs) = uva 0xa4).
    { unfold s_pc2; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc2) in "Hpc".
    iNext.
    (* ============ STEP 3: sfence.vma -- EXIT into the user invariant === *)
    iApply (wp_instr_pt2_tramp uroot (kpt_tree_spec kroot) (upt_tree_spec uroot tfp um)
              (kpt_pt2_tramp_spec kroot) (upt_pt2_tramp_spec uroot tfp um Hwf)
              (upt_pt2_base uroot tfp um)
              Φ (uva 0xa4) (upa 0xa4) false ai_sfence
              mstatus0 mie_v mdv0 menvcfg0 dq
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpt2 Hpc Hi3").
    iIntros (σ3 Hpceq3) "Hpriv Hms Hmie Hmdl Hmenv Hpt2 Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv3.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms3.
    iMod (reg_update _ nextPC _ (uva 0xa8) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc3 := set_reg σ3 nextPC (uva 0xa8)).
    assert (Lpriv3p : register_lookup cur_privilege s_pc3.(sregs) = Supervisor)
      by (unfold s_pc3; tmig; exact Lpriv3).
    assert (Lms3p : register_lookup mstatus s_pc3.(sregs) = mstatus0)
      by (unfold s_pc3; tmig; exact Lms3).
    destruct (exec_execute_SFENCE_VMA_S s_pc3 Lpriv3p
                ltac:(rewrite Lms3p; exact HTVM)) as (tlbz3 & Hex3 & Hnone3).
    (* exit the window: the kernel table parks, the user invariant seals *)
    iDestruct (tlb_inv_pt2_exit with "Hpt2") as (usatp3 tlbvec3 ut3)
      "(Hsatp & %HuMode3 & %Huasid3 & %Huppn3 & Htlb & %Hspecu3 & %Hpmaw3 & Hut & Hpmp & Hkfr)".
    iMod (reg_update _ tlb _ tlbz3 with "Hreg Htlb") as "[Hreg Htlb]".
    iDestruct (utlb_inv_pt_intro uroot tfp um usatp3 tlbz3 ut3
                 HuMode3 Huasid3 Huppn3
                 (tlb_ok_pt_empty (mword_of_int 0) ut3 tlbz3
                    (fun vpn' => Hnone3 _ (tlb_hash_range vpn')))
                 Hspecu3 Hwf Hpmaw3 with "Hsatp Htlb Hut Hpmp") as "Hutlb".
    iModIntro.
    iExists (set_reg s_pc3 tlb tlbz3).
    iSplitR.
    { iPureIntro. rewrite Hpceq3. rewrite Hva03. fold s_pc3.
      change ai_sfence with (SFENCE_VMA (zreg, zreg)). exact Hex3. }
    iSplitL "Hreg Hmem".
    { unfold s_pc3, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc".
    assert (Lnpc3 : register_lookup nextPC (set_reg s_pc3 tlb tlbz3).(sregs) = uva 0xa8).
    { unfold s_pc3; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc3) in "Hpc".
    iNext.
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hkfr
                          [$Hpc $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.

End UserretEntryPt.
